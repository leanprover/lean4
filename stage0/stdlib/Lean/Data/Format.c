// Lean compiler output
// Module: Lean.Data.Format
// Imports: public import Lean.Data.Options public import Init.Data.Format.Instances
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
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Std_Format_defIndent;
extern uint8_t l_Std_Format_defUnicode;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Std_Format_getWidth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l_Lean_Std_Format_getWidth___closed__0 = (const lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value;
static const lean_string_object l_Lean_Std_Format_getWidth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "width"};
static const lean_object* l_Lean_Std_Format_getWidth___closed__1 = (const lean_object*)&l_Lean_Std_Format_getWidth___closed__1_value;
static const lean_ctor_object l_Lean_Std_Format_getWidth___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Lean_Std_Format_getWidth___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Std_Format_getWidth___closed__2_value_aux_0),((lean_object*)&l_Lean_Std_Format_getWidth___closed__1_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 45, 141, 245, 85, 231, 30)}};
static const lean_object* l_Lean_Std_Format_getWidth___closed__2 = (const lean_object*)&l_Lean_Std_Format_getWidth___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Std_Format_getWidth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_getWidth___boxed(lean_object*);
static const lean_string_object l_Lean_Std_Format_getIndent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "indent"};
static const lean_object* l_Lean_Std_Format_getIndent___closed__0 = (const lean_object*)&l_Lean_Std_Format_getIndent___closed__0_value;
static const lean_ctor_object l_Lean_Std_Format_getIndent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Lean_Std_Format_getIndent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Std_Format_getIndent___closed__1_value_aux_0),((lean_object*)&l_Lean_Std_Format_getIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 177, 135, 35, 69, 72, 208, 204)}};
static const lean_object* l_Lean_Std_Format_getIndent___closed__1 = (const lean_object*)&l_Lean_Std_Format_getIndent___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Std_Format_getIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_getIndent___boxed(lean_object*);
static const lean_string_object l_Lean_Std_Format_getUnicode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unicode"};
static const lean_object* l_Lean_Std_Format_getUnicode___closed__0 = (const lean_object*)&l_Lean_Std_Format_getUnicode___closed__0_value;
static const lean_ctor_object l_Lean_Std_Format_getUnicode___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Lean_Std_Format_getUnicode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Std_Format_getUnicode___closed__1_value_aux_0),((lean_object*)&l_Lean_Std_Format_getUnicode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 238, 228, 128, 13, 57, 105, 12)}};
static const lean_object* l_Lean_Std_Format_getUnicode___closed__1 = (const lean_object*)&l_Lean_Std_Format_getUnicode___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Std_Format_getUnicode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_getUnicode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "indentation"};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static lean_once_cell_t l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
static const lean_string_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(17, 91, 241, 9, 207, 1, 69, 94)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 19, 27, 189, 190, 96, 237, 102)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 101, 185, 92, 60, 135, 175, 32)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Std_Format_getWidth___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 53, 142, 251, 216, 118, 196, 222)}};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_format_width;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unicode characters"};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
static lean_once_cell_t l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_;
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(17, 91, 241, 9, 207, 1, 69, 94)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 19, 27, 189, 190, 96, 237, 102)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 101, 185, 92, 60, 135, 175, 32)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Std_Format_getUnicode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 68, 8, 44, 58, 34, 134, 77)}};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_format_unicode;
static lean_once_cell_t l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_;
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(17, 91, 241, 9, 207, 1, 69, 94)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 19, 27, 189, 190, 96, 237, 102)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 101, 185, 92, 60, 135, 175, 32)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Std_Format_getIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 47, 80, 176, 57, 237, 202, 74)}};
static const lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_format_indent;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToFormatName__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToFormatName__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToFormatName__lean___closed__0 = (const lean_object*)&l_Lean_instToFormatName__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToFormatName__lean = (const lean_object*)&l_Lean_instToFormatName__lean___closed__0_value;
static const lean_string_object l_Lean_instToFormatDataValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__0 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToFormatDataValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__1 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToFormatDataValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__2 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_instToFormatDataValue___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__2_value)}};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__3 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__3_value;
static const lean_string_object l_Lean_instToFormatDataValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__4 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instToFormatDataValue___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__4_value)}};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__5 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToFormatDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToFormatDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToFormatDataValue___closed__0 = (const lean_object*)&l_Lean_instToFormatDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToFormatDataValue = (const lean_object*)&l_Lean_instToFormatDataValue___closed__0_value;
static const lean_string_object l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instToFormatProdNameDataValue___lam__0___closed__0 = (const lean_object*)&l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToFormatProdNameDataValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instToFormatProdNameDataValue___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instToFormatProdNameDataValue___lam__0___closed__1 = (const lean_object*)&l_Lean_instToFormatProdNameDataValue___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToFormatProdNameDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToFormatProdNameDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToFormatProdNameDataValue___closed__0 = (const lean_object*)&l_Lean_instToFormatProdNameDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToFormatProdNameDataValue = (const lean_object*)&l_Lean_instToFormatProdNameDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_formatKVMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_formatKVMap___closed__0 = (const lean_object*)&l_Lean_formatKVMap___closed__0_value;
static const lean_ctor_object l_Lean_formatKVMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_formatKVMap___closed__0_value)}};
static const lean_object* l_Lean_formatKVMap___closed__1 = (const lean_object*)&l_Lean_formatKVMap___closed__1_value;
static const lean_string_object l_Lean_formatKVMap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_formatKVMap___closed__2 = (const lean_object*)&l_Lean_formatKVMap___closed__2_value;
static const lean_string_object l_Lean_formatKVMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_formatKVMap___closed__3 = (const lean_object*)&l_Lean_formatKVMap___closed__3_value;
static lean_once_cell_t l_Lean_formatKVMap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_formatKVMap___closed__4;
static lean_once_cell_t l_Lean_formatKVMap___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_formatKVMap___closed__5;
static const lean_ctor_object l_Lean_formatKVMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_formatKVMap___closed__2_value)}};
static const lean_object* l_Lean_formatKVMap___closed__6 = (const lean_object*)&l_Lean_formatKVMap___closed__6_value;
static const lean_ctor_object l_Lean_formatKVMap___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_formatKVMap___closed__3_value)}};
static const lean_object* l_Lean_formatKVMap___closed__7 = (const lean_object*)&l_Lean_formatKVMap___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object*);
static const lean_closure_object l_Lean_instToFormatKVMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_formatKVMap, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToFormatKVMap___closed__0 = (const lean_object*)&l_Lean_instToFormatKVMap___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToFormatKVMap = (const lean_object*)&l_Lean_instToFormatKVMap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Std_Format_getWidth(lean_object* v_o_6_){
_start:
{
lean_object* v_map_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_map_7_ = lean_ctor_get(v_o_6_, 0);
v___x_8_ = ((lean_object*)(l_Lean_Std_Format_getWidth___closed__2));
v___x_9_ = l_Std_Format_defWidth;
v___x_10_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_7_, v___x_8_);
if (lean_obj_tag(v___x_10_) == 0)
{
return v___x_9_;
}
else
{
lean_object* v_val_11_; 
v_val_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_val_11_);
lean_dec_ref_known(v___x_10_, 1);
if (lean_obj_tag(v_val_11_) == 3)
{
lean_object* v_v_12_; 
v_v_12_ = lean_ctor_get(v_val_11_, 0);
lean_inc(v_v_12_);
lean_dec_ref_known(v_val_11_, 1);
return v_v_12_;
}
else
{
lean_dec(v_val_11_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_getWidth___boxed(lean_object* v_o_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Std_Format_getWidth(v_o_13_);
lean_dec_ref(v_o_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_getIndent(lean_object* v_o_19_){
_start:
{
lean_object* v_map_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_map_20_ = lean_ctor_get(v_o_19_, 0);
v___x_21_ = ((lean_object*)(l_Lean_Std_Format_getIndent___closed__1));
v___x_22_ = l_Std_Format_defIndent;
v___x_23_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_20_, v___x_21_);
if (lean_obj_tag(v___x_23_) == 0)
{
return v___x_22_;
}
else
{
lean_object* v_val_24_; 
v_val_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_val_24_);
lean_dec_ref_known(v___x_23_, 1);
if (lean_obj_tag(v_val_24_) == 3)
{
lean_object* v_v_25_; 
v_v_25_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_v_25_);
lean_dec_ref_known(v_val_24_, 1);
return v_v_25_;
}
else
{
lean_dec(v_val_24_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_getIndent___boxed(lean_object* v_o_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Std_Format_getIndent(v_o_26_);
lean_dec_ref(v_o_26_);
return v_res_27_;
}
}
uint8_t l_Lean_Std_Format_getUnicode(lean_object* v_o_32_){
_start:
{
lean_object* v_map_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; 
v_map_33_ = lean_ctor_get(v_o_32_, 0);
v___x_34_ = ((lean_object*)(l_Lean_Std_Format_getUnicode___closed__1));
v___x_35_ = l_Std_Format_defUnicode;
v___x_36_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_33_, v___x_34_);
if (lean_obj_tag(v___x_36_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v___x_36_, 1);
if (lean_obj_tag(v_val_37_) == 1)
{
uint8_t v_v_38_; 
v_v_38_ = lean_ctor_get_uint8(v_val_37_, 0);
lean_dec_ref_known(v_val_37_, 0);
return v_v_38_;
}
else
{
lean_dec(v_val_37_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT void l_Lean_Std_Format_getUnicode_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_32_ = stack[0].m_obj;
uint8_t v_res_39_;
v_res_39_ = l_Lean_Std_Format_getUnicode(v_o_32_);
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_getUnicode___boxed(lean_object* v_o_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_Std_Format_getUnicode(v_o_40_);
lean_dec_ref(v_o_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object* v_name_43_, lean_object* v_decl_44_, lean_object* v_ref_45_){
_start:
{
lean_object* v_defValue_47_; lean_object* v_descr_48_; lean_object* v_deprecation_x3f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_defValue_47_ = lean_ctor_get(v_decl_44_, 0);
v_descr_48_ = lean_ctor_get(v_decl_44_, 1);
v_deprecation_x3f_49_ = lean_ctor_get(v_decl_44_, 2);
lean_inc(v_defValue_47_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v_defValue_47_);
lean_inc(v_deprecation_x3f_49_);
lean_inc_ref(v_descr_48_);
lean_inc_n(v_name_43_, 2);
v___x_51_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_51_, 0, v_name_43_);
lean_ctor_set(v___x_51_, 1, v_ref_45_);
lean_ctor_set(v___x_51_, 2, v___x_50_);
lean_ctor_set(v___x_51_, 3, v_descr_48_);
lean_ctor_set(v___x_51_, 4, v_deprecation_x3f_49_);
v___x_52_ = lean_register_option(v_name_43_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_61_);
v___x_54_ = v___x_52_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_dec(v___x_52_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_inc(v_defValue_47_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_name_43_);
lean_ctor_set(v___x_56_, 1, v_defValue_47_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v_name_43_);
v_a_62_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_52_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_52_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_43_ = stack[0].m_obj;
lean_object* v_decl_44_ = stack[1].m_obj;
lean_object* v_ref_45_ = stack[2].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_43_, v_decl_44_, v_ref_45_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_71_, lean_object* v_decl_72_, lean_object* v_ref_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_71_, v_decl_72_, v_ref_73_);
lean_dec_ref(v_decl_72_);
return v_res_75_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = lean_box(0);
v___x_78_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_79_ = l_Std_Format_defWidth;
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_77_);
return v___x_80_;
}
}
lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = ((lean_object*)(l_Lean_Std_Format_getWidth___closed__2));
v___x_92_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_);
v___x_93_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_94_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_91_, v___x_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_95_;
v_res_95_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
return v_res_97_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object* v_name_98_, lean_object* v_decl_99_, lean_object* v_ref_100_){
_start:
{
lean_object* v_defValue_102_; lean_object* v_descr_103_; lean_object* v_deprecation_x3f_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_defValue_102_ = lean_ctor_get(v_decl_99_, 0);
v_descr_103_ = lean_ctor_get(v_decl_99_, 1);
v_deprecation_x3f_104_ = lean_ctor_get(v_decl_99_, 2);
v___x_105_ = lean_alloc_ctor(1, 0, 1);
v___x_106_ = lean_unbox(v_defValue_102_);
lean_ctor_set_uint8(v___x_105_, 0, v___x_106_);
lean_inc(v_deprecation_x3f_104_);
lean_inc_ref(v_descr_103_);
lean_inc_n(v_name_98_, 2);
v___x_107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_107_, 0, v_name_98_);
lean_ctor_set(v___x_107_, 1, v_ref_100_);
lean_ctor_set(v___x_107_, 2, v___x_105_);
lean_ctor_set(v___x_107_, 3, v_descr_103_);
lean_ctor_set(v___x_107_, 4, v_deprecation_x3f_104_);
v___x_108_ = lean_register_option(v_name_98_, v___x_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v___x_108_, 0);
lean_dec(v_unused_117_);
v___x_110_ = v___x_108_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_dec(v___x_108_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
lean_inc(v_defValue_102_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v_name_98_);
lean_ctor_set(v___x_112_, 1, v_defValue_102_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v_name_98_);
v_a_118_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_108_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_98_ = stack[0].m_obj;
lean_object* v_decl_99_ = stack[1].m_obj;
lean_object* v_ref_100_ = stack[2].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_98_, v_decl_99_, v_ref_100_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_127_, lean_object* v_decl_128_, lean_object* v_ref_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_127_, v_decl_128_, v_ref_129_);
lean_dec_ref(v_decl_128_);
return v_res_131_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = lean_box(0);
v___x_134_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_135_ = l_Std_Format_defUnicode;
v___x_136_ = lean_box(v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_134_);
lean_ctor_set(v___x_137_, 2, v___x_133_);
return v___x_137_;
}
}
lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = ((lean_object*)(l_Lean_Std_Format_getUnicode___closed__1));
v___x_146_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_);
v___x_147_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_148_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v___x_145_, v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_149_;
v_res_149_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
return v_res_151_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_box(0);
v___x_153_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_154_ = l_Std_Format_defIndent;
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_152_);
return v___x_155_;
}
}
lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = ((lean_object*)(l_Lean_Std_Format_getIndent___closed__1));
v___x_164_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_);
v___x_165_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_));
v___x_166_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_163_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_inc(v_defValue_173_);
return v_defValue_173_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_175_, 1);
if (lean_obj_tag(v_val_176_) == 3)
{
lean_object* v_v_177_; 
v_v_177_ = lean_ctor_get(v_val_176_, 0);
lean_inc(v_v_177_);
lean_dec_ref_known(v_val_176_, 1);
return v_v_177_;
}
else
{
lean_dec(v_val_176_);
lean_inc(v_defValue_173_);
return v_defValue_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0___boxed(lean_object* v_opts_178_, lean_object* v_opt_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(v_opts_178_, v_opt_179_);
lean_dec_ref(v_opt_179_);
lean_dec_ref(v_opts_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27(lean_object* v_f_181_, lean_object* v_o_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = l_Lean_Std_Format_format_width;
v___x_184_ = l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(v_o_182_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Std_Format_pretty(v_f_181_, v___x_184_, v___x_185_, v___x_185_);
lean_dec(v___x_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27___boxed(lean_object* v_f_187_, lean_object* v_o_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Std_Format_pretty_x27(v_f_187_, v_o_188_);
lean_dec_ref(v_o_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object* v_n_190_){
_start:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = 1;
v___x_192_ = l_Lean_Name_toString(v_n_190_, v___x_191_);
v___x_193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__0(lean_object* v_x_205_){
_start:
{
switch(lean_obj_tag(v_x_205_))
{
case 0:
{
lean_object* v_v_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_214_; 
v_v_206_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_208_ = v_x_205_;
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_v_206_);
lean_dec(v_x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = l_String_quote(v_v_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 3);
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
case 1:
{
uint8_t v_v_215_; 
v_v_215_ = lean_ctor_get_uint8(v_x_205_, 0);
lean_dec_ref_known(v_x_205_, 0);
if (v_v_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
return v___x_217_;
}
}
case 2:
{
lean_object* v_v_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_229_; 
v_v_218_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_229_ == 0)
{
v___x_220_ = v_x_205_;
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_v_218_);
lean_dec(v_x_205_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_222_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_223_ = 1;
v___x_224_ = l_Lean_Name_toString(v_v_218_, v___x_223_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 3);
lean_ctor_set(v___x_220_, 0, v___x_224_);
v___x_226_ = v___x_220_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_222_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
return v___x_227_;
}
}
}
case 3:
{
lean_object* v_v_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_238_; 
v_v_230_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_238_ == 0)
{
v___x_232_ = v_x_205_;
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_v_230_);
lean_dec(v_x_205_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Nat_reprFast(v_v_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
case 4:
{
lean_object* v_v_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_v_239_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_x_205_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_v_239_);
lean_dec(v_x_205_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = l_Int_repr(v_v_239_);
lean_dec(v_v_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
default: 
{
lean_object* v_v_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; 
v_v_248_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_v_248_);
lean_dec_ref_known(v_x_205_, 1);
v___x_249_ = lean_box(0);
v___x_250_ = 0;
v___x_251_ = l_Lean_Syntax_formatStx(v_v_248_, v___x_249_, v___x_250_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object* v_x_257_){
_start:
{
lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_322_; 
v_fst_258_ = lean_ctor_get(v_x_257_, 0);
v_snd_259_ = lean_ctor_get(v_x_257_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_322_ == 0)
{
v___x_261_ = v_x_257_;
v_isShared_262_ = v_isSharedCheck_322_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snd_259_);
lean_inc(v_fst_258_);
lean_dec(v_x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_322_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_263_ = 1;
v___x_264_ = l_Lean_Name_toString(v_fst_258_, v___x_263_);
v___x_265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 5);
lean_ctor_set(v___x_261_, 1, v___x_266_);
lean_ctor_set(v___x_261_, 0, v___x_265_);
v___x_268_ = v___x_261_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_321_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
switch(lean_obj_tag(v_snd_259_))
{
case 0:
{
lean_object* v_v_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v_v_269_ = lean_ctor_get(v_snd_259_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_snd_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v_snd_259_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_v_269_);
lean_dec(v_snd_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_String_quote(v_v_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 3);
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_268_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
}
}
case 1:
{
uint8_t v_v_279_; 
v_v_279_ = lean_ctor_get_uint8(v_snd_259_, 0);
lean_dec_ref_known(v_snd_259_, 0);
if (v_v_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_268_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_268_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
}
case 2:
{
lean_object* v_v_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_295_; 
v_v_284_ = lean_ctor_get(v_snd_259_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_snd_259_);
if (v_isSharedCheck_295_ == 0)
{
v___x_286_ = v_snd_259_;
v_isShared_287_ = v_isSharedCheck_295_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_v_284_);
lean_dec(v_snd_259_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_295_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_289_ = l_Lean_Name_toString(v_v_284_, v___x_263_);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 3);
lean_ctor_set(v___x_286_, 0, v___x_289_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_294_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_288_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_268_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
}
}
case 3:
{
lean_object* v_v_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
v_v_296_ = lean_ctor_get(v_snd_259_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_snd_259_);
if (v_isSharedCheck_305_ == 0)
{
v___x_298_ = v_snd_259_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_v_296_);
lean_dec(v_snd_259_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Nat_reprFast(v_v_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_268_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
}
case 4:
{
lean_object* v_v_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_315_; 
v_v_306_ = lean_ctor_get(v_snd_259_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_snd_259_);
if (v_isSharedCheck_315_ == 0)
{
v___x_308_ = v_snd_259_;
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_v_306_);
lean_dec(v_snd_259_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Int_repr(v_v_306_);
lean_dec(v_v_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 3);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_314_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_268_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
}
default: 
{
lean_object* v_v_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_v_316_ = lean_ctor_get(v_snd_259_, 0);
lean_inc(v_v_316_);
lean_dec_ref_known(v_snd_259_, 1);
v___x_317_ = lean_box(0);
v___x_318_ = 0;
v___x_319_ = l_Lean_Syntax_formatStx(v_v_316_, v___x_317_, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_268_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_nat_to_int(v_a_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_dec(v_x_327_);
return v_x_328_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_417_; 
v_head_330_ = lean_ctor_get(v_x_329_, 0);
v_tail_331_ = lean_ctor_get(v_x_329_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_417_ == 0)
{
v___x_333_ = v_x_329_;
v_isShared_334_ = v_isSharedCheck_417_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_tail_331_);
lean_inc(v_head_330_);
lean_dec(v_x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_417_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_416_; 
v_fst_335_ = lean_ctor_get(v_head_330_, 0);
v_snd_336_ = lean_ctor_get(v_head_330_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_head_330_);
if (v_isSharedCheck_416_ == 0)
{
v___x_338_ = v_head_330_;
v_isShared_339_ = v_isSharedCheck_416_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_inc(v_fst_335_);
lean_dec(v_head_330_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_416_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
lean_inc(v_x_327_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 5);
lean_ctor_set(v___x_338_, 1, v_x_327_);
lean_ctor_set(v___x_338_, 0, v_x_328_);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_x_328_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_x_327_);
v___x_341_ = v_reuseFailAlloc_415_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_342_ = 1;
v___x_343_ = l_Lean_Name_toString(v_fst_335_, v___x_342_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 5);
lean_ctor_set(v___x_333_, 1, v___x_345_);
lean_ctor_set(v___x_333_, 0, v___x_344_);
v___x_347_ = v___x_333_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_414_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
switch(lean_obj_tag(v_snd_336_))
{
case 0:
{
lean_object* v_v_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_359_; 
v_v_348_ = lean_ctor_get(v_snd_336_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_snd_336_);
if (v_isSharedCheck_359_ == 0)
{
v___x_350_ = v_snd_336_;
v_isShared_351_ = v_isSharedCheck_359_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_v_348_);
lean_dec(v_snd_336_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_359_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = l_String_quote(v_v_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 3);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_347_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_341_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v_x_328_ = v___x_356_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
case 1:
{
uint8_t v_v_360_; 
v_v_360_ = lean_ctor_get_uint8(v_snd_336_, 0);
lean_dec_ref_known(v_snd_336_, 0);
if (v_v_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_347_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_341_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v_x_328_ = v___x_363_;
v_x_329_ = v_tail_331_;
goto _start;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_347_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_341_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v_x_328_ = v___x_367_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
case 2:
{
lean_object* v_v_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_382_; 
v_v_369_ = lean_ctor_get(v_snd_336_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_snd_336_);
if (v_isSharedCheck_382_ == 0)
{
v___x_371_ = v_snd_336_;
v_isShared_372_ = v_isSharedCheck_382_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_v_369_);
lean_dec(v_snd_336_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_382_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_374_ = l_Lean_Name_toString(v_v_369_, v___x_342_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 3);
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_373_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_347_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_341_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v_x_328_ = v___x_379_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
case 3:
{
lean_object* v_v_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_394_; 
v_v_383_ = lean_ctor_get(v_snd_336_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_snd_336_);
if (v_isSharedCheck_394_ == 0)
{
v___x_385_ = v_snd_336_;
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_v_383_);
lean_dec(v_snd_336_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = l_Nat_reprFast(v_v_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_393_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_347_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_341_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v_x_328_ = v___x_391_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
case 4:
{
lean_object* v_v_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_406_; 
v_v_395_ = lean_ctor_get(v_snd_336_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_snd_336_);
if (v_isSharedCheck_406_ == 0)
{
v___x_397_ = v_snd_336_;
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_v_395_);
lean_dec(v_snd_336_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = l_Int_repr(v_v_395_);
lean_dec(v_v_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 3);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_347_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_341_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_x_328_ = v___x_403_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
default: 
{
lean_object* v_v_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_v_407_ = lean_ctor_get(v_snd_336_, 0);
lean_inc(v_v_407_);
lean_dec_ref_known(v_snd_336_, 1);
v___x_408_ = lean_box(0);
v___x_409_ = 0;
v___x_410_ = l_Lean_Syntax_formatStx(v_v_407_, v___x_408_, v___x_409_);
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_347_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_341_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v_x_328_ = v___x_412_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v___x_420_; 
lean_dec(v_x_419_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v_tail_421_; 
v_tail_421_ = lean_ctor_get(v_x_418_, 1);
if (lean_obj_tag(v_tail_421_) == 0)
{
lean_object* v_head_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_x_419_);
v_head_422_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_x_418_, 1);
lean_dec(v_unused_506_);
v___x_424_ = v_x_418_;
v_isShared_425_ = v_isSharedCheck_505_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_head_422_);
lean_dec(v_x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_505_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_504_; 
v_fst_426_ = lean_ctor_get(v_head_422_, 0);
v_snd_427_ = lean_ctor_get(v_head_422_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_head_422_);
if (v_isSharedCheck_504_ == 0)
{
v___x_429_ = v_head_422_;
v_isShared_430_ = v_isSharedCheck_504_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_head_422_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_504_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_431_ = 1;
v___x_432_ = l_Lean_Name_toString(v_fst_426_, v___x_431_);
v___x_433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
v___x_434_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 5);
lean_ctor_set(v___x_429_, 1, v___x_434_);
lean_ctor_set(v___x_429_, 0, v___x_433_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_503_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
switch(lean_obj_tag(v_snd_427_))
{
case 0:
{
lean_object* v_v_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
v_v_437_ = lean_ctor_get(v_snd_427_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_snd_427_);
if (v_isSharedCheck_448_ == 0)
{
v___x_439_ = v_snd_427_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_v_437_);
lean_dec(v_snd_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_String_quote(v_v_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 3);
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_443_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_445_ = v___x_424_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
case 1:
{
uint8_t v_v_449_; 
v_v_449_ = lean_ctor_get_uint8(v_snd_427_, 0);
lean_dec_ref_known(v_snd_427_, 0);
if (v_v_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_450_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_452_ = v___x_424_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_454_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_456_ = v___x_424_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
case 2:
{
lean_object* v_v_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_471_; 
v_v_458_ = lean_ctor_get(v_snd_427_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_snd_427_);
if (v_isSharedCheck_471_ == 0)
{
v___x_460_ = v_snd_427_;
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_v_458_);
lean_dec(v_snd_427_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_463_ = l_Lean_Name_toString(v_v_458_, v___x_431_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 3);
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_470_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_465_);
lean_ctor_set(v___x_424_, 0, v___x_462_);
v___x_467_ = v___x_424_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_436_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
return v___x_468_;
}
}
}
}
case 3:
{
lean_object* v_v_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_483_; 
v_v_472_ = lean_ctor_get(v_snd_427_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_snd_427_);
if (v_isSharedCheck_483_ == 0)
{
v___x_474_ = v_snd_427_;
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_v_472_);
lean_dec(v_snd_427_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = l_Nat_reprFast(v_v_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_478_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_480_ = v___x_424_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
case 4:
{
lean_object* v_v_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_v_484_ = lean_ctor_get(v_snd_427_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_snd_427_);
if (v_isSharedCheck_495_ == 0)
{
v___x_486_ = v_snd_427_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_v_484_);
lean_dec(v_snd_427_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = l_Int_repr(v_v_484_);
lean_dec(v_v_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 3);
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_490_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_492_ = v___x_424_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
default: 
{
lean_object* v_v_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v_v_496_ = lean_ctor_get(v_snd_427_, 0);
lean_inc(v_v_496_);
lean_dec_ref_known(v_snd_427_, 1);
v___x_497_ = lean_box(0);
v___x_498_ = 0;
v___x_499_ = l_Lean_Syntax_formatStx(v_v_496_, v___x_497_, v___x_498_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v___x_499_);
lean_ctor_set(v___x_424_, 0, v___x_436_);
v___x_501_ = v___x_424_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
}
else
{
lean_object* v_head_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_597_; 
lean_inc(v_tail_421_);
v_head_507_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_x_418_, 1);
lean_dec(v_unused_598_);
v___x_509_ = v_x_418_;
v_isShared_510_ = v_isSharedCheck_597_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_head_507_);
lean_dec(v_x_418_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_597_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_596_; 
v_fst_511_ = lean_ctor_get(v_head_507_, 0);
v_snd_512_ = lean_ctor_get(v_head_507_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_head_507_);
if (v_isSharedCheck_596_ == 0)
{
v___x_514_ = v_head_507_;
v_isShared_515_ = v_isSharedCheck_596_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v_head_507_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_596_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_516_ = 1;
v___x_517_ = l_Lean_Name_toString(v_fst_511_, v___x_516_);
v___x_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 5);
lean_ctor_set(v___x_514_, 1, v___x_519_);
lean_ctor_set(v___x_514_, 0, v___x_518_);
v___x_521_ = v___x_514_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_595_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
switch(lean_obj_tag(v_snd_512_))
{
case 0:
{
lean_object* v_v_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_v_522_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_534_ == 0)
{
v___x_524_ = v_snd_512_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_v_522_);
lean_dec(v_snd_512_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_String_quote(v_v_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 3);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_528_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_530_ = v___x_509_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_532_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_530_, v_tail_421_);
return v___x_531_;
}
}
}
}
case 1:
{
uint8_t v_v_535_; 
v_v_535_ = lean_ctor_get_uint8(v_snd_512_, 0);
lean_dec_ref_known(v_snd_512_, 0);
if (v_v_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_536_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_538_ = v___x_509_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_538_, v_tail_421_);
return v___x_539_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_541_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_543_ = v___x_509_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_543_, v_tail_421_);
return v___x_544_;
}
}
}
case 2:
{
lean_object* v_v_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_560_; 
v_v_546_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_560_ == 0)
{
v___x_548_ = v_snd_512_;
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_v_546_);
lean_dec(v_snd_512_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_551_ = l_Lean_Name_toString(v_v_546_, v___x_516_);
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 3);
lean_ctor_set(v___x_548_, 0, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_559_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_553_);
lean_ctor_set(v___x_509_, 0, v___x_550_);
v___x_555_ = v___x_509_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_521_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_556_, v_tail_421_);
return v___x_557_;
}
}
}
}
case 3:
{
lean_object* v_v_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_573_; 
v_v_561_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_573_ == 0)
{
v___x_563_ = v_snd_512_;
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_v_561_);
lean_dec(v_snd_512_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Nat_reprFast(v_v_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_572_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_567_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_569_ = v___x_509_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_569_, v_tail_421_);
return v___x_570_;
}
}
}
}
case 4:
{
lean_object* v_v_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_586_; 
v_v_574_ = lean_ctor_get(v_snd_512_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_586_ == 0)
{
v___x_576_ = v_snd_512_;
v_isShared_577_ = v_isSharedCheck_586_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_v_574_);
lean_dec(v_snd_512_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_586_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = l_Int_repr(v_v_574_);
lean_dec(v_v_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 3);
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_580_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_582_ = v___x_509_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_584_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
v___x_583_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_582_, v_tail_421_);
return v___x_583_;
}
}
}
}
default: 
{
lean_object* v_v_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v_v_587_ = lean_ctor_get(v_snd_512_, 0);
lean_inc(v_v_587_);
lean_dec_ref_known(v_snd_512_, 1);
v___x_588_ = lean_box(0);
v___x_589_ = 0;
v___x_590_ = l_Lean_Syntax_formatStx(v_v_587_, v___x_588_, v___x_589_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 5);
lean_ctor_set(v___x_509_, 1, v___x_590_);
lean_ctor_set(v___x_509_, 0, v___x_521_);
v___x_592_ = v___x_509_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_419_, v___x_592_, v_tail_421_);
return v___x_593_;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__4(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_formatKVMap___closed__2));
v___x_605_ = lean_string_length(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__5(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_formatKVMap___closed__4, &l_Lean_formatKVMap___closed__4_once, _init_l_Lean_formatKVMap___closed__4);
v___x_607_ = lean_nat_to_int(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* v_m_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; 
v___x_613_ = ((lean_object*)(l_Lean_formatKVMap___closed__1));
v___x_614_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_612_, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_formatKVMap___closed__5, &l_Lean_formatKVMap___closed__5_once, _init_l_Lean_formatKVMap___closed__5);
v___x_616_ = ((lean_object*)(l_Lean_formatKVMap___closed__6));
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_614_);
v___x_618_ = ((lean_object*)(l_Lean_formatKVMap___closed__7));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_615_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = 0;
v___x_622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_621_);
return v___x_622_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Std_Format_format_width = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Std_Format_format_width);
lean_dec_ref(res);
res = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Std_Format_format_unicode = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Std_Format_format_unicode);
lean_dec_ref(res);
res = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Std_Format_format_indent = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Std_Format_format_indent);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Format(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Format(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Format(builtin);
}
#ifdef __cplusplus
}
#endif
