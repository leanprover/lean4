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
LEAN_EXPORT uint8_t l_Lean_Std_Format_getUnicode(lean_object* v_o_32_){
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
LEAN_EXPORT lean_object* l_Lean_Std_Format_getUnicode___boxed(lean_object* v_o_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lean_Std_Format_getUnicode(v_o_39_);
lean_dec_ref(v_o_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object* v_name_42_, lean_object* v_decl_43_, lean_object* v_ref_44_){
_start:
{
lean_object* v_defValue_46_; lean_object* v_descr_47_; lean_object* v_deprecation_x3f_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_defValue_46_ = lean_ctor_get(v_decl_43_, 0);
v_descr_47_ = lean_ctor_get(v_decl_43_, 1);
v_deprecation_x3f_48_ = lean_ctor_get(v_decl_43_, 2);
lean_inc(v_defValue_46_);
v___x_49_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_49_, 0, v_defValue_46_);
lean_inc(v_deprecation_x3f_48_);
lean_inc_ref(v_descr_47_);
lean_inc_n(v_name_42_, 2);
v___x_50_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_50_, 0, v_name_42_);
lean_ctor_set(v___x_50_, 1, v_ref_44_);
lean_ctor_set(v___x_50_, 2, v___x_49_);
lean_ctor_set(v___x_50_, 3, v_descr_47_);
lean_ctor_set(v___x_50_, 4, v_deprecation_x3f_48_);
v___x_51_ = lean_register_option(v_name_42_, v___x_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_59_; 
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_60_);
v___x_53_ = v___x_51_;
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
else
{
lean_dec(v___x_51_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
lean_inc(v_defValue_46_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_name_42_);
lean_ctor_set(v___x_55_, 1, v_defValue_46_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec(v_name_42_);
v_a_61_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_51_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_51_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_69_, lean_object* v_decl_70_, lean_object* v_ref_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_69_, v_decl_70_, v_ref_71_);
lean_dec_ref(v_decl_70_);
return v_res_73_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_77_ = l_Std_Format_defWidth;
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = ((lean_object*)(l_Lean_Std_Format_getWidth___closed__2));
v___x_90_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_);
v___x_91_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__5_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_92_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_89_, v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object* v_name_95_, lean_object* v_decl_96_, lean_object* v_ref_97_){
_start:
{
lean_object* v_defValue_99_; lean_object* v_descr_100_; lean_object* v_deprecation_x3f_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_defValue_99_ = lean_ctor_get(v_decl_96_, 0);
v_descr_100_ = lean_ctor_get(v_decl_96_, 1);
v_deprecation_x3f_101_ = lean_ctor_get(v_decl_96_, 2);
v___x_102_ = lean_alloc_ctor(1, 0, 1);
v___x_103_ = lean_unbox(v_defValue_99_);
lean_ctor_set_uint8(v___x_102_, 0, v___x_103_);
lean_inc(v_deprecation_x3f_101_);
lean_inc_ref(v_descr_100_);
lean_inc_n(v_name_95_, 2);
v___x_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_104_, 0, v_name_95_);
lean_ctor_set(v___x_104_, 1, v_ref_97_);
lean_ctor_set(v___x_104_, 2, v___x_102_);
lean_ctor_set(v___x_104_, 3, v_descr_100_);
lean_ctor_set(v___x_104_, 4, v_deprecation_x3f_101_);
v___x_105_ = lean_register_option(v_name_95_, v___x_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_105_, 0);
lean_dec(v_unused_114_);
v___x_107_ = v___x_105_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_dec(v___x_105_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_defValue_99_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_name_95_);
lean_ctor_set(v___x_109_, 1, v_defValue_99_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_name_95_);
v_a_115_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_105_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_105_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_123_, lean_object* v_decl_124_, lean_object* v_ref_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_123_, v_decl_124_, v_ref_125_);
lean_dec_ref(v_decl_124_);
return v_res_127_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = lean_box(0);
v___x_130_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_131_ = l_Std_Format_defUnicode;
v___x_132_ = lean_box(v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_130_);
lean_ctor_set(v___x_133_, 2, v___x_129_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = ((lean_object*)(l_Lean_Std_Format_getUnicode___closed__1));
v___x_142_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_);
v___x_143_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_144_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
return v_res_146_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_149_ = l_Std_Format_defIndent;
v___x_150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = ((lean_object*)(l_Lean_Std_Format_getIndent___closed__1));
v___x_159_ = lean_obj_once(&l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_);
v___x_160_ = ((lean_object*)(l___private_Lean_Data_Format_0__Lean_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_));
v___x_161_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_158_, v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Data_Format_0__Lean_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(lean_object* v_opts_164_, lean_object* v_opt_165_){
_start:
{
lean_object* v_name_166_; lean_object* v_defValue_167_; lean_object* v_map_168_; lean_object* v___x_169_; 
v_name_166_ = lean_ctor_get(v_opt_165_, 0);
v_defValue_167_ = lean_ctor_get(v_opt_165_, 1);
v_map_168_ = lean_ctor_get(v_opts_164_, 0);
v___x_169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_168_, v_name_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_inc(v_defValue_167_);
return v_defValue_167_;
}
else
{
lean_object* v_val_170_; 
v_val_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v___x_169_, 1);
if (lean_obj_tag(v_val_170_) == 3)
{
lean_object* v_v_171_; 
v_v_171_ = lean_ctor_get(v_val_170_, 0);
lean_inc(v_v_171_);
lean_dec_ref_known(v_val_170_, 1);
return v_v_171_;
}
else
{
lean_dec(v_val_170_);
lean_inc(v_defValue_167_);
return v_defValue_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0___boxed(lean_object* v_opts_172_, lean_object* v_opt_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(v_opts_172_, v_opt_173_);
lean_dec_ref(v_opt_173_);
lean_dec_ref(v_opts_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27(lean_object* v_f_175_, lean_object* v_o_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = l_Lean_Std_Format_format_width;
v___x_178_ = l_Lean_Option_get___at___00Lean_Std_Format_pretty_x27_spec__0(v_o_176_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Std_Format_pretty(v_f_175_, v___x_178_, v___x_179_, v___x_179_);
lean_dec(v___x_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Std_Format_pretty_x27___boxed(lean_object* v_f_181_, lean_object* v_o_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Std_Format_pretty_x27(v_f_181_, v_o_182_);
lean_dec_ref(v_o_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object* v_n_184_){
_start:
{
uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = 1;
v___x_186_ = l_Lean_Name_toString(v_n_184_, v___x_185_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__0(lean_object* v_x_199_){
_start:
{
switch(lean_obj_tag(v_x_199_))
{
case 0:
{
lean_object* v_v_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_v_200_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_x_199_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_v_200_);
lean_dec(v_x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = l_String_quote(v_v_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 3);
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
case 1:
{
uint8_t v_v_209_; 
v_v_209_ = lean_ctor_get_uint8(v_x_199_, 0);
lean_dec_ref_known(v_x_199_, 0);
if (v_v_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
return v___x_211_;
}
}
case 2:
{
lean_object* v_v_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_223_; 
v_v_212_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_223_ == 0)
{
v___x_214_ = v_x_199_;
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_v_212_);
lean_dec(v_x_199_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_216_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_217_ = 1;
v___x_218_ = l_Lean_Name_toString(v_v_212_, v___x_217_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 3);
lean_ctor_set(v___x_214_, 0, v___x_218_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_222_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_216_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
}
case 3:
{
lean_object* v_v_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_v_224_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v_x_199_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_v_224_);
lean_dec(v_x_199_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = l_Nat_reprFast(v_v_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
case 4:
{
lean_object* v_v_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_v_233_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v_x_199_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_v_233_);
lean_dec(v_x_199_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = l_Int_repr(v_v_233_);
lean_dec(v_v_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 3);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
default: 
{
lean_object* v_v_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; 
v_v_242_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_v_242_);
lean_dec_ref_known(v_x_199_, 1);
v___x_243_ = lean_box(0);
v___x_244_ = 0;
v___x_245_ = l_Lean_Syntax_formatStx(v_v_242_, v___x_243_, v___x_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object* v_x_251_){
_start:
{
lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_316_; 
v_fst_252_ = lean_ctor_get(v_x_251_, 0);
v_snd_253_ = lean_ctor_get(v_x_251_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_251_);
if (v_isSharedCheck_316_ == 0)
{
v___x_255_ = v_x_251_;
v_isShared_256_ = v_isSharedCheck_316_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_snd_253_);
lean_inc(v_fst_252_);
lean_dec(v_x_251_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_316_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_257_ = 1;
v___x_258_ = l_Lean_Name_toString(v_fst_252_, v___x_257_);
v___x_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
v___x_260_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 5);
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_315_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
switch(lean_obj_tag(v_snd_253_))
{
case 0:
{
lean_object* v_v_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_272_; 
v_v_263_ = lean_ctor_get(v_snd_253_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_snd_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_265_ = v_snd_253_;
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_v_263_);
lean_dec(v_snd_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_272_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = l_String_quote(v_v_263_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 3);
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_262_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
}
}
case 1:
{
uint8_t v_v_273_; 
v_v_273_ = lean_ctor_get_uint8(v_snd_253_, 0);
lean_dec_ref_known(v_snd_253_, 0);
if (v_v_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_262_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_262_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
}
case 2:
{
lean_object* v_v_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_289_; 
v_v_278_ = lean_ctor_get(v_snd_253_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_snd_253_);
if (v_isSharedCheck_289_ == 0)
{
v___x_280_ = v_snd_253_;
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_v_278_);
lean_dec(v_snd_253_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_283_ = l_Lean_Name_toString(v_v_278_, v___x_257_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 3);
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_288_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_282_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_262_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
}
}
case 3:
{
lean_object* v_v_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_299_; 
v_v_290_ = lean_ctor_get(v_snd_253_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_snd_253_);
if (v_isSharedCheck_299_ == 0)
{
v___x_292_ = v_snd_253_;
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_v_290_);
lean_dec(v_snd_253_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = l_Nat_reprFast(v_v_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_262_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
}
}
case 4:
{
lean_object* v_v_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_309_; 
v_v_300_ = lean_ctor_get(v_snd_253_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_snd_253_);
if (v_isSharedCheck_309_ == 0)
{
v___x_302_ = v_snd_253_;
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_v_300_);
lean_dec(v_snd_253_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = l_Int_repr(v_v_300_);
lean_dec(v_v_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 3);
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_308_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_262_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
}
}
default: 
{
lean_object* v_v_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_v_310_ = lean_ctor_get(v_snd_253_, 0);
lean_inc(v_v_310_);
lean_dec_ref_known(v_snd_253_, 1);
v___x_311_ = lean_box(0);
v___x_312_ = 0;
v___x_313_ = l_Lean_Syntax_formatStx(v_v_310_, v___x_311_, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_262_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_nat_to_int(v_a_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_dec(v_x_321_);
return v_x_322_;
}
else
{
lean_object* v_head_324_; lean_object* v_tail_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_411_; 
v_head_324_ = lean_ctor_get(v_x_323_, 0);
v_tail_325_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_411_ == 0)
{
v___x_327_ = v_x_323_;
v_isShared_328_ = v_isSharedCheck_411_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_tail_325_);
lean_inc(v_head_324_);
lean_dec(v_x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_411_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_410_; 
v_fst_329_ = lean_ctor_get(v_head_324_, 0);
v_snd_330_ = lean_ctor_get(v_head_324_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_head_324_);
if (v_isSharedCheck_410_ == 0)
{
v___x_332_ = v_head_324_;
v_isShared_333_ = v_isSharedCheck_410_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_snd_330_);
lean_inc(v_fst_329_);
lean_dec(v_head_324_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_410_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
lean_inc(v_x_321_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 5);
lean_ctor_set(v___x_332_, 1, v_x_321_);
lean_ctor_set(v___x_332_, 0, v_x_322_);
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_x_322_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_x_321_);
v___x_335_ = v_reuseFailAlloc_409_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_336_ = 1;
v___x_337_ = l_Lean_Name_toString(v_fst_329_, v___x_336_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 5);
lean_ctor_set(v___x_327_, 1, v___x_339_);
lean_ctor_set(v___x_327_, 0, v___x_338_);
v___x_341_ = v___x_327_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_408_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
switch(lean_obj_tag(v_snd_330_))
{
case 0:
{
lean_object* v_v_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_353_; 
v_v_342_ = lean_ctor_get(v_snd_330_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_snd_330_);
if (v_isSharedCheck_353_ == 0)
{
v___x_344_ = v_snd_330_;
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_v_342_);
lean_dec(v_snd_330_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = l_String_quote(v_v_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 3);
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_348_ = v___x_344_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_341_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_335_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v_x_322_ = v___x_350_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
}
case 1:
{
uint8_t v_v_354_; 
v_v_354_ = lean_ctor_get_uint8(v_snd_330_, 0);
lean_dec_ref_known(v_snd_330_, 0);
if (v_v_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_341_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_335_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v_x_322_ = v___x_357_;
v_x_323_ = v_tail_325_;
goto _start;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_341_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_335_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v_x_322_ = v___x_361_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
case 2:
{
lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_376_; 
v_v_363_ = lean_ctor_get(v_snd_330_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_snd_330_);
if (v_isSharedCheck_376_ == 0)
{
v___x_365_ = v_snd_330_;
v_isShared_366_ = v_isSharedCheck_376_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_v_363_);
lean_dec(v_snd_330_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_376_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_368_ = l_Lean_Name_toString(v_v_363_, v___x_336_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 3);
lean_ctor_set(v___x_365_, 0, v___x_368_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_375_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_367_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_341_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_335_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v_x_322_ = v___x_373_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
}
case 3:
{
lean_object* v_v_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_388_; 
v_v_377_ = lean_ctor_get(v_snd_330_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_snd_330_);
if (v_isSharedCheck_388_ == 0)
{
v___x_379_ = v_snd_330_;
v_isShared_380_ = v_isSharedCheck_388_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_v_377_);
lean_dec(v_snd_330_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_388_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = l_Nat_reprFast(v_v_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_341_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_335_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v_x_322_ = v___x_385_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
}
case 4:
{
lean_object* v_v_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_400_; 
v_v_389_ = lean_ctor_get(v_snd_330_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_snd_330_);
if (v_isSharedCheck_400_ == 0)
{
v___x_391_ = v_snd_330_;
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_v_389_);
lean_dec(v_snd_330_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = l_Int_repr(v_v_389_);
lean_dec(v_v_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 3);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_341_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_335_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v_x_322_ = v___x_397_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
}
default: 
{
lean_object* v_v_401_; lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_v_401_ = lean_ctor_get(v_snd_330_, 0);
lean_inc(v_v_401_);
lean_dec_ref_known(v_snd_330_, 1);
v___x_402_ = lean_box(0);
v___x_403_ = 0;
v___x_404_ = l_Lean_Syntax_formatStx(v_v_401_, v___x_402_, v___x_403_);
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_341_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_335_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v_x_322_ = v___x_406_;
v_x_323_ = v_tail_325_;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v___x_414_; 
lean_dec(v_x_413_);
v___x_414_ = lean_box(0);
return v___x_414_;
}
else
{
lean_object* v_tail_415_; 
v_tail_415_ = lean_ctor_get(v_x_412_, 1);
if (lean_obj_tag(v_tail_415_) == 0)
{
lean_object* v_head_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_x_413_);
v_head_416_ = lean_ctor_get(v_x_412_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v_x_412_, 1);
lean_dec(v_unused_500_);
v___x_418_ = v_x_412_;
v_isShared_419_ = v_isSharedCheck_499_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_head_416_);
lean_dec(v_x_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_499_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_498_; 
v_fst_420_ = lean_ctor_get(v_head_416_, 0);
v_snd_421_ = lean_ctor_get(v_head_416_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_head_416_);
if (v_isSharedCheck_498_ == 0)
{
v___x_423_ = v_head_416_;
v_isShared_424_ = v_isSharedCheck_498_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_inc(v_fst_420_);
lean_dec(v_head_416_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_498_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_425_ = 1;
v___x_426_ = l_Lean_Name_toString(v_fst_420_, v___x_425_);
v___x_427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 5);
lean_ctor_set(v___x_423_, 1, v___x_428_);
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_430_ = v___x_423_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_497_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
switch(lean_obj_tag(v_snd_421_))
{
case 0:
{
lean_object* v_v_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_442_; 
v_v_431_ = lean_ctor_get(v_snd_421_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_snd_421_);
if (v_isSharedCheck_442_ == 0)
{
v___x_433_ = v_snd_421_;
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_v_431_);
lean_dec(v_snd_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_String_quote(v_v_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 3);
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_437_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_439_ = v___x_418_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
case 1:
{
uint8_t v_v_443_; 
v_v_443_ = lean_ctor_get_uint8(v_snd_421_, 0);
lean_dec_ref_known(v_snd_421_, 0);
if (v_v_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_444_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_446_ = v___x_418_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_448_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_450_ = v___x_418_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
case 2:
{
lean_object* v_v_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_465_; 
v_v_452_ = lean_ctor_get(v_snd_421_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_snd_421_);
if (v_isSharedCheck_465_ == 0)
{
v___x_454_ = v_snd_421_;
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_v_452_);
lean_dec(v_snd_421_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_456_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_457_ = l_Lean_Name_toString(v_v_452_, v___x_425_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 3);
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_464_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_459_);
lean_ctor_set(v___x_418_, 0, v___x_456_);
v___x_461_ = v___x_418_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_430_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
return v___x_462_;
}
}
}
}
case 3:
{
lean_object* v_v_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_477_; 
v_v_466_ = lean_ctor_get(v_snd_421_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_snd_421_);
if (v_isSharedCheck_477_ == 0)
{
v___x_468_ = v_snd_421_;
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_v_466_);
lean_dec(v_snd_421_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = l_Nat_reprFast(v_v_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_472_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_474_ = v___x_418_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
case 4:
{
lean_object* v_v_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_v_478_ = lean_ctor_get(v_snd_421_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_snd_421_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v_snd_421_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_v_478_);
lean_dec(v_snd_421_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = l_Int_repr(v_v_478_);
lean_dec(v_v_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 3);
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_484_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_486_ = v___x_418_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
default: 
{
lean_object* v_v_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v_v_490_ = lean_ctor_get(v_snd_421_, 0);
lean_inc(v_v_490_);
lean_dec_ref_known(v_snd_421_, 1);
v___x_491_ = lean_box(0);
v___x_492_ = 0;
v___x_493_ = l_Lean_Syntax_formatStx(v_v_490_, v___x_491_, v___x_492_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_493_);
lean_ctor_set(v___x_418_, 0, v___x_430_);
v___x_495_ = v___x_418_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
}
else
{
lean_object* v_head_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_591_; 
lean_inc(v_tail_415_);
v_head_501_ = lean_ctor_get(v_x_412_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_x_412_, 1);
lean_dec(v_unused_592_);
v___x_503_ = v_x_412_;
v_isShared_504_ = v_isSharedCheck_591_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_head_501_);
lean_dec(v_x_412_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_591_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_590_; 
v_fst_505_ = lean_ctor_get(v_head_501_, 0);
v_snd_506_ = lean_ctor_get(v_head_501_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_head_501_);
if (v_isSharedCheck_590_ == 0)
{
v___x_508_ = v_head_501_;
v_isShared_509_ = v_isSharedCheck_590_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v_head_501_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_590_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_510_ = 1;
v___x_511_ = l_Lean_Name_toString(v_fst_505_, v___x_510_);
v___x_512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
v___x_513_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 5);
lean_ctor_set(v___x_508_, 1, v___x_513_);
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_515_ = v___x_508_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_589_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
switch(lean_obj_tag(v_snd_506_))
{
case 0:
{
lean_object* v_v_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_528_; 
v_v_516_ = lean_ctor_get(v_snd_506_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_snd_506_);
if (v_isSharedCheck_528_ == 0)
{
v___x_518_ = v_snd_506_;
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_v_516_);
lean_dec(v_snd_506_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_String_quote(v_v_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 3);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_522_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_524_ = v___x_503_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_524_, v_tail_415_);
return v___x_525_;
}
}
}
}
case 1:
{
uint8_t v_v_529_; 
v_v_529_ = lean_ctor_get_uint8(v_snd_506_, 0);
lean_dec_ref_known(v_snd_506_, 0);
if (v_v_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_530_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_532_ = v___x_503_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_532_, v_tail_415_);
return v___x_533_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_535_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_537_ = v___x_503_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_537_, v_tail_415_);
return v___x_538_;
}
}
}
case 2:
{
lean_object* v_v_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_554_; 
v_v_540_ = lean_ctor_get(v_snd_506_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_snd_506_);
if (v_isSharedCheck_554_ == 0)
{
v___x_542_ = v_snd_506_;
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_v_540_);
lean_dec(v_snd_506_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_544_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_545_ = l_Lean_Name_toString(v_v_540_, v___x_510_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 3);
lean_ctor_set(v___x_542_, 0, v___x_545_);
v___x_547_ = v___x_542_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_553_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_547_);
lean_ctor_set(v___x_503_, 0, v___x_544_);
v___x_549_ = v___x_503_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_515_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_550_, v_tail_415_);
return v___x_551_;
}
}
}
}
case 3:
{
lean_object* v_v_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_v_555_ = lean_ctor_get(v_snd_506_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_snd_506_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v_snd_506_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_v_555_);
lean_dec(v_snd_506_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = l_Nat_reprFast(v_v_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_566_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_561_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_563_ = v___x_503_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_561_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_563_, v_tail_415_);
return v___x_564_;
}
}
}
}
case 4:
{
lean_object* v_v_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
v_v_568_ = lean_ctor_get(v_snd_506_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_snd_506_);
if (v_isSharedCheck_580_ == 0)
{
v___x_570_ = v_snd_506_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_v_568_);
lean_dec(v_snd_506_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = l_Int_repr(v_v_568_);
lean_dec(v_v_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 3);
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_579_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_574_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_576_ = v___x_503_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_576_, v_tail_415_);
return v___x_577_;
}
}
}
}
default: 
{
lean_object* v_v_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_v_581_ = lean_ctor_get(v_snd_506_, 0);
lean_inc(v_v_581_);
lean_dec_ref_known(v_snd_506_, 1);
v___x_582_ = lean_box(0);
v___x_583_ = 0;
v___x_584_ = l_Lean_Syntax_formatStx(v_v_581_, v___x_582_, v___x_583_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v___x_584_);
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_586_ = v___x_503_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_413_, v___x_586_, v_tail_415_);
return v___x_587_;
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
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_formatKVMap___closed__2));
v___x_599_ = lean_string_length(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__5(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_obj_once(&l_Lean_formatKVMap___closed__4, &l_Lean_formatKVMap___closed__4_once, _init_l_Lean_formatKVMap___closed__4);
v___x_601_ = lean_nat_to_int(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* v_m_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; 
v___x_607_ = ((lean_object*)(l_Lean_formatKVMap___closed__1));
v___x_608_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_606_, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_formatKVMap___closed__5, &l_Lean_formatKVMap___closed__5_once, _init_l_Lean_formatKVMap___closed__5);
v___x_610_ = ((lean_object*)(l_Lean_formatKVMap___closed__6));
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_608_);
v___x_612_ = ((lean_object*)(l_Lean_formatKVMap___closed__7));
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_609_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = 0;
v___x_616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*1, v___x_615_);
return v___x_616_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Instances(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
