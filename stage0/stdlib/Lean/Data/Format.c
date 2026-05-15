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
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern uint8_t l_Std_Format_defUnicode;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defIndent;
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static const lean_string_object l_Std_Format_getWidth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l_Std_Format_getWidth___closed__0 = (const lean_object*)&l_Std_Format_getWidth___closed__0_value;
static const lean_string_object l_Std_Format_getWidth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "width"};
static const lean_object* l_Std_Format_getWidth___closed__1 = (const lean_object*)&l_Std_Format_getWidth___closed__1_value;
static const lean_ctor_object l_Std_Format_getWidth___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Std_Format_getWidth___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_getWidth___closed__2_value_aux_0),((lean_object*)&l_Std_Format_getWidth___closed__1_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 45, 141, 245, 85, 231, 30)}};
static const lean_object* l_Std_Format_getWidth___closed__2 = (const lean_object*)&l_Std_Format_getWidth___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Format_getWidth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getWidth___boxed(lean_object*);
static const lean_string_object l_Std_Format_getIndent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "indent"};
static const lean_object* l_Std_Format_getIndent___closed__0 = (const lean_object*)&l_Std_Format_getIndent___closed__0_value;
static const lean_ctor_object l_Std_Format_getIndent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Std_Format_getIndent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_getIndent___closed__1_value_aux_0),((lean_object*)&l_Std_Format_getIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 177, 135, 35, 69, 72, 208, 204)}};
static const lean_object* l_Std_Format_getIndent___closed__1 = (const lean_object*)&l_Std_Format_getIndent___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Format_getIndent(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getIndent___boxed(lean_object*);
static const lean_string_object l_Std_Format_getUnicode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unicode"};
static const lean_object* l_Std_Format_getUnicode___closed__0 = (const lean_object*)&l_Std_Format_getUnicode___closed__0_value;
static const lean_ctor_object l_Std_Format_getUnicode___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Std_Format_getUnicode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_getUnicode___closed__1_value_aux_0),((lean_object*)&l_Std_Format_getUnicode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 238, 228, 128, 13, 57, 105, 12)}};
static const lean_object* l_Std_Format_getUnicode___closed__1 = (const lean_object*)&l_Std_Format_getUnicode___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Format_getUnicode(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getUnicode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "indentation"};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static lean_once_cell_t l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
static const lean_string_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getWidth___closed__1_value),LEAN_SCALAR_PTR_LITERAL(112, 1, 20, 146, 144, 212, 112, 144)}};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_width;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unicode characters"};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
static lean_once_cell_t l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_;
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getUnicode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 167, 78, 137, 229, 171, 91, 86)}};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_unicode;
static lean_once_cell_t l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_;
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 94, 144, 55, 30, 65, 170, 89)}};
static const lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_indent;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Format_getWidth(lean_object* v_o_6_){
_start:
{
lean_object* v_map_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_map_7_ = lean_ctor_get(v_o_6_, 0);
v___x_8_ = ((lean_object*)(l_Std_Format_getWidth___closed__2));
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
lean_dec_ref(v___x_10_);
if (lean_obj_tag(v_val_11_) == 3)
{
lean_object* v_v_12_; 
v_v_12_ = lean_ctor_get(v_val_11_, 0);
lean_inc(v_v_12_);
lean_dec_ref(v_val_11_);
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
LEAN_EXPORT lean_object* l_Std_Format_getWidth___boxed(lean_object* v_o_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Format_getWidth(v_o_13_);
lean_dec_ref(v_o_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_getIndent(lean_object* v_o_19_){
_start:
{
lean_object* v_map_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_map_20_ = lean_ctor_get(v_o_19_, 0);
v___x_21_ = ((lean_object*)(l_Std_Format_getIndent___closed__1));
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
lean_dec_ref(v___x_23_);
if (lean_obj_tag(v_val_24_) == 3)
{
lean_object* v_v_25_; 
v_v_25_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_v_25_);
lean_dec_ref(v_val_24_);
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
LEAN_EXPORT lean_object* l_Std_Format_getIndent___boxed(lean_object* v_o_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Format_getIndent(v_o_26_);
lean_dec_ref(v_o_26_);
return v_res_27_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_getUnicode(lean_object* v_o_32_){
_start:
{
lean_object* v_map_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; 
v_map_33_ = lean_ctor_get(v_o_32_, 0);
v___x_34_ = ((lean_object*)(l_Std_Format_getUnicode___closed__1));
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
lean_dec_ref(v___x_36_);
if (lean_obj_tag(v_val_37_) == 1)
{
uint8_t v_v_38_; 
v_v_38_ = lean_ctor_get_uint8(v_val_37_, 0);
lean_dec_ref(v_val_37_);
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
LEAN_EXPORT lean_object* l_Std_Format_getUnicode___boxed(lean_object* v_o_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_Format_getUnicode(v_o_39_);
lean_dec_ref(v_o_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object* v_name_42_, lean_object* v_decl_43_, lean_object* v_ref_44_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_69_, lean_object* v_decl_70_, lean_object* v_ref_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_69_, v_decl_70_, v_ref_71_);
lean_dec_ref(v_decl_70_);
return v_res_73_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_77_ = l_Std_Format_defWidth;
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l_Std_Format_getWidth___closed__2));
v___x_88_ = lean_obj_once(&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_);
v___x_89_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_90_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object* v_name_93_, lean_object* v_decl_94_, lean_object* v_ref_95_){
_start:
{
lean_object* v_defValue_97_; lean_object* v_descr_98_; lean_object* v_deprecation_x3f_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_defValue_97_ = lean_ctor_get(v_decl_94_, 0);
v_descr_98_ = lean_ctor_get(v_decl_94_, 1);
v_deprecation_x3f_99_ = lean_ctor_get(v_decl_94_, 2);
v___x_100_ = lean_alloc_ctor(1, 0, 1);
v___x_101_ = lean_unbox(v_defValue_97_);
lean_ctor_set_uint8(v___x_100_, 0, v___x_101_);
lean_inc(v_deprecation_x3f_99_);
lean_inc_ref(v_descr_98_);
lean_inc_n(v_name_93_, 2);
v___x_102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_102_, 0, v_name_93_);
lean_ctor_set(v___x_102_, 1, v_ref_95_);
lean_ctor_set(v___x_102_, 2, v___x_100_);
lean_ctor_set(v___x_102_, 3, v_descr_98_);
lean_ctor_set(v___x_102_, 4, v_deprecation_x3f_99_);
v___x_103_ = lean_register_option(v_name_93_, v___x_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_103_, 0);
lean_dec(v_unused_112_);
v___x_105_ = v___x_103_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_dec(v___x_103_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
lean_inc(v_defValue_97_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_name_93_);
lean_ctor_set(v___x_107_, 1, v_defValue_97_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_name_93_);
v_a_113_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_103_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_103_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_121_, lean_object* v_decl_122_, lean_object* v_ref_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_121_, v_decl_122_, v_ref_123_);
lean_dec_ref(v_decl_122_);
return v_res_125_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_127_ = lean_box(0);
v___x_128_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_129_ = l_Std_Format_defUnicode;
v___x_130_ = lean_box(v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_128_);
lean_ctor_set(v___x_131_, 2, v___x_127_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_138_ = ((lean_object*)(l_Std_Format_getUnicode___closed__1));
v___x_139_ = lean_obj_once(&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_);
v___x_140_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_141_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v___x_138_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_box(0);
v___x_145_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_146_ = l_Std_Format_defIndent;
v___x_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = ((lean_object*)(l_Std_Format_getIndent___closed__1));
v___x_155_ = lean_obj_once(&l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_, &l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once, _init_l___private_Lean_Data_Format_0__Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_);
v___x_156_ = ((lean_object*)(l___private_Lean_Data_Format_0__Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_));
v___x_157_ = l_Lean_Option_register___at___00__private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_154_, v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(lean_object* v_opts_160_, lean_object* v_opt_161_){
_start:
{
lean_object* v_name_162_; lean_object* v_defValue_163_; lean_object* v_map_164_; lean_object* v___x_165_; 
v_name_162_ = lean_ctor_get(v_opt_161_, 0);
v_defValue_163_ = lean_ctor_get(v_opt_161_, 1);
v_map_164_ = lean_ctor_get(v_opts_160_, 0);
v___x_165_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_164_, v_name_162_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_inc(v_defValue_163_);
return v_defValue_163_;
}
else
{
lean_object* v_val_166_; 
v_val_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_val_166_);
lean_dec_ref(v___x_165_);
if (lean_obj_tag(v_val_166_) == 3)
{
lean_object* v_v_167_; 
v_v_167_ = lean_ctor_get(v_val_166_, 0);
lean_inc(v_v_167_);
lean_dec_ref(v_val_166_);
return v_v_167_;
}
else
{
lean_dec(v_val_166_);
lean_inc(v_defValue_163_);
return v_defValue_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0___boxed(lean_object* v_opts_168_, lean_object* v_opt_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_opts_168_, v_opt_169_);
lean_dec_ref(v_opt_169_);
lean_dec_ref(v_opts_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27(lean_object* v_f_171_, lean_object* v_o_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = l_Std_Format_format_width;
v___x_174_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_o_172_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Std_Format_pretty(v_f_171_, v___x_174_, v___x_175_, v___x_175_);
lean_dec(v___x_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27___boxed(lean_object* v_f_177_, lean_object* v_o_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Format_pretty_x27(v_f_177_, v_o_178_);
lean_dec_ref(v_o_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object* v_n_180_){
_start:
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = 1;
v___x_182_ = l_Lean_Name_toString(v_n_180_, v___x_181_);
v___x_183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__0(lean_object* v_x_195_){
_start:
{
switch(lean_obj_tag(v_x_195_))
{
case 0:
{
lean_object* v_v_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_v_196_ = lean_ctor_get(v_x_195_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v_x_195_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_v_196_);
lean_dec(v_x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = l_String_quote(v_v_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 3);
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
case 1:
{
uint8_t v_v_205_; 
v_v_205_ = lean_ctor_get_uint8(v_x_195_, 0);
lean_dec_ref(v_x_195_);
if (v_v_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
return v___x_207_;
}
}
case 2:
{
lean_object* v_v_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_219_; 
v_v_208_ = lean_ctor_get(v_x_195_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_219_ == 0)
{
v___x_210_ = v_x_195_;
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_v_208_);
lean_dec(v_x_195_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_212_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_213_ = 1;
v___x_214_ = l_Lean_Name_toString(v_v_208_, v___x_213_);
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 3);
lean_ctor_set(v___x_210_, 0, v___x_214_);
v___x_216_ = v___x_210_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_212_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
}
case 3:
{
lean_object* v_v_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_v_220_ = lean_ctor_get(v_x_195_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v_x_195_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_v_220_);
lean_dec(v_x_195_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = l_Nat_reprFast(v_v_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
case 4:
{
lean_object* v_v_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_v_229_ = lean_ctor_get(v_x_195_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v_x_195_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_v_229_);
lean_dec(v_x_195_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = l_Int_repr(v_v_229_);
lean_dec(v_v_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 3);
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
default: 
{
lean_object* v_v_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; 
v_v_238_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_v_238_);
lean_dec_ref(v_x_195_);
v___x_239_ = lean_box(0);
v___x_240_ = 0;
v___x_241_ = l_Lean_Syntax_formatStx(v_v_238_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object* v_x_247_){
_start:
{
lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_312_; 
v_fst_248_ = lean_ctor_get(v_x_247_, 0);
v_snd_249_ = lean_ctor_get(v_x_247_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_247_);
if (v_isSharedCheck_312_ == 0)
{
v___x_251_ = v_x_247_;
v_isShared_252_ = v_isSharedCheck_312_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_inc(v_fst_248_);
lean_dec(v_x_247_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_312_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_253_ = 1;
v___x_254_ = l_Lean_Name_toString(v_fst_248_, v___x_253_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 5);
lean_ctor_set(v___x_251_, 1, v___x_256_);
lean_ctor_set(v___x_251_, 0, v___x_255_);
v___x_258_ = v___x_251_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_311_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
switch(lean_obj_tag(v_snd_249_))
{
case 0:
{
lean_object* v_v_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_268_; 
v_v_259_ = lean_ctor_get(v_snd_249_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_268_ == 0)
{
v___x_261_ = v_snd_249_;
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_v_259_);
lean_dec(v_snd_249_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_268_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = l_String_quote(v_v_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 3);
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_267_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_258_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
return v___x_266_;
}
}
}
case 1:
{
uint8_t v_v_269_; 
v_v_269_ = lean_ctor_get_uint8(v_snd_249_, 0);
lean_dec_ref(v_snd_249_);
if (v_v_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_258_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_258_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
case 2:
{
lean_object* v_v_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_285_; 
v_v_274_ = lean_ctor_get(v_snd_249_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_285_ == 0)
{
v___x_276_ = v_snd_249_;
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_v_274_);
lean_dec(v_snd_249_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_279_ = l_Lean_Name_toString(v_v_274_, v___x_253_);
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 3);
lean_ctor_set(v___x_276_, 0, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_284_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_278_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_258_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
}
}
case 3:
{
lean_object* v_v_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_295_; 
v_v_286_ = lean_ctor_get(v_snd_249_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_295_ == 0)
{
v___x_288_ = v_snd_249_;
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_v_286_);
lean_dec(v_snd_249_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = l_Nat_reprFast(v_v_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_294_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_258_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
}
}
case 4:
{
lean_object* v_v_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
v_v_296_ = lean_ctor_get(v_snd_249_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_305_ == 0)
{
v___x_298_ = v_snd_249_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_v_296_);
lean_dec(v_snd_249_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Int_repr(v_v_296_);
lean_dec(v_v_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 3);
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
lean_ctor_set(v___x_303_, 0, v___x_258_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
}
default: 
{
lean_object* v_v_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_v_306_ = lean_ctor_get(v_snd_249_, 0);
lean_inc(v_v_306_);
lean_dec_ref(v_snd_249_);
v___x_307_ = lean_box(0);
v___x_308_ = 0;
v___x_309_ = l_Lean_Syntax_formatStx(v_v_306_, v___x_307_, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_258_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_nat_to_int(v_a_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_dec(v_x_317_);
return v_x_318_;
}
else
{
lean_object* v_head_320_; lean_object* v_tail_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_407_; 
v_head_320_ = lean_ctor_get(v_x_319_, 0);
v_tail_321_ = lean_ctor_get(v_x_319_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_407_ == 0)
{
v___x_323_ = v_x_319_;
v_isShared_324_ = v_isSharedCheck_407_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_tail_321_);
lean_inc(v_head_320_);
lean_dec(v_x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_407_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_406_; 
v_fst_325_ = lean_ctor_get(v_head_320_, 0);
v_snd_326_ = lean_ctor_get(v_head_320_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_head_320_);
if (v_isSharedCheck_406_ == 0)
{
v___x_328_ = v_head_320_;
v_isShared_329_ = v_isSharedCheck_406_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v_head_320_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_406_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
lean_inc(v_x_317_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 5);
lean_ctor_set(v___x_328_, 1, v_x_317_);
lean_ctor_set(v___x_328_, 0, v_x_318_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_318_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_317_);
v___x_331_ = v_reuseFailAlloc_405_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_332_ = 1;
v___x_333_ = l_Lean_Name_toString(v_fst_325_, v___x_332_);
v___x_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
v___x_335_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 5);
lean_ctor_set(v___x_323_, 1, v___x_335_);
lean_ctor_set(v___x_323_, 0, v___x_334_);
v___x_337_ = v___x_323_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_404_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
switch(lean_obj_tag(v_snd_326_))
{
case 0:
{
lean_object* v_v_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_349_; 
v_v_338_ = lean_ctor_get(v_snd_326_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_349_ == 0)
{
v___x_340_ = v_snd_326_;
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_v_338_);
lean_dec(v_snd_326_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = l_String_quote(v_v_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 3);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_337_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_331_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v_x_318_ = v___x_346_;
v_x_319_ = v_tail_321_;
goto _start;
}
}
}
case 1:
{
uint8_t v_v_350_; 
v_v_350_ = lean_ctor_get_uint8(v_snd_326_, 0);
lean_dec_ref(v_snd_326_);
if (v_v_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_337_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_331_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v_x_318_ = v___x_353_;
v_x_319_ = v_tail_321_;
goto _start;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_337_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_331_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v_x_318_ = v___x_357_;
v_x_319_ = v_tail_321_;
goto _start;
}
}
case 2:
{
lean_object* v_v_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_372_; 
v_v_359_ = lean_ctor_get(v_snd_326_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_372_ == 0)
{
v___x_361_ = v_snd_326_;
v_isShared_362_ = v_isSharedCheck_372_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_v_359_);
lean_dec(v_snd_326_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_372_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_364_ = l_Lean_Name_toString(v_v_359_, v___x_332_);
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 3);
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_371_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_363_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_337_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_331_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v_x_318_ = v___x_369_;
v_x_319_ = v_tail_321_;
goto _start;
}
}
}
case 3:
{
lean_object* v_v_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_v_373_ = lean_ctor_get(v_snd_326_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v_snd_326_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_v_373_);
lean_dec(v_snd_326_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = l_Nat_reprFast(v_v_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_337_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_331_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v_x_318_ = v___x_381_;
v_x_319_ = v_tail_321_;
goto _start;
}
}
}
case 4:
{
lean_object* v_v_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_396_; 
v_v_385_ = lean_ctor_get(v_snd_326_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_396_ == 0)
{
v___x_387_ = v_snd_326_;
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_v_385_);
lean_dec(v_snd_326_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_396_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = l_Int_repr(v_v_385_);
lean_dec(v_v_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 3);
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_337_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_331_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v_x_318_ = v___x_393_;
v_x_319_ = v_tail_321_;
goto _start;
}
}
}
default: 
{
lean_object* v_v_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_v_397_ = lean_ctor_get(v_snd_326_, 0);
lean_inc(v_v_397_);
lean_dec_ref(v_snd_326_);
v___x_398_ = lean_box(0);
v___x_399_ = 0;
v___x_400_ = l_Lean_Syntax_formatStx(v_v_397_, v___x_398_, v___x_399_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_337_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_331_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v_x_318_ = v___x_402_;
v_x_319_ = v_tail_321_;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v___x_410_; 
lean_dec(v_x_409_);
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_tail_411_; 
v_tail_411_ = lean_ctor_get(v_x_408_, 1);
if (lean_obj_tag(v_tail_411_) == 0)
{
lean_object* v_head_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_x_409_);
v_head_412_ = lean_ctor_get(v_x_408_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_x_408_, 1);
lean_dec(v_unused_496_);
v___x_414_ = v_x_408_;
v_isShared_415_ = v_isSharedCheck_495_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_head_412_);
lean_dec(v_x_408_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_495_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_494_; 
v_fst_416_ = lean_ctor_get(v_head_412_, 0);
v_snd_417_ = lean_ctor_get(v_head_412_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_head_412_);
if (v_isSharedCheck_494_ == 0)
{
v___x_419_ = v_head_412_;
v_isShared_420_ = v_isSharedCheck_494_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
lean_dec(v_head_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_494_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_421_ = 1;
v___x_422_ = l_Lean_Name_toString(v_fst_416_, v___x_421_);
v___x_423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 5);
lean_ctor_set(v___x_419_, 1, v___x_424_);
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_493_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
switch(lean_obj_tag(v_snd_417_))
{
case 0:
{
lean_object* v_v_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_438_; 
v_v_427_ = lean_ctor_get(v_snd_417_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_snd_417_);
if (v_isSharedCheck_438_ == 0)
{
v___x_429_ = v_snd_417_;
v_isShared_430_ = v_isSharedCheck_438_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_v_427_);
lean_dec(v_snd_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_438_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_String_quote(v_v_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 3);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_433_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_435_ = v___x_414_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
case 1:
{
uint8_t v_v_439_; 
v_v_439_ = lean_ctor_get_uint8(v_snd_417_, 0);
lean_dec_ref(v_snd_417_);
if (v_v_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_440_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_442_ = v___x_414_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_444_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_446_ = v___x_414_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
case 2:
{
lean_object* v_v_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
v_v_448_ = lean_ctor_get(v_snd_417_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_snd_417_);
if (v_isSharedCheck_461_ == 0)
{
v___x_450_ = v_snd_417_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_v_448_);
lean_dec(v_snd_417_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_453_ = l_Lean_Name_toString(v_v_448_, v___x_421_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 3);
lean_ctor_set(v___x_450_, 0, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_460_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_455_);
lean_ctor_set(v___x_414_, 0, v___x_452_);
v___x_457_ = v___x_414_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_459_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_426_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
}
}
case 3:
{
lean_object* v_v_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_473_; 
v_v_462_ = lean_ctor_get(v_snd_417_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_snd_417_);
if (v_isSharedCheck_473_ == 0)
{
v___x_464_ = v_snd_417_;
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_v_462_);
lean_dec(v_snd_417_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Nat_reprFast(v_v_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_468_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_470_ = v___x_414_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
case 4:
{
lean_object* v_v_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_v_474_ = lean_ctor_get(v_snd_417_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_snd_417_);
if (v_isSharedCheck_485_ == 0)
{
v___x_476_ = v_snd_417_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_v_474_);
lean_dec(v_snd_417_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l_Int_repr(v_v_474_);
lean_dec(v_v_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 3);
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_480_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_482_ = v___x_414_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
default: 
{
lean_object* v_v_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v_v_486_ = lean_ctor_get(v_snd_417_, 0);
lean_inc(v_v_486_);
lean_dec_ref(v_snd_417_);
v___x_487_ = lean_box(0);
v___x_488_ = 0;
v___x_489_ = l_Lean_Syntax_formatStx(v_v_486_, v___x_487_, v___x_488_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 5);
lean_ctor_set(v___x_414_, 1, v___x_489_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_491_ = v___x_414_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
else
{
lean_object* v_head_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_587_; 
lean_inc(v_tail_411_);
v_head_497_ = lean_ctor_get(v_x_408_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_x_408_, 1);
lean_dec(v_unused_588_);
v___x_499_ = v_x_408_;
v_isShared_500_ = v_isSharedCheck_587_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_head_497_);
lean_dec(v_x_408_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_587_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_586_; 
v_fst_501_ = lean_ctor_get(v_head_497_, 0);
v_snd_502_ = lean_ctor_get(v_head_497_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_head_497_);
if (v_isSharedCheck_586_ == 0)
{
v___x_504_ = v_head_497_;
v_isShared_505_ = v_isSharedCheck_586_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snd_502_);
lean_inc(v_fst_501_);
lean_dec(v_head_497_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_586_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_506_ = 1;
v___x_507_ = l_Lean_Name_toString(v_fst_501_, v___x_506_);
v___x_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 5);
lean_ctor_set(v___x_504_, 1, v___x_509_);
lean_ctor_set(v___x_504_, 0, v___x_508_);
v___x_511_ = v___x_504_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_585_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
switch(lean_obj_tag(v_snd_502_))
{
case 0:
{
lean_object* v_v_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_v_512_ = lean_ctor_get(v_snd_502_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_snd_502_);
if (v_isSharedCheck_524_ == 0)
{
v___x_514_ = v_snd_502_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_v_512_);
lean_dec(v_snd_502_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = l_String_quote(v_v_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 3);
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_523_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_518_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_520_ = v___x_499_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_522_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_520_, v_tail_411_);
return v___x_521_;
}
}
}
}
case 1:
{
uint8_t v_v_525_; 
v_v_525_ = lean_ctor_get_uint8(v_snd_502_, 0);
lean_dec_ref(v_snd_502_);
if (v_v_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_526_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_528_ = v___x_499_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_528_, v_tail_411_);
return v___x_529_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_531_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_533_ = v___x_499_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_533_, v_tail_411_);
return v___x_534_;
}
}
}
case 2:
{
lean_object* v_v_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_550_; 
v_v_536_ = lean_ctor_get(v_snd_502_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_snd_502_);
if (v_isSharedCheck_550_ == 0)
{
v___x_538_ = v_snd_502_;
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_v_536_);
lean_dec(v_snd_502_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_550_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_541_ = l_Lean_Name_toString(v_v_536_, v___x_506_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 3);
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_543_);
lean_ctor_set(v___x_499_, 0, v___x_540_);
v___x_545_ = v___x_499_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_511_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_546_, v_tail_411_);
return v___x_547_;
}
}
}
}
case 3:
{
lean_object* v_v_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_563_; 
v_v_551_ = lean_ctor_get(v_snd_502_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_snd_502_);
if (v_isSharedCheck_563_ == 0)
{
v___x_553_ = v_snd_502_;
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_v_551_);
lean_dec(v_snd_502_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Nat_reprFast(v_v_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_562_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_557_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_559_ = v___x_499_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_559_, v_tail_411_);
return v___x_560_;
}
}
}
}
case 4:
{
lean_object* v_v_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_576_; 
v_v_564_ = lean_ctor_get(v_snd_502_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_snd_502_);
if (v_isSharedCheck_576_ == 0)
{
v___x_566_ = v_snd_502_;
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_v_564_);
lean_dec(v_snd_502_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Int_repr(v_v_564_);
lean_dec(v_v_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 3);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_570_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_572_ = v___x_499_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_572_, v_tail_411_);
return v___x_573_;
}
}
}
}
default: 
{
lean_object* v_v_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v_v_577_ = lean_ctor_get(v_snd_502_, 0);
lean_inc(v_v_577_);
lean_dec_ref(v_snd_502_);
v___x_578_ = lean_box(0);
v___x_579_ = 0;
v___x_580_ = l_Lean_Syntax_formatStx(v_v_577_, v___x_578_, v___x_579_);
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
lean_ctor_set(v___x_499_, 1, v___x_580_);
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_582_ = v___x_499_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_584_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
v___x_583_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_409_, v___x_582_, v_tail_411_);
return v___x_583_;
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
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_Lean_formatKVMap___closed__2));
v___x_595_ = lean_string_length(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__5(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Lean_formatKVMap___closed__4, &l_Lean_formatKVMap___closed__4_once, _init_l_Lean_formatKVMap___closed__4);
v___x_597_ = lean_nat_to_int(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* v_m_602_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_603_ = ((lean_object*)(l_Lean_formatKVMap___closed__1));
v___x_604_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_602_, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_formatKVMap___closed__5, &l_Lean_formatKVMap___closed__5_once, _init_l_Lean_formatKVMap___closed__5);
v___x_606_ = ((lean_object*)(l_Lean_formatKVMap___closed__6));
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_604_);
v___x_608_ = ((lean_object*)(l_Lean_formatKVMap___closed__7));
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_605_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = 0;
v___x_612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_611_);
return v___x_612_;
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
res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_width = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_width);
lean_dec_ref(res);
res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_unicode = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_unicode);
lean_dec_ref(res);
res = l___private_Lean_Data_Format_0__Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_indent = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_indent);
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
