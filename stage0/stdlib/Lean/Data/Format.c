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
extern uint8_t l_Std_Format_defUnicode;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defIndent;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "indentation"};
static const lean_object* l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static lean_once_cell_t l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_;
static const lean_string_object l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_string_object l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
static const lean_ctor_object l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getWidth___closed__1_value),LEAN_SCALAR_PTR_LITERAL(112, 1, 20, 146, 144, 212, 112, 144)}};
static const lean_object* l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_width;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unicode characters"};
static const lean_object* l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
static lean_once_cell_t l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_;
static const lean_ctor_object l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getUnicode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 167, 78, 137, 229, 171, 91, 86)}};
static const lean_object* l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_unicode;
static lean_once_cell_t l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_;
static const lean_ctor_object l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Std_Format_initFn___closed__3_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Std_Format_getWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 134, 113, 210, 183, 126, 169, 25)}};
static const lean_ctor_object l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Std_Format_getIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 94, 144, 55, 30, 65, 170, 89)}};
static const lean_object* l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_ = (const lean_object*)&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_instToFormatDataValue___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToFormatDataValue___lam__0___closed__6;
static const lean_string_object l_Lean_instToFormatDataValue___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_instToFormatDataValue___lam__0___closed__7 = (const lean_object*)&l_Lean_instToFormatDataValue___lam__0___closed__7_value;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(lean_object* v_name_42_, lean_object* v_decl_43_, lean_object* v_ref_44_){
_start:
{
lean_object* v_defValue_46_; lean_object* v_descr_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_73_; 
v_defValue_46_ = lean_ctor_get(v_decl_43_, 0);
v_descr_47_ = lean_ctor_get(v_decl_43_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_decl_43_);
if (v_isSharedCheck_73_ == 0)
{
v___x_49_ = v_decl_43_;
v_isShared_50_ = v_isSharedCheck_73_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_descr_47_);
lean_inc(v_defValue_46_);
lean_dec(v_decl_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_73_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_inc(v_defValue_46_);
v___x_51_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_51_, 0, v_defValue_46_);
lean_inc(v_name_42_);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_name_42_);
lean_ctor_set(v___x_52_, 1, v_ref_44_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_descr_47_);
lean_inc(v_name_42_);
v___x_53_ = lean_register_option(v_name_42_, v___x_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_63_; 
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_53_, 0);
lean_dec(v_unused_64_);
v___x_55_ = v___x_53_;
v_isShared_56_ = v_isSharedCheck_63_;
goto v_resetjp_54_;
}
else
{
lean_dec(v___x_53_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_63_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v_defValue_46_);
lean_ctor_set(v___x_49_, 0, v_name_42_);
v___x_58_ = v___x_49_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_name_42_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_defValue_46_);
v___x_58_ = v_reuseFailAlloc_62_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_del_object(v___x_49_);
lean_dec(v_defValue_46_);
lean_dec(v_name_42_);
v_a_65_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_53_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_53_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_74_, lean_object* v_decl_75_, lean_object* v_ref_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v_name_74_, v_decl_75_, v_ref_76_);
return v_res_78_;
}
}
static lean_object* _init_l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_81_ = l_Std_Format_defWidth;
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = ((lean_object*)(l_Std_Format_getWidth___closed__2));
v___x_92_ = lean_obj_once(&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_, &l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__once, _init_l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_);
v___x_93_ = ((lean_object*)(l_Std_Format_initFn___closed__4_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_94_ = l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_91_, v___x_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4____boxed(lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(lean_object* v_name_97_, lean_object* v_decl_98_, lean_object* v_ref_99_){
_start:
{
lean_object* v_defValue_101_; lean_object* v_descr_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_129_; 
v_defValue_101_ = lean_ctor_get(v_decl_98_, 0);
v_descr_102_ = lean_ctor_get(v_decl_98_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_decl_98_);
if (v_isSharedCheck_129_ == 0)
{
v___x_104_ = v_decl_98_;
v_isShared_105_ = v_isSharedCheck_129_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_descr_102_);
lean_inc(v_defValue_101_);
lean_dec(v_decl_98_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_129_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_alloc_ctor(1, 0, 1);
v___x_107_ = lean_unbox(v_defValue_101_);
lean_ctor_set_uint8(v___x_106_, 0, v___x_107_);
lean_inc(v_name_97_);
v___x_108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_108_, 0, v_name_97_);
lean_ctor_set(v___x_108_, 1, v_ref_99_);
lean_ctor_set(v___x_108_, 2, v___x_106_);
lean_ctor_set(v___x_108_, 3, v_descr_102_);
lean_inc(v_name_97_);
v___x_109_ = lean_register_option(v_name_97_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_119_; 
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v___x_109_, 0);
lean_dec(v_unused_120_);
v___x_111_ = v___x_109_;
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
else
{
lean_dec(v___x_109_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_119_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_defValue_101_);
lean_ctor_set(v___x_104_, 0, v_name_97_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_name_97_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_defValue_101_);
v___x_114_ = v_reuseFailAlloc_118_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_del_object(v___x_104_);
lean_dec(v_defValue_101_);
lean_dec(v_name_97_);
v_a_121_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_109_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_109_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_130_, lean_object* v_decl_131_, lean_object* v_ref_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v_name_130_, v_decl_131_, v_ref_132_);
return v_res_134_;
}
}
static lean_object* _init_l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = ((lean_object*)(l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_137_ = l_Std_Format_defUnicode;
v___x_138_ = lean_box(v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_136_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = ((lean_object*)(l_Std_Format_getUnicode___closed__1));
v___x_147_ = lean_obj_once(&l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_, &l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__once, _init_l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_);
v___x_148_ = ((lean_object*)(l_Std_Format_initFn___closed__2_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_));
v___x_149_ = l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4__spec__0(v___x_146_, v___x_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4____boxed(lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
return v_res_151_;
}
}
static lean_object* _init_l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((lean_object*)(l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_));
v___x_153_ = l_Std_Format_defIndent;
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = ((lean_object*)(l_Std_Format_getIndent___closed__1));
v___x_162_ = lean_obj_once(&l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_, &l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4__once, _init_l_Std_Format_initFn___closed__0_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_);
v___x_163_ = ((lean_object*)(l_Std_Format_initFn___closed__1_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_));
v___x_164_ = l_Lean_Option_register___at___00Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4__spec__0(v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4____boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(lean_object* v_opts_167_, lean_object* v_opt_168_){
_start:
{
lean_object* v_name_169_; lean_object* v_defValue_170_; lean_object* v_map_171_; lean_object* v___x_172_; 
v_name_169_ = lean_ctor_get(v_opt_168_, 0);
v_defValue_170_ = lean_ctor_get(v_opt_168_, 1);
v_map_171_ = lean_ctor_get(v_opts_167_, 0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_171_, v_name_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_inc(v_defValue_170_);
return v_defValue_170_;
}
else
{
lean_object* v_val_173_; 
v_val_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_173_);
lean_dec_ref(v___x_172_);
if (lean_obj_tag(v_val_173_) == 3)
{
lean_object* v_v_174_; 
v_v_174_ = lean_ctor_get(v_val_173_, 0);
lean_inc(v_v_174_);
lean_dec_ref(v_val_173_);
return v_v_174_;
}
else
{
lean_dec(v_val_173_);
lean_inc(v_defValue_170_);
return v_defValue_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0___boxed(lean_object* v_opts_175_, lean_object* v_opt_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_opts_175_, v_opt_176_);
lean_dec_ref(v_opt_176_);
lean_dec_ref(v_opts_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27(lean_object* v_f_178_, lean_object* v_o_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = l_Std_Format_format_width;
v___x_181_ = l_Lean_Option_get___at___00Std_Format_pretty_x27_spec__0(v_o_179_, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_Std_Format_pretty(v_f_178_, v___x_181_, v___x_182_, v___x_182_);
lean_dec(v___x_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27___boxed(lean_object* v_f_184_, lean_object* v_o_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Format_pretty_x27(v_f_184_, v_o_185_);
lean_dec_ref(v_o_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0(lean_object* v_n_187_){
_start:
{
uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = 1;
v___x_189_ = l_Lean_Name_toString(v_n_187_, v___x_188_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_instToFormatDataValue___lam__0___closed__6(void){
_start:
{
lean_object* v_natZero_202_; lean_object* v_intZero_203_; 
v_natZero_202_ = lean_unsigned_to_nat(0u);
v_intZero_203_ = lean_nat_to_int(v_natZero_202_);
return v_intZero_203_;
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
lean_dec_ref(v_x_205_);
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
lean_object* v_v_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_260_; 
v_v_239_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_260_ == 0)
{
v___x_241_ = v_x_205_;
v_isShared_242_ = v_isSharedCheck_260_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_v_239_);
lean_dec(v_x_205_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_260_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_intZero_243_; uint8_t v_isNeg_244_; 
v_intZero_243_ = lean_obj_once(&l_Lean_instToFormatDataValue___lam__0___closed__6, &l_Lean_instToFormatDataValue___lam__0___closed__6_once, _init_l_Lean_instToFormatDataValue___lam__0___closed__6);
v_isNeg_244_ = lean_int_dec_lt(v_v_239_, v_intZero_243_);
if (v_isNeg_244_ == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v_a_245_ = lean_nat_abs(v_v_239_);
lean_dec(v_v_239_);
v___x_246_ = l_Nat_reprFast(v_a_245_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 0, v___x_246_);
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v_abs_250_; lean_object* v_one_251_; lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v_abs_250_ = lean_nat_abs(v_v_239_);
lean_dec(v_v_239_);
v_one_251_ = lean_unsigned_to_nat(1u);
v_a_252_ = lean_nat_sub(v_abs_250_, v_one_251_);
lean_dec(v_abs_250_);
v___x_253_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__7));
v___x_254_ = lean_nat_add(v_a_252_, v_one_251_);
lean_dec(v_a_252_);
v___x_255_ = l_Nat_reprFast(v___x_254_);
v___x_256_ = lean_string_append(v___x_253_, v___x_255_);
lean_dec_ref(v___x_255_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 0, v___x_256_);
v___x_258_ = v___x_241_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
default: 
{
lean_object* v_v_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v_v_261_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_v_261_);
lean_dec_ref(v_x_205_);
v___x_262_ = lean_box(0);
v___x_263_ = 0;
v___x_264_ = l_Lean_Syntax_formatStx(v_v_261_, v___x_262_, v___x_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object* v_x_270_){
_start:
{
lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_349_; 
v_fst_271_ = lean_ctor_get(v_x_270_, 0);
v_snd_272_ = lean_ctor_get(v_x_270_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_349_ == 0)
{
v___x_274_ = v_x_270_;
v_isShared_275_ = v_isSharedCheck_349_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_snd_272_);
lean_inc(v_fst_271_);
lean_dec(v_x_270_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_349_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_276_ = 1;
v___x_277_ = l_Lean_Name_toString(v_fst_271_, v___x_276_);
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_275_ == 0)
{
lean_ctor_set_tag(v___x_274_, 5);
lean_ctor_set(v___x_274_, 1, v___x_279_);
lean_ctor_set(v___x_274_, 0, v___x_278_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_279_);
v___x_281_ = v_reuseFailAlloc_348_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
switch(lean_obj_tag(v_snd_272_))
{
case 0:
{
lean_object* v_v_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_291_; 
v_v_282_ = lean_ctor_get(v_snd_272_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_snd_272_);
if (v_isSharedCheck_291_ == 0)
{
v___x_284_ = v_snd_272_;
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_v_282_);
lean_dec(v_snd_272_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = l_String_quote(v_v_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set_tag(v___x_284_, 3);
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_281_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
return v___x_289_;
}
}
}
case 1:
{
uint8_t v_v_292_; 
v_v_292_ = lean_ctor_get_uint8(v_snd_272_, 0);
lean_dec_ref(v_snd_272_);
if (v_v_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_281_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_281_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
}
case 2:
{
lean_object* v_v_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_308_; 
v_v_297_ = lean_ctor_get(v_snd_272_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_snd_272_);
if (v_isSharedCheck_308_ == 0)
{
v___x_299_ = v_snd_272_;
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_v_297_);
lean_dec(v_snd_272_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_302_ = l_Lean_Name_toString(v_v_297_, v___x_276_);
if (v_isShared_300_ == 0)
{
lean_ctor_set_tag(v___x_299_, 3);
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_307_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_301_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_281_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
return v___x_306_;
}
}
}
case 3:
{
lean_object* v_v_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_318_; 
v_v_309_ = lean_ctor_get(v_snd_272_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_snd_272_);
if (v_isSharedCheck_318_ == 0)
{
v___x_311_ = v_snd_272_;
v_isShared_312_ = v_isSharedCheck_318_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_v_309_);
lean_dec(v_snd_272_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_318_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l_Nat_reprFast(v_v_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_281_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
}
}
case 4:
{
lean_object* v_v_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_342_; 
v_v_319_ = lean_ctor_get(v_snd_272_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_snd_272_);
if (v_isSharedCheck_342_ == 0)
{
v___x_321_ = v_snd_272_;
v_isShared_322_ = v_isSharedCheck_342_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_v_319_);
lean_dec(v_snd_272_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_342_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_intZero_323_; uint8_t v_isNeg_324_; 
v_intZero_323_ = lean_obj_once(&l_Lean_instToFormatDataValue___lam__0___closed__6, &l_Lean_instToFormatDataValue___lam__0___closed__6_once, _init_l_Lean_instToFormatDataValue___lam__0___closed__6);
v_isNeg_324_ = lean_int_dec_lt(v_v_319_, v_intZero_323_);
if (v_isNeg_324_ == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_a_325_ = lean_nat_abs(v_v_319_);
lean_dec(v_v_319_);
v___x_326_ = l_Nat_reprFast(v_a_325_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
lean_ctor_set(v___x_321_, 0, v___x_326_);
v___x_328_ = v___x_321_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_281_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
else
{
lean_object* v_abs_331_; lean_object* v_one_332_; lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v_abs_331_ = lean_nat_abs(v_v_319_);
lean_dec(v_v_319_);
v_one_332_ = lean_unsigned_to_nat(1u);
v_a_333_ = lean_nat_sub(v_abs_331_, v_one_332_);
lean_dec(v_abs_331_);
v___x_334_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__7));
v___x_335_ = lean_nat_add(v_a_333_, v_one_332_);
lean_dec(v_a_333_);
v___x_336_ = l_Nat_reprFast(v___x_335_);
v___x_337_ = lean_string_append(v___x_334_, v___x_336_);
lean_dec_ref(v___x_336_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
lean_ctor_set(v___x_321_, 0, v___x_337_);
v___x_339_ = v___x_321_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_341_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_281_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
return v___x_340_;
}
}
}
}
default: 
{
lean_object* v_v_343_; lean_object* v___x_344_; uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_v_343_ = lean_ctor_get(v_snd_272_, 0);
lean_inc(v_v_343_);
lean_dec_ref(v_snd_272_);
v___x_344_ = lean_box(0);
v___x_345_ = 0;
v___x_346_ = l_Lean_Syntax_formatStx(v_v_343_, v___x_344_, v___x_345_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_281_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object* v_a_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_nat_to_int(v_a_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_dec(v_x_354_);
return v_x_355_;
}
else
{
lean_object* v_head_357_; lean_object* v_tail_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_460_; 
v_head_357_ = lean_ctor_get(v_x_356_, 0);
v_tail_358_ = lean_ctor_get(v_x_356_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_460_ == 0)
{
v___x_360_ = v_x_356_;
v_isShared_361_ = v_isSharedCheck_460_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_tail_358_);
lean_inc(v_head_357_);
lean_dec(v_x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_460_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_459_; 
v_fst_362_ = lean_ctor_get(v_head_357_, 0);
v_snd_363_ = lean_ctor_get(v_head_357_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_head_357_);
if (v_isSharedCheck_459_ == 0)
{
v___x_365_ = v_head_357_;
v_isShared_366_ = v_isSharedCheck_459_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v_head_357_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_459_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
lean_inc(v_x_354_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 5);
lean_ctor_set(v___x_365_, 1, v_x_354_);
lean_ctor_set(v___x_365_, 0, v_x_355_);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_x_355_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_x_354_);
v___x_368_ = v_reuseFailAlloc_458_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_369_ = 1;
v___x_370_ = l_Lean_Name_toString(v_fst_362_, v___x_369_);
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
v___x_372_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 5);
lean_ctor_set(v___x_360_, 1, v___x_372_);
lean_ctor_set(v___x_360_, 0, v___x_371_);
v___x_374_ = v___x_360_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_457_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
switch(lean_obj_tag(v_snd_363_))
{
case 0:
{
lean_object* v_v_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_386_; 
v_v_375_ = lean_ctor_get(v_snd_363_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_386_ == 0)
{
v___x_377_ = v_snd_363_;
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_v_375_);
lean_dec(v_snd_363_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_String_quote(v_v_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 3);
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_374_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_368_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v_x_355_ = v___x_383_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
}
case 1:
{
uint8_t v_v_387_; 
v_v_387_ = lean_ctor_get_uint8(v_snd_363_, 0);
lean_dec_ref(v_snd_363_);
if (v_v_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_374_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_368_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v_x_355_ = v___x_390_;
v_x_356_ = v_tail_358_;
goto _start;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_374_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_368_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v_x_355_ = v___x_394_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
case 2:
{
lean_object* v_v_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_409_; 
v_v_396_ = lean_ctor_get(v_snd_363_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_409_ == 0)
{
v___x_398_ = v_snd_363_;
v_isShared_399_ = v_isSharedCheck_409_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_v_396_);
lean_dec(v_snd_363_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_409_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_400_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_401_ = l_Lean_Name_toString(v_v_396_, v___x_369_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 3);
lean_ctor_set(v___x_398_, 0, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_408_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_400_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_374_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_368_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v_x_355_ = v___x_406_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
}
case 3:
{
lean_object* v_v_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_v_410_ = lean_ctor_get(v_snd_363_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v_snd_363_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_v_410_);
lean_dec(v_snd_363_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Nat_reprFast(v_v_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_374_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_368_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v_x_355_ = v___x_418_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
}
case 4:
{
lean_object* v_v_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_449_; 
v_v_422_ = lean_ctor_get(v_snd_363_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_449_ == 0)
{
v___x_424_ = v_snd_363_;
v_isShared_425_ = v_isSharedCheck_449_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_v_422_);
lean_dec(v_snd_363_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_449_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_intZero_426_; uint8_t v_isNeg_427_; 
v_intZero_426_ = lean_obj_once(&l_Lean_instToFormatDataValue___lam__0___closed__6, &l_Lean_instToFormatDataValue___lam__0___closed__6_once, _init_l_Lean_instToFormatDataValue___lam__0___closed__6);
v_isNeg_427_ = lean_int_dec_lt(v_v_422_, v_intZero_426_);
if (v_isNeg_427_ == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v_a_428_ = lean_nat_abs(v_v_422_);
lean_dec(v_v_422_);
v___x_429_ = l_Nat_reprFast(v_a_428_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 3);
lean_ctor_set(v___x_424_, 0, v___x_429_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_374_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_368_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v_x_355_ = v___x_433_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
else
{
lean_object* v_abs_436_; lean_object* v_one_437_; lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_abs_436_ = lean_nat_abs(v_v_422_);
lean_dec(v_v_422_);
v_one_437_ = lean_unsigned_to_nat(1u);
v_a_438_ = lean_nat_sub(v_abs_436_, v_one_437_);
lean_dec(v_abs_436_);
v___x_439_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__7));
v___x_440_ = lean_nat_add(v_a_438_, v_one_437_);
lean_dec(v_a_438_);
v___x_441_ = l_Nat_reprFast(v___x_440_);
v___x_442_ = lean_string_append(v___x_439_, v___x_441_);
lean_dec_ref(v___x_441_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 3);
lean_ctor_set(v___x_424_, 0, v___x_442_);
v___x_444_ = v___x_424_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_374_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_368_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v_x_355_ = v___x_446_;
v_x_356_ = v_tail_358_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_v_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_v_450_ = lean_ctor_get(v_snd_363_, 0);
lean_inc(v_v_450_);
lean_dec_ref(v_snd_363_);
v___x_451_ = lean_box(0);
v___x_452_ = 0;
v___x_453_ = l_Lean_Syntax_formatStx(v_v_450_, v___x_451_, v___x_452_);
v___x_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_374_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_368_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v_x_355_ = v___x_455_;
v_x_356_ = v_tail_358_;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_463_; 
lean_dec(v_x_462_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v_tail_464_; 
v_tail_464_ = lean_ctor_get(v_x_461_, 1);
if (lean_obj_tag(v_tail_464_) == 0)
{
lean_object* v_head_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_x_462_);
v_head_465_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_x_461_, 1);
lean_dec(v_unused_565_);
v___x_467_ = v_x_461_;
v_isShared_468_ = v_isSharedCheck_564_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_head_465_);
lean_dec(v_x_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_564_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_563_; 
v_fst_469_ = lean_ctor_get(v_head_465_, 0);
v_snd_470_ = lean_ctor_get(v_head_465_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_head_465_);
if (v_isSharedCheck_563_ == 0)
{
v___x_472_ = v_head_465_;
v_isShared_473_ = v_isSharedCheck_563_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snd_470_);
lean_inc(v_fst_469_);
lean_dec(v_head_465_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_563_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_474_ = 1;
v___x_475_ = l_Lean_Name_toString(v_fst_469_, v___x_474_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 5);
lean_ctor_set(v___x_472_, 1, v___x_477_);
lean_ctor_set(v___x_472_, 0, v___x_476_);
v___x_479_ = v___x_472_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_562_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
switch(lean_obj_tag(v_snd_470_))
{
case 0:
{
lean_object* v_v_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_491_; 
v_v_480_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_491_ == 0)
{
v___x_482_ = v_snd_470_;
v_isShared_483_ = v_isSharedCheck_491_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_v_480_);
lean_dec(v_snd_470_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_491_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = l_String_quote(v_v_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 3);
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_486_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_488_ = v___x_467_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
case 1:
{
uint8_t v_v_492_; 
v_v_492_ = lean_ctor_get_uint8(v_snd_470_, 0);
lean_dec_ref(v_snd_470_);
if (v_v_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_493_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_495_ = v___x_467_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_497_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_499_ = v___x_467_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
case 2:
{
lean_object* v_v_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_514_; 
v_v_501_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_514_ == 0)
{
v___x_503_ = v_snd_470_;
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_v_501_);
lean_dec(v_snd_470_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_514_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_506_ = l_Lean_Name_toString(v_v_501_, v___x_474_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 3);
lean_ctor_set(v___x_503_, 0, v___x_506_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_513_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_508_);
lean_ctor_set(v___x_467_, 0, v___x_505_);
v___x_510_ = v___x_467_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_479_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
return v___x_511_;
}
}
}
}
case 3:
{
lean_object* v_v_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_526_; 
v_v_515_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_526_ == 0)
{
v___x_517_ = v_snd_470_;
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_v_515_);
lean_dec(v_snd_470_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Nat_reprFast(v_v_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_521_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_523_ = v___x_467_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
case 4:
{
lean_object* v_v_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_554_; 
v_v_527_ = lean_ctor_get(v_snd_470_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_snd_470_);
if (v_isSharedCheck_554_ == 0)
{
v___x_529_ = v_snd_470_;
v_isShared_530_ = v_isSharedCheck_554_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_v_527_);
lean_dec(v_snd_470_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_554_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_intZero_531_; uint8_t v_isNeg_532_; 
v_intZero_531_ = lean_obj_once(&l_Lean_instToFormatDataValue___lam__0___closed__6, &l_Lean_instToFormatDataValue___lam__0___closed__6_once, _init_l_Lean_instToFormatDataValue___lam__0___closed__6);
v_isNeg_532_ = lean_int_dec_lt(v_v_527_, v_intZero_531_);
if (v_isNeg_532_ == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v_a_533_ = lean_nat_abs(v_v_527_);
lean_dec(v_v_527_);
v___x_534_ = l_Nat_reprFast(v_a_533_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 3);
lean_ctor_set(v___x_529_, 0, v___x_534_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_536_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_538_ = v___x_467_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v_abs_541_; lean_object* v_one_542_; lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v_abs_541_ = lean_nat_abs(v_v_527_);
lean_dec(v_v_527_);
v_one_542_ = lean_unsigned_to_nat(1u);
v_a_543_ = lean_nat_sub(v_abs_541_, v_one_542_);
lean_dec(v_abs_541_);
v___x_544_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__7));
v___x_545_ = lean_nat_add(v_a_543_, v_one_542_);
lean_dec(v_a_543_);
v___x_546_ = l_Nat_reprFast(v___x_545_);
v___x_547_ = lean_string_append(v___x_544_, v___x_546_);
lean_dec_ref(v___x_546_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 3);
lean_ctor_set(v___x_529_, 0, v___x_547_);
v___x_549_ = v___x_529_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_553_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_549_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_551_ = v___x_467_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
default: 
{
lean_object* v_v_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v_v_555_ = lean_ctor_get(v_snd_470_, 0);
lean_inc(v_v_555_);
lean_dec_ref(v_snd_470_);
v___x_556_ = lean_box(0);
v___x_557_ = 0;
v___x_558_ = l_Lean_Syntax_formatStx(v_v_555_, v___x_556_, v___x_557_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v___x_558_);
lean_ctor_set(v___x_467_, 0, v___x_479_);
v___x_560_ = v___x_467_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
}
else
{
lean_object* v_head_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_673_; 
lean_inc(v_tail_464_);
v_head_566_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_x_461_, 1);
lean_dec(v_unused_674_);
v___x_568_ = v_x_461_;
v_isShared_569_ = v_isSharedCheck_673_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_head_566_);
lean_dec(v_x_461_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_673_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_672_; 
v_fst_570_ = lean_ctor_get(v_head_566_, 0);
v_snd_571_ = lean_ctor_get(v_head_566_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_head_566_);
if (v_isSharedCheck_672_ == 0)
{
v___x_573_ = v_head_566_;
v_isShared_574_ = v_isSharedCheck_672_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_head_566_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_672_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_575_ = 1;
v___x_576_ = l_Lean_Name_toString(v_fst_570_, v___x_575_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 5);
lean_ctor_set(v___x_573_, 1, v___x_578_);
lean_ctor_set(v___x_573_, 0, v___x_577_);
v___x_580_ = v___x_573_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_671_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
switch(lean_obj_tag(v_snd_571_))
{
case 0:
{
lean_object* v_v_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_593_; 
v_v_581_ = lean_ctor_get(v_snd_571_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_593_ == 0)
{
v___x_583_ = v_snd_571_;
v_isShared_584_ = v_isSharedCheck_593_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_v_581_);
lean_dec(v_snd_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_593_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l_String_quote(v_v_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 3);
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_592_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_587_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_589_ = v___x_568_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_589_, v_tail_464_);
return v___x_590_;
}
}
}
}
case 1:
{
uint8_t v_v_594_; 
v_v_594_ = lean_ctor_get_uint8(v_snd_571_, 0);
lean_dec_ref(v_snd_571_);
if (v_v_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_595_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_597_ = v___x_568_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_597_, v_tail_464_);
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_600_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_602_ = v___x_568_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_602_, v_tail_464_);
return v___x_603_;
}
}
}
case 2:
{
lean_object* v_v_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_v_605_ = lean_ctor_get(v_snd_571_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_619_ == 0)
{
v___x_607_ = v_snd_571_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_v_605_);
lean_dec(v_snd_571_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_610_ = l_Lean_Name_toString(v_v_605_, v___x_575_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 3);
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_618_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_612_);
lean_ctor_set(v___x_568_, 0, v___x_609_);
v___x_614_ = v___x_568_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_580_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_615_, v_tail_464_);
return v___x_616_;
}
}
}
}
case 3:
{
lean_object* v_v_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_632_; 
v_v_620_ = lean_ctor_get(v_snd_571_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_632_ == 0)
{
v___x_622_ = v_snd_571_;
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_v_620_);
lean_dec(v_snd_571_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_632_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = l_Nat_reprFast(v_v_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_631_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_626_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_628_ = v___x_568_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_628_, v_tail_464_);
return v___x_629_;
}
}
}
}
case 4:
{
lean_object* v_v_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_662_; 
v_v_633_ = lean_ctor_get(v_snd_571_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_662_ == 0)
{
v___x_635_ = v_snd_571_;
v_isShared_636_ = v_isSharedCheck_662_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_v_633_);
lean_dec(v_snd_571_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_662_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_intZero_637_; uint8_t v_isNeg_638_; 
v_intZero_637_ = lean_obj_once(&l_Lean_instToFormatDataValue___lam__0___closed__6, &l_Lean_instToFormatDataValue___lam__0___closed__6_once, _init_l_Lean_instToFormatDataValue___lam__0___closed__6);
v_isNeg_638_ = lean_int_dec_lt(v_v_633_, v_intZero_637_);
if (v_isNeg_638_ == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v_a_639_ = lean_nat_abs(v_v_633_);
lean_dec(v_v_633_);
v___x_640_ = l_Nat_reprFast(v_a_639_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 3);
lean_ctor_set(v___x_635_, 0, v___x_640_);
v___x_642_ = v___x_635_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_647_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_642_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_644_ = v___x_568_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_644_, v_tail_464_);
return v___x_645_;
}
}
}
else
{
lean_object* v_abs_648_; lean_object* v_one_649_; lean_object* v_a_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v_abs_648_ = lean_nat_abs(v_v_633_);
lean_dec(v_v_633_);
v_one_649_ = lean_unsigned_to_nat(1u);
v_a_650_ = lean_nat_sub(v_abs_648_, v_one_649_);
lean_dec(v_abs_648_);
v___x_651_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__7));
v___x_652_ = lean_nat_add(v_a_650_, v_one_649_);
lean_dec(v_a_650_);
v___x_653_ = l_Nat_reprFast(v___x_652_);
v___x_654_ = lean_string_append(v___x_651_, v___x_653_);
lean_dec_ref(v___x_653_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 3);
lean_ctor_set(v___x_635_, 0, v___x_654_);
v___x_656_ = v___x_635_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_661_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_656_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_658_ = v___x_568_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_658_, v_tail_464_);
return v___x_659_;
}
}
}
}
}
default: 
{
lean_object* v_v_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v_v_663_ = lean_ctor_get(v_snd_571_, 0);
lean_inc(v_v_663_);
lean_dec_ref(v_snd_571_);
v___x_664_ = lean_box(0);
v___x_665_ = 0;
v___x_666_ = l_Lean_Syntax_formatStx(v_v_663_, v___x_664_, v___x_665_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v___x_666_);
lean_ctor_set(v___x_568_, 0, v___x_580_);
v___x_668_ = v___x_568_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_670_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; 
v___x_669_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_462_, v___x_668_, v_tail_464_);
return v___x_669_;
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
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_formatKVMap___closed__2));
v___x_681_ = lean_string_length(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__5(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_formatKVMap___closed__4, &l_Lean_formatKVMap___closed__4_once, _init_l_Lean_formatKVMap___closed__4);
v___x_683_ = lean_nat_to_int(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* v_m_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_689_ = ((lean_object*)(l_Lean_formatKVMap___closed__1));
v___x_690_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_688_, v___x_689_);
v___x_691_ = lean_obj_once(&l_Lean_formatKVMap___closed__5, &l_Lean_formatKVMap___closed__5_once, _init_l_Lean_formatKVMap___closed__5);
v___x_692_ = ((lean_object*)(l_Lean_formatKVMap___closed__6));
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_690_);
v___x_694_ = ((lean_object*)(l_Lean_formatKVMap___closed__7));
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = 0;
v___x_698_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v___x_697_);
return v___x_698_;
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
res = l_Std_Format_initFn_00___x40_Lean_Data_Format_3484694372____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_width = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_width);
lean_dec_ref(res);
res = l_Std_Format_initFn_00___x40_Lean_Data_Format_2495473732____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_unicode = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_unicode);
lean_dec_ref(res);
res = l_Std_Format_initFn_00___x40_Lean_Data_Format_1056614795____hygCtx___hyg_4_();
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
