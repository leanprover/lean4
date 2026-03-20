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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defIndent;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__0(lean_object* v_x_202_){
_start:
{
switch(lean_obj_tag(v_x_202_))
{
case 0:
{
lean_object* v_v_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_v_203_ = lean_ctor_get(v_x_202_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v_x_202_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_v_203_);
lean_dec(v_x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = l_String_quote(v_v_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 3);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
case 1:
{
uint8_t v_v_212_; 
v_v_212_ = lean_ctor_get_uint8(v_x_202_, 0);
lean_dec_ref(v_x_202_);
if (v_v_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
return v___x_214_;
}
}
case 2:
{
lean_object* v_v_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_226_; 
v_v_215_ = lean_ctor_get(v_x_202_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_226_ == 0)
{
v___x_217_ = v_x_202_;
v_isShared_218_ = v_isSharedCheck_226_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_v_215_);
lean_dec(v_x_202_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_226_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_219_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_220_ = 1;
v___x_221_ = l_Lean_Name_toString(v_v_215_, v___x_220_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 3);
lean_ctor_set(v___x_217_, 0, v___x_221_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
}
case 3:
{
lean_object* v_v_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_235_; 
v_v_227_ = lean_ctor_get(v_x_202_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_235_ == 0)
{
v___x_229_ = v_x_202_;
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_v_227_);
lean_dec(v_x_202_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = l_Nat_reprFast(v_v_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_231_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
case 4:
{
lean_object* v_v_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_v_236_ = lean_ctor_get(v_x_202_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v_x_202_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_v_236_);
lean_dec(v_x_202_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = l_Int_repr(v_v_236_);
lean_dec(v_v_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 3);
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
default: 
{
lean_object* v_v_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v_v_245_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_v_245_);
lean_dec_ref(v_x_202_);
v___x_246_ = lean_box(0);
v___x_247_ = 0;
v___x_248_ = l_Lean_Syntax_formatStx(v_v_245_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__0(lean_object* v_x_254_){
_start:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_319_; 
v_fst_255_ = lean_ctor_get(v_x_254_, 0);
v_snd_256_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_319_ == 0)
{
v___x_258_ = v_x_254_;
v_isShared_259_ = v_isSharedCheck_319_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snd_256_);
lean_inc(v_fst_255_);
lean_dec(v_x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_319_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_260_ = 1;
v___x_261_ = l_Lean_Name_toString(v_fst_255_, v___x_260_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 5);
lean_ctor_set(v___x_258_, 1, v___x_263_);
lean_ctor_set(v___x_258_, 0, v___x_262_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_318_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
switch(lean_obj_tag(v_snd_256_))
{
case 0:
{
lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_275_; 
v_v_266_ = lean_ctor_get(v_snd_256_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_snd_256_);
if (v_isSharedCheck_275_ == 0)
{
v___x_268_ = v_snd_256_;
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_v_266_);
lean_dec(v_snd_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_String_quote(v_v_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 3);
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_265_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
}
case 1:
{
uint8_t v_v_276_; 
v_v_276_ = lean_ctor_get_uint8(v_snd_256_, 0);
lean_dec_ref(v_snd_256_);
if (v_v_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_265_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_265_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
return v___x_280_;
}
}
case 2:
{
lean_object* v_v_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_292_; 
v_v_281_ = lean_ctor_get(v_snd_256_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_snd_256_);
if (v_isSharedCheck_292_ == 0)
{
v___x_283_ = v_snd_256_;
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_v_281_);
lean_dec(v_snd_256_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_286_ = l_Lean_Name_toString(v_v_281_, v___x_260_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 3);
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_291_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_285_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_265_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
}
}
case 3:
{
lean_object* v_v_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_302_; 
v_v_293_ = lean_ctor_get(v_snd_256_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_snd_256_);
if (v_isSharedCheck_302_ == 0)
{
v___x_295_ = v_snd_256_;
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_v_293_);
lean_dec(v_snd_256_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = l_Nat_reprFast(v_v_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_301_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_265_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
}
}
case 4:
{
lean_object* v_v_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_312_; 
v_v_303_ = lean_ctor_get(v_snd_256_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_snd_256_);
if (v_isSharedCheck_312_ == 0)
{
v___x_305_ = v_snd_256_;
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_v_303_);
lean_dec(v_snd_256_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = l_Int_repr(v_v_303_);
lean_dec(v_v_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 3);
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_311_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_265_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
}
}
default: 
{
lean_object* v_v_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_v_313_ = lean_ctor_get(v_snd_256_, 0);
lean_inc(v_v_313_);
lean_dec_ref(v_snd_256_);
v___x_314_ = lean_box(0);
v___x_315_ = 0;
v___x_316_ = l_Lean_Syntax_formatStx(v_v_313_, v___x_314_, v___x_315_);
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_265_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_formatKVMap_spec__1(lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_nat_to_int(v_a_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_dec(v_x_324_);
return v_x_325_;
}
else
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_414_; 
v_head_327_ = lean_ctor_get(v_x_326_, 0);
v_tail_328_ = lean_ctor_get(v_x_326_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_414_ == 0)
{
v___x_330_ = v_x_326_;
v_isShared_331_ = v_isSharedCheck_414_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_head_327_);
lean_dec(v_x_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_414_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_413_; 
v_fst_332_ = lean_ctor_get(v_head_327_, 0);
v_snd_333_ = lean_ctor_get(v_head_327_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_head_327_);
if (v_isSharedCheck_413_ == 0)
{
v___x_335_ = v_head_327_;
v_isShared_336_ = v_isSharedCheck_413_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snd_333_);
lean_inc(v_fst_332_);
lean_dec(v_head_327_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_413_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
lean_inc(v_x_324_);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 5);
lean_ctor_set(v___x_335_, 1, v_x_324_);
lean_ctor_set(v___x_335_, 0, v_x_325_);
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_x_325_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_x_324_);
v___x_338_ = v_reuseFailAlloc_412_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_339_ = 1;
v___x_340_ = l_Lean_Name_toString(v_fst_332_, v___x_339_);
v___x_341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 5);
lean_ctor_set(v___x_330_, 1, v___x_342_);
lean_ctor_set(v___x_330_, 0, v___x_341_);
v___x_344_ = v___x_330_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_411_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
switch(lean_obj_tag(v_snd_333_))
{
case 0:
{
lean_object* v_v_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_356_; 
v_v_345_ = lean_ctor_get(v_snd_333_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_snd_333_);
if (v_isSharedCheck_356_ == 0)
{
v___x_347_ = v_snd_333_;
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_v_345_);
lean_dec(v_snd_333_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_String_quote(v_v_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 3);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_344_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_338_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v_x_325_ = v___x_353_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
}
case 1:
{
uint8_t v_v_357_; 
v_v_357_ = lean_ctor_get_uint8(v_snd_333_, 0);
lean_dec_ref(v_snd_333_);
if (v_v_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_344_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_338_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v_x_325_ = v___x_360_;
v_x_326_ = v_tail_328_;
goto _start;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_344_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_338_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v_x_325_ = v___x_364_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
case 2:
{
lean_object* v_v_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_379_; 
v_v_366_ = lean_ctor_get(v_snd_333_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_snd_333_);
if (v_isSharedCheck_379_ == 0)
{
v___x_368_ = v_snd_333_;
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_v_366_);
lean_dec(v_snd_333_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_371_ = l_Lean_Name_toString(v_v_366_, v___x_339_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 3);
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_378_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_370_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_344_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_338_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v_x_325_ = v___x_376_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
}
case 3:
{
lean_object* v_v_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_391_; 
v_v_380_ = lean_ctor_get(v_snd_333_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_snd_333_);
if (v_isSharedCheck_391_ == 0)
{
v___x_382_ = v_snd_333_;
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_v_380_);
lean_dec(v_snd_333_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = l_Nat_reprFast(v_v_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_344_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_338_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v_x_325_ = v___x_388_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
}
case 4:
{
lean_object* v_v_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_403_; 
v_v_392_ = lean_ctor_get(v_snd_333_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_snd_333_);
if (v_isSharedCheck_403_ == 0)
{
v___x_394_ = v_snd_333_;
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_v_392_);
lean_dec(v_snd_333_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = l_Int_repr(v_v_392_);
lean_dec(v_v_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 3);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_402_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_344_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_338_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v_x_325_ = v___x_400_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
}
default: 
{
lean_object* v_v_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_v_404_ = lean_ctor_get(v_snd_333_, 0);
lean_inc(v_v_404_);
lean_dec_ref(v_snd_333_);
v___x_405_ = lean_box(0);
v___x_406_ = 0;
v___x_407_ = l_Lean_Syntax_formatStx(v_v_404_, v___x_405_, v___x_406_);
v___x_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_344_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_338_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v_x_325_ = v___x_409_;
v_x_326_ = v_tail_328_;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_417_; 
lean_dec(v_x_416_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v_tail_418_; 
v_tail_418_ = lean_ctor_get(v_x_415_, 1);
if (lean_obj_tag(v_tail_418_) == 0)
{
lean_object* v_head_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_x_416_);
v_head_419_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_x_415_, 1);
lean_dec(v_unused_503_);
v___x_421_ = v_x_415_;
v_isShared_422_ = v_isSharedCheck_502_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_head_419_);
lean_dec(v_x_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_502_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_501_; 
v_fst_423_ = lean_ctor_get(v_head_419_, 0);
v_snd_424_ = lean_ctor_get(v_head_419_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_head_419_);
if (v_isSharedCheck_501_ == 0)
{
v___x_426_ = v_head_419_;
v_isShared_427_ = v_isSharedCheck_501_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_inc(v_fst_423_);
lean_dec(v_head_419_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_501_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_428_ = 1;
v___x_429_ = l_Lean_Name_toString(v_fst_423_, v___x_428_);
v___x_430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
v___x_431_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 5);
lean_ctor_set(v___x_426_, 1, v___x_431_);
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_433_ = v___x_426_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_500_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
switch(lean_obj_tag(v_snd_424_))
{
case 0:
{
lean_object* v_v_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v_v_434_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v_snd_424_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_v_434_);
lean_dec(v_snd_424_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_String_quote(v_v_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 3);
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_440_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_442_ = v___x_421_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
case 1:
{
uint8_t v_v_446_; 
v_v_446_ = lean_ctor_get_uint8(v_snd_424_, 0);
lean_dec_ref(v_snd_424_);
if (v_v_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_447_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_449_ = v___x_421_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_451_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_453_ = v___x_421_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
case 2:
{
lean_object* v_v_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_468_; 
v_v_455_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_468_ == 0)
{
v___x_457_ = v_snd_424_;
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_v_455_);
lean_dec(v_snd_424_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_460_ = l_Lean_Name_toString(v_v_455_, v___x_428_);
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 3);
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_462_);
lean_ctor_set(v___x_421_, 0, v___x_459_);
v___x_464_ = v___x_421_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_433_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
}
}
case 3:
{
lean_object* v_v_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_480_; 
v_v_469_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_480_ == 0)
{
v___x_471_ = v_snd_424_;
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_v_469_);
lean_dec(v_snd_424_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = l_Nat_reprFast(v_v_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_475_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_477_ = v___x_421_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
case 4:
{
lean_object* v_v_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_492_; 
v_v_481_ = lean_ctor_get(v_snd_424_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_snd_424_);
if (v_isSharedCheck_492_ == 0)
{
v___x_483_ = v_snd_424_;
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_v_481_);
lean_dec(v_snd_424_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Int_repr(v_v_481_);
lean_dec(v_v_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 3);
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_487_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_489_ = v___x_421_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
default: 
{
lean_object* v_v_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v_v_493_ = lean_ctor_get(v_snd_424_, 0);
lean_inc(v_v_493_);
lean_dec_ref(v_snd_424_);
v___x_494_ = lean_box(0);
v___x_495_ = 0;
v___x_496_ = l_Lean_Syntax_formatStx(v_v_493_, v___x_494_, v___x_495_);
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 5);
lean_ctor_set(v___x_421_, 1, v___x_496_);
lean_ctor_set(v___x_421_, 0, v___x_433_);
v___x_498_ = v___x_421_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
}
else
{
lean_object* v_head_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_594_; 
lean_inc(v_tail_418_);
v_head_504_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_x_415_, 1);
lean_dec(v_unused_595_);
v___x_506_ = v_x_415_;
v_isShared_507_ = v_isSharedCheck_594_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_head_504_);
lean_dec(v_x_415_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_594_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_593_; 
v_fst_508_ = lean_ctor_get(v_head_504_, 0);
v_snd_509_ = lean_ctor_get(v_head_504_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_head_504_);
if (v_isSharedCheck_593_ == 0)
{
v___x_511_ = v_head_504_;
v_isShared_512_ = v_isSharedCheck_593_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_inc(v_fst_508_);
lean_dec(v_head_504_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_593_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_513_ = 1;
v___x_514_ = l_Lean_Name_toString(v_fst_508_, v___x_513_);
v___x_515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_instToFormatProdNameDataValue___lam__0___closed__1));
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 5);
lean_ctor_set(v___x_511_, 1, v___x_516_);
lean_ctor_set(v___x_511_, 0, v___x_515_);
v___x_518_ = v___x_511_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_592_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
switch(lean_obj_tag(v_snd_509_))
{
case 0:
{
lean_object* v_v_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_v_519_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_snd_509_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_v_519_);
lean_dec(v_snd_509_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_String_quote(v_v_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 3);
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_525_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_527_ = v___x_506_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_527_, v_tail_418_);
return v___x_528_;
}
}
}
}
case 1:
{
uint8_t v_v_532_; 
v_v_532_ = lean_ctor_get_uint8(v_snd_509_, 0);
lean_dec_ref(v_snd_509_);
if (v_v_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__1));
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_533_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_535_ = v___x_506_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_535_, v_tail_418_);
return v___x_536_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__3));
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_538_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_540_ = v___x_506_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_540_, v_tail_418_);
return v___x_541_;
}
}
}
case 2:
{
lean_object* v_v_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_557_; 
v_v_543_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_557_ == 0)
{
v___x_545_ = v_snd_509_;
v_isShared_546_ = v_isSharedCheck_557_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_v_543_);
lean_dec(v_snd_509_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_557_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = ((lean_object*)(l_Lean_instToFormatDataValue___lam__0___closed__5));
v___x_548_ = l_Lean_Name_toString(v_v_543_, v___x_513_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 3);
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_556_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_550_);
lean_ctor_set(v___x_506_, 0, v___x_547_);
v___x_552_ = v___x_506_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_518_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_553_, v_tail_418_);
return v___x_554_;
}
}
}
}
case 3:
{
lean_object* v_v_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v_v_558_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v_snd_509_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_v_558_);
lean_dec(v_snd_509_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = l_Nat_reprFast(v_v_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_564_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_566_ = v___x_506_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_566_, v_tail_418_);
return v___x_567_;
}
}
}
}
case 4:
{
lean_object* v_v_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_583_; 
v_v_571_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_583_ == 0)
{
v___x_573_ = v_snd_509_;
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_v_571_);
lean_dec(v_snd_509_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = l_Int_repr(v_v_571_);
lean_dec(v_v_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 3);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_582_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_577_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_579_ = v___x_506_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_577_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_579_, v_tail_418_);
return v___x_580_;
}
}
}
}
default: 
{
lean_object* v_v_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_v_584_ = lean_ctor_get(v_snd_509_, 0);
lean_inc(v_v_584_);
lean_dec_ref(v_snd_509_);
v___x_585_ = lean_box(0);
v___x_586_ = 0;
v___x_587_ = l_Lean_Syntax_formatStx(v_v_584_, v___x_585_, v___x_586_);
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 5);
lean_ctor_set(v___x_506_, 1, v___x_587_);
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_589_ = v___x_506_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_formatKVMap_spec__0_spec__0(v_x_416_, v___x_589_, v_tail_418_);
return v___x_590_;
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
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_formatKVMap___closed__2));
v___x_602_ = lean_string_length(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_formatKVMap___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_formatKVMap___closed__4, &l_Lean_formatKVMap___closed__4_once, _init_l_Lean_formatKVMap___closed__4);
v___x_604_ = lean_nat_to_int(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* v_m_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; 
v___x_610_ = ((lean_object*)(l_Lean_formatKVMap___closed__1));
v___x_611_ = l_Std_Format_joinSep___at___00Lean_formatKVMap_spec__0(v_m_609_, v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_formatKVMap___closed__5, &l_Lean_formatKVMap___closed__5_once, _init_l_Lean_formatKVMap___closed__5);
v___x_613_ = ((lean_object*)(l_Lean_formatKVMap___closed__6));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_611_);
v___x_615_ = ((lean_object*)(l_Lean_formatKVMap___closed__7));
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_612_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = 0;
v___x_619_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*1, v___x_618_);
return v___x_619_;
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
