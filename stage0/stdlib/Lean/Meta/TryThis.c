// Lean compiler output
// Module: Lean.Meta.TryThis
// Imports: public import Lean.Data.Lsp.Basic public import Lean.PrettyPrinter
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
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_maximum(double, double);
double lean_float_minimum(double, double);
double lean_float_mul(double, double);
double round(double);
lean_object* lean_float_to_string(double);
lean_object* lean_string_append(lean_object*, lean_object*);
double lean_float_sub(double, double);
double pow(double, double);
double lean_float_add(double, double);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "className"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pointer dim"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "style"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "color"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "var(--vscode-errorForeground)"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "textDecoration"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "underline wavy var(--vscode-editorError-foreground) 1pt"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "gold pointer dim"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "underline wavy var(--vscode-editorWarning-foreground) 1pt"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "information pointer dim"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "goal-hyp pointer dim"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "goal-inaccessible pointer dim"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hsl("};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " 95% "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "%)"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Apply suggestion"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Apply suggestion ("};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TryThis"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "TryThisInfo"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 55, 191, 109, 224, 169, 145, 115)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(89, 112, 140, 127, 159, 194, 21, 171)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inputWidth"};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 147, 146, 63, 150, 233, 253, 32)}};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ideal input width"};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 55, 191, 109, 224, 169, 145, 115)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 10, 29, 165, 121, 220, 111, 19)}};
static const lean_ctor_object l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(16, 85, 191, 240, 102, 91, 59, 55)}};
static const lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_format_inputWidth;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_kind_7_; lean_object* v_a_8_; lean_object* v___x_9_; 
v_kind_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_kind_7_);
v_a_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_kind_7_, v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_10_);
lean_dec_ref_known(v_t_5_, 1);
v___x_11_ = lean_apply_1(v_k_6_, v_a_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim___redArg(lean_object* v_t_24_, lean_object* v_tsyntax_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_24_, v_tsyntax_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_tsyntax_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_28_, v_tsyntax_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim___redArg(lean_object* v_t_32_, lean_object* v_string_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_32_, v_string_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_string_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_36_, v_string_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_47_; 
v_a_46_ = lean_ctor_get(v_x_45_, 1);
lean_inc(v_a_46_);
lean_dec_ref_known(v_x_45_, 2);
v___x_47_ = l_Lean_MessageData_ofSyntax(v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_a_48_ = lean_ctor_get(v_x_45_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v_x_45_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v_x_45_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 3);
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_55_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_MessageData_ofFormat(v___x_53_);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(lean_object* v_kind_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_kind_59_);
lean_ctor_set(v___x_61_, 1, v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object* v_kind_62_){
_start:
{
lean_object* v___f_63_; 
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0), 2, 1);
lean_closure_set(v___f_63_, 0, v_kind_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_a_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1(lean_object* v_a_70_){
_start:
{
lean_inc(v_a_70_);
return v_a_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1(v_a_71_);
lean_dec(v_a_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0(lean_object* v___y_73_){
_start:
{
lean_inc(v___y_73_);
return v___y_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0___boxed(lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0(v___y_74_);
lean_dec(v___y_74_);
return v_res_75_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9));
v___x_97_ = l_Lean_Json_mkObj(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16));
v___x_112_ = l_Lean_Json_mkObj(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t v_decorated_113_){
_start:
{
lean_object* v___y_115_; 
if (v_decorated_113_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10);
v___y_115_ = v___x_123_;
goto v___jp_114_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17);
v___y_115_ = v___x_124_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3));
v___x_117_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
lean_inc(v___y_115_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_115_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_Json_mkObj(v___x_121_);
lean_dec_ref_known(v___x_121_, 2);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object* v_decorated_125_){
_start:
{
uint8_t v_decorated_boxed_126_; lean_object* v_res_127_; 
v_decorated_boxed_126_ = lean_unbox(v_decorated_125_);
v_res_127_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(v_decorated_boxed_126_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3));
v___x_138_ = l_Lean_Json_mkObj(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8));
v___x_149_ = l_Lean_Json_mkObj(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9);
v___x_151_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_box(0);
v___x_154_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2));
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12);
v___x_160_ = l_Lean_Json_mkObj(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t v_decorated_161_){
_start:
{
if (v_decorated_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object* v_decorated_164_){
_start:
{
uint8_t v_decorated_boxed_165_; lean_object* v_res_166_; 
v_decorated_boxed_165_ = lean_unbox(v_decorated_164_);
v_res_166_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(v_decorated_boxed_165_);
return v_res_166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3));
v___x_177_ = l_Lean_Json_mkObj(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3));
v___x_189_ = l_Lean_Json_mkObj(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3));
v___x_201_ = l_Lean_Json_mkObj(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4);
return v___x_202_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0(void){
_start:
{
lean_object* v___x_203_; double v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_float_of_nat(v___x_203_);
return v___x_204_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1(void){
_start:
{
lean_object* v___x_205_; double v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_float_of_nat(v___x_205_);
return v___x_206_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3(void){
_start:
{
lean_object* v___x_208_; double v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(120u);
v___x_209_ = lean_float_of_nat(v___x_208_);
return v___x_209_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5(void){
_start:
{
lean_object* v___x_211_; double v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(60u);
v___x_212_ = lean_float_of_nat(v___x_211_);
return v___x_212_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6(void){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; double v___x_216_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = 1;
v___x_215_ = lean_unsigned_to_nat(5u);
v___x_216_ = l_Float_ofScientific(v___x_215_, v___x_214_, v___x_213_);
return v___x_216_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7(void){
_start:
{
lean_object* v___x_217_; double v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(2u);
v___x_218_ = lean_float_of_nat(v___x_217_);
return v___x_218_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8(void){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; double v___x_222_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = 1;
v___x_221_ = lean_unsigned_to_nat(75u);
v___x_222_ = l_Float_ofScientific(v___x_221_, v___x_220_, v___x_219_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double v_t_228_, uint8_t v_showValueInHoverText_229_){
_start:
{
double v___x_230_; double v___x_231_; double v___x_232_; double v_t_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; double v___x_238_; double v___x_239_; double v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; double v___x_245_; double v___x_246_; double v___x_247_; double v___x_248_; double v___x_249_; double v___x_250_; double v___x_251_; double v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___y_265_; 
v___x_230_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0);
v___x_231_ = lean_float_maximum(v_t_228_, v___x_230_);
v___x_232_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1);
v_t_233_ = lean_float_minimum(v___x_231_, v___x_232_);
v___x_234_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3));
v___x_235_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_236_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5));
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2));
v___x_238_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3);
v___x_239_ = lean_float_mul(v_t_233_, v___x_238_);
v___x_240_ = round(v___x_239_);
v___x_241_ = lean_float_to_string(v___x_240_);
v___x_242_ = lean_string_append(v___x_237_, v___x_241_);
lean_dec_ref(v___x_241_);
v___x_243_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4));
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
v___x_245_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5);
v___x_246_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6);
v___x_247_ = lean_float_sub(v_t_233_, v___x_246_);
v___x_248_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7);
v___x_249_ = pow(v___x_247_, v___x_248_);
v___x_250_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8);
v___x_251_ = lean_float_add(v___x_249_, v___x_250_);
v___x_252_ = lean_float_mul(v___x_245_, v___x_251_);
v___x_253_ = lean_float_to_string(v___x_252_);
v___x_254_ = lean_string_append(v___x_244_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9));
v___x_256_ = lean_string_append(v___x_254_, v___x_255_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_236_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = l_Lean_Json_mkObj(v___x_260_);
lean_dec_ref_known(v___x_260_, 2);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_235_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10));
if (v_showValueInHoverText_229_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11));
v___y_265_ = v___x_272_;
goto v___jp_264_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12));
v___x_274_ = lean_float_to_string(v_t_233_);
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
lean_dec_ref(v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___y_265_ = v___x_277_;
goto v___jp_264_;
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___y_265_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_263_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_259_);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_262_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_234_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_Json_mkObj(v___x_270_);
lean_dec_ref_known(v___x_270_, 2);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object* v_t_278_, lean_object* v_showValueInHoverText_279_){
_start:
{
double v_t_boxed_280_; uint8_t v_showValueInHoverText_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_280_ = lean_unbox_float(v_t_278_);
lean_dec_ref(v_t_278_);
v_showValueInHoverText_boxed_281_ = lean_unbox(v_showValueInHoverText_279_);
v_res_282_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(v_t_boxed_280_, v_showValueInHoverText_boxed_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object* v_s_288_){
_start:
{
lean_object* v_messageData_x3f_289_; 
v_messageData_x3f_289_ = lean_ctor_get(v_s_288_, 4);
if (lean_obj_tag(v_messageData_x3f_289_) == 0)
{
lean_object* v_suggestion_290_; 
v_suggestion_290_ = lean_ctor_get(v_s_288_, 0);
lean_inc_ref(v_suggestion_290_);
lean_dec_ref(v_s_288_);
if (lean_obj_tag(v_suggestion_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v_suggestion_290_, 1);
lean_inc(v_a_291_);
lean_dec_ref_known(v_suggestion_290_, 2);
v___x_292_ = l_Lean_MessageData_ofSyntax(v_a_291_);
return v___x_292_;
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v_suggestion_290_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_suggestion_290_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v_suggestion_290_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v_suggestion_290_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 3);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_MessageData_ofFormat(v___x_298_);
return v___x_299_;
}
}
}
}
else
{
lean_object* v_val_302_; 
lean_inc_ref(v_messageData_x3f_289_);
lean_dec_ref(v_s_288_);
v_val_302_ = lean_ctor_get(v_messageData_x3f_289_, 0);
lean_inc(v_val_302_);
lean_dec_ref_known(v_messageData_x3f_289_, 1);
return v_val_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_307_, 0, v_t_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_ctor_set(v___x_307_, 2, v___x_306_);
lean_ctor_set(v___x_307_, 3, v___x_306_);
lean_ctor_set(v___x_307_, 4, v___x_306_);
lean_ctor_set(v___x_307_, 5, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(lean_object* v_s_323_, lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
lean_object* v___x_326_; uint8_t v_decide_327_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v_decide_327_ = lean_nat_dec_eq(v_a_324_, v___x_326_);
if (v_decide_327_ == 0)
{
lean_object* v_str_328_; lean_object* v_startInclusive_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint32_t v___x_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v_str_328_ = lean_ctor_get(v_s_323_, 0);
v_startInclusive_329_ = lean_ctor_get(v_s_323_, 1);
v___x_330_ = lean_nat_add(v_startInclusive_329_, v_a_324_);
lean_inc(v___x_330_);
lean_inc(v_startInclusive_329_);
lean_inc_ref(v_str_328_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v_str_328_);
lean_ctor_set(v___x_331_, 1, v_startInclusive_329_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
v___x_332_ = lean_nat_sub(v___x_330_, v_startInclusive_329_);
lean_dec(v___x_330_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_sub(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
v___x_335_ = l_String_Slice_posLE(v___x_331_, v___x_334_);
lean_dec_ref_known(v___x_331_, 3);
v___x_336_ = lean_nat_add(v_startInclusive_329_, v___x_335_);
v___x_337_ = lean_string_utf8_get_fast(v_str_328_, v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = 10;
v___x_339_ = lean_uint32_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v___x_335_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_nat_sub(v_a_324_, v___x_333_);
lean_dec(v_a_324_);
v___x_342_ = l_String_Slice_posLE(v_s_323_, v___x_341_);
v_a_324_ = v___x_342_;
v_b_325_ = v___x_340_;
goto _start;
}
else
{
lean_object* v___x_344_; 
lean_dec(v_a_324_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_335_);
return v___x_344_;
}
}
else
{
lean_dec(v_a_324_);
lean_inc(v_b_325_);
return v_b_325_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg___boxed(lean_object* v_s_345_, lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_345_, v_a_346_, v_b_347_);
lean_dec(v_b_347_);
lean_dec_ref(v_s_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(lean_object* v_s_349_){
_start:
{
lean_object* v_startInclusive_350_; lean_object* v_endExclusive_351_; lean_object* v_searcher_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_startInclusive_350_ = lean_ctor_get(v_s_349_, 1);
v_endExclusive_351_ = lean_ctor_get(v_s_349_, 2);
v_searcher_352_ = lean_nat_sub(v_endExclusive_351_, v_startInclusive_350_);
v___x_353_ = lean_box(0);
v___x_354_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_349_, v_searcher_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0___boxed(lean_object* v_s_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v_s_355_);
lean_dec_ref(v_s_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(lean_object* v_s_357_, lean_object* v_p_358_){
_start:
{
lean_object* v_val_360_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_357_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_s_357_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set(v___x_366_, 2, v_p_358_);
v___x_367_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v___x_366_);
lean_dec_ref_known(v___x_366_, 3);
if (lean_obj_tag(v___x_367_) == 0)
{
if (lean_obj_tag(v___x_367_) == 0)
{
lean_dec_ref(v_s_357_);
return v___x_365_;
}
else
{
lean_object* v_val_368_; 
v_val_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___x_367_, 1);
v_val_360_ = v_val_368_;
goto v___jp_359_;
}
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_367_, 1);
v_val_360_ = v_val_369_;
goto v___jp_359_;
}
v___jp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_string_utf8_byte_size(v_s_357_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v_s_357_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
v___x_364_ = l_String_Slice_Pos_next_x21(v___x_363_, v_val_360_);
lean_dec(v_val_360_);
lean_dec_ref_known(v___x_363_, 3);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(lean_object* v_s_370_, lean_object* v_inst_371_, lean_object* v_R_372_, lean_object* v_a_373_, lean_object* v_b_374_, lean_object* v_c_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_370_, v_a_373_, v_b_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___boxed(lean_object* v_s_377_, lean_object* v_inst_378_, lean_object* v_R_379_, lean_object* v_a_380_, lean_object* v_b_381_, lean_object* v_c_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(v_s_377_, v_inst_378_, v_R_379_, v_a_380_, v_b_381_, v_c_382_);
lean_dec(v_b_381_);
lean_dec_ref(v_s_377_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(lean_object* v___x_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
lean_object* v_str_387_; lean_object* v_startInclusive_388_; lean_object* v_endExclusive_389_; lean_object* v___x_390_; uint8_t v_decide_391_; 
v_str_387_ = lean_ctor_get(v___x_384_, 0);
v_startInclusive_388_ = lean_ctor_get(v___x_384_, 1);
v_endExclusive_389_ = lean_ctor_get(v___x_384_, 2);
v___x_390_ = lean_nat_sub(v_endExclusive_389_, v_startInclusive_388_);
v_decide_391_ = lean_nat_dec_eq(v_a_385_, v___x_390_);
lean_dec(v___x_390_);
if (v_decide_391_ == 0)
{
lean_object* v___x_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_392_ = lean_nat_add(v_startInclusive_388_, v_a_385_);
v___x_393_ = lean_string_utf8_get_fast(v_str_387_, v___x_392_);
v___x_394_ = 32;
v___x_395_ = lean_uint32_dec_eq(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec(v___x_392_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_a_385_);
return v___x_396_;
}
else
{
if (v_decide_391_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_a_385_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_string_utf8_next_fast(v_str_387_, v___x_392_);
lean_dec(v___x_392_);
v___x_399_ = lean_nat_sub(v___x_398_, v_startInclusive_388_);
v_a_385_ = v___x_399_;
v_b_386_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_401_; 
lean_dec(v___x_392_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v_a_385_);
return v___x_401_;
}
}
}
else
{
lean_dec(v_a_385_);
lean_inc(v_b_386_);
return v_b_386_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg___boxed(lean_object* v___x_402_, lean_object* v_a_403_, lean_object* v_b_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_402_, v_a_403_, v_b_404_);
lean_dec(v_b_404_);
lean_dec_ref(v___x_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object* v_map_406_, lean_object* v_range_407_){
_start:
{
lean_object* v_source_408_; lean_object* v_start_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_434_; 
v_source_408_ = lean_ctor_get(v_map_406_, 0);
lean_inc_ref(v_source_408_);
lean_dec_ref(v_map_406_);
v_start_409_ = lean_ctor_get(v_range_407_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_range_407_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_range_407_, 1);
lean_dec(v_unused_435_);
v___x_411_ = v_range_407_;
v_isShared_412_ = v_isSharedCheck_434_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_start_409_);
lean_dec(v_range_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_434_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_searcher_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_rangeStart_416_; lean_object* v_start_417_; lean_object* v___x_418_; lean_object* v___y_420_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_searcher_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_string_utf8_byte_size(v_source_408_);
lean_inc_ref_n(v_source_408_, 2);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v_source_408_);
lean_ctor_set(v___x_415_, 1, v_searcher_413_);
lean_ctor_set(v___x_415_, 2, v___x_414_);
v_rangeStart_416_ = l_String_Slice_pos_x21(v___x_415_, v_start_409_);
lean_dec_ref_known(v___x_415_, 3);
lean_inc(v_rangeStart_416_);
v_start_417_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(v_source_408_, v_rangeStart_416_);
v___x_418_ = l_String_slice_x21(v_source_408_, v_start_417_, v_rangeStart_416_);
lean_dec(v_rangeStart_416_);
v___x_428_ = lean_box(0);
v___x_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_418_, v_searcher_413_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_startInclusive_430_; lean_object* v_endExclusive_431_; lean_object* v___x_432_; 
v_startInclusive_430_ = lean_ctor_get(v___x_418_, 1);
v_endExclusive_431_ = lean_ctor_get(v___x_418_, 2);
v___x_432_ = lean_nat_sub(v_endExclusive_431_, v_startInclusive_430_);
v___y_420_ = v___x_432_;
goto v___jp_419_;
}
else
{
lean_object* v_val_433_; 
v_val_433_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_429_, 1);
v___y_420_ = v_val_433_;
goto v___jp_419_;
}
v___jp_419_:
{
lean_object* v_startInclusive_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_startInclusive_421_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_startInclusive_421_);
lean_dec_ref(v___x_418_);
v___x_422_ = lean_nat_add(v_startInclusive_421_, v___y_420_);
lean_dec(v___y_420_);
lean_dec(v_startInclusive_421_);
v___x_423_ = lean_nat_sub(v___x_422_, v_start_417_);
lean_dec(v___x_422_);
v___x_424_ = lean_nat_sub(v_start_409_, v_start_417_);
lean_dec(v_start_417_);
lean_dec(v_start_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_424_);
lean_ctor_set(v___x_411_, 0, v___x_423_);
v___x_426_ = v___x_411_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(lean_object* v___x_436_, lean_object* v_inst_437_, lean_object* v_R_438_, lean_object* v_a_439_, lean_object* v_b_440_, lean_object* v_c_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_436_, v_a_439_, v_b_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___boxed(lean_object* v___x_443_, lean_object* v_inst_444_, lean_object* v_R_445_, lean_object* v_a_446_, lean_object* v_b_447_, lean_object* v_c_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(v___x_443_, v_inst_444_, v_R_445_, v_a_446_, v_b_447_, v_c_448_);
lean_dec(v_b_447_);
lean_dec_ref(v___x_443_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(lean_object* v_name_450_, lean_object* v_decl_451_, lean_object* v_ref_452_){
_start:
{
lean_object* v_defValue_454_; lean_object* v_descr_455_; lean_object* v_deprecation_x3f_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_defValue_454_ = lean_ctor_get(v_decl_451_, 0);
v_descr_455_ = lean_ctor_get(v_decl_451_, 1);
v_deprecation_x3f_456_ = lean_ctor_get(v_decl_451_, 2);
lean_inc(v_defValue_454_);
v___x_457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_457_, 0, v_defValue_454_);
lean_inc(v_deprecation_x3f_456_);
lean_inc_ref(v_descr_455_);
lean_inc_n(v_name_450_, 2);
v___x_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_458_, 0, v_name_450_);
lean_ctor_set(v___x_458_, 1, v_ref_452_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v_descr_455_);
lean_ctor_set(v___x_458_, 4, v_deprecation_x3f_456_);
v___x_459_ = lean_register_option(v_name_450_, v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_468_);
v___x_461_ = v___x_459_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___x_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_inc(v_defValue_454_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_name_450_);
lean_ctor_set(v___x_463_, 1, v_defValue_454_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_name_450_);
v_a_469_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_459_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_459_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_477_, lean_object* v_decl_478_, lean_object* v_ref_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v_name_477_, v_decl_478_, v_ref_479_);
lean_dec_ref(v_decl_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_501_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_503_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v___x_500_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(lean_object* v_opts_506_, lean_object* v_opt_507_){
_start:
{
lean_object* v_name_508_; lean_object* v_defValue_509_; lean_object* v_map_510_; lean_object* v___x_511_; 
v_name_508_ = lean_ctor_get(v_opt_507_, 0);
v_defValue_509_ = lean_ctor_get(v_opt_507_, 1);
v_map_510_ = lean_ctor_get(v_opts_506_, 0);
v___x_511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_510_, v_name_508_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_inc(v_defValue_509_);
return v_defValue_509_;
}
else
{
lean_object* v_val_512_; 
v_val_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v___x_511_, 1);
if (lean_obj_tag(v_val_512_) == 3)
{
lean_object* v_v_513_; 
v_v_513_ = lean_ctor_get(v_val_512_, 0);
lean_inc(v_v_513_);
lean_dec_ref_known(v_val_512_, 1);
return v_v_513_;
}
else
{
lean_dec(v_val_512_);
lean_inc(v_defValue_509_);
return v_defValue_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0___boxed(lean_object* v_opts_514_, lean_object* v_opt_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_opts_514_, v_opt_515_);
lean_dec_ref(v_opt_515_);
lean_dec_ref(v_opts_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object* v_o_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_519_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_o_517_, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object* v_o_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_o_520_);
lean_dec_ref(v_o_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object* v_x_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_kind_526_; lean_object* v_a_527_; lean_object* v___x_528_; 
v_kind_526_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_kind_526_);
v_a_527_ = lean_ctor_get(v_x_522_, 1);
lean_inc(v_a_527_);
lean_dec_ref_known(v_x_522_, 2);
v___x_528_ = l_Lean_PrettyPrinter_ppCategory(v_kind_526_, v_a_527_, v_a_523_, v_a_524_);
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_a_529_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v_x_522_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v_x_522_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 3);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty___boxed(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(v_x_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object* v_s_543_, lean_object* v_w_544_, lean_object* v_indent_545_, lean_object* v_column_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
if (lean_obj_tag(v_s_543_) == 0)
{
lean_object* v_kind_550_; lean_object* v_a_551_; lean_object* v_w_553_; lean_object* v___y_554_; lean_object* v___y_555_; 
v_kind_550_ = lean_ctor_get(v_s_543_, 0);
lean_inc(v_kind_550_);
v_a_551_ = lean_ctor_get(v_s_543_, 1);
lean_inc(v_a_551_);
lean_dec_ref_known(v_s_543_, 2);
if (lean_obj_tag(v_w_544_) == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_547_);
v___x_575_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v___x_574_);
lean_dec_ref(v___x_574_);
v_w_553_ = v___x_575_;
v___y_554_ = v_a_547_;
v___y_555_ = v_a_548_;
goto v___jp_552_;
}
else
{
lean_object* v_val_576_; 
v_val_576_ = lean_ctor_get(v_w_544_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v_w_544_, 1);
v_w_553_ = v_val_576_;
v___y_554_ = v_a_547_;
v___y_555_ = v_a_548_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PrettyPrinter_ppCategory(v_kind_550_, v_a_551_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = l_Std_Format_pretty(v_a_557_, v_w_553_, v_indent_545_, v_column_546_);
lean_dec(v_w_553_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_w_553_);
lean_dec(v_column_546_);
lean_dec(v_indent_545_);
v_a_566_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_556_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_556_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_column_546_);
lean_dec(v_indent_545_);
lean_dec(v_w_544_);
v_a_577_ = lean_ctor_get(v_s_543_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_s_543_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v_s_543_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v_s_543_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 0);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___boxed(lean_object* v_s_585_, lean_object* v_w_586_, lean_object* v_indent_587_, lean_object* v_column_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_s_585_, v_w_586_, v_indent_587_, v_column_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(lean_object* v_s_593_, lean_object* v_w_594_, lean_object* v_indent_595_, lean_object* v_column_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_suggestion_600_; lean_object* v___x_601_; 
v_suggestion_600_ = lean_ctor_get(v_s_593_, 0);
lean_inc_ref(v_suggestion_600_);
lean_dec_ref(v_s_593_);
v___x_601_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_suggestion_600_, v_w_594_, v_indent_595_, v_column_596_, v_a_597_, v_a_598_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty___boxed(lean_object* v_s_602_, lean_object* v_w_603_, lean_object* v_indent_604_, lean_object* v_column_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_602_, v_w_603_, v_indent_604_, v_column_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(lean_object* v_s_610_, lean_object* v_range_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_toCold_615_; lean_object* v_fileMap_616_; lean_object* v___x_617_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_toCold_615_ = lean_ctor_get(v_a_612_, 0);
v_fileMap_616_ = lean_ctor_get(v_toCold_615_, 1);
lean_inc_ref(v_range_611_);
lean_inc_ref(v_fileMap_616_);
v___x_617_ = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(v_fileMap_616_, v_range_611_);
v_fst_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_snd_619_);
lean_dec_ref(v___x_617_);
v___x_620_ = lean_box(0);
v___x_621_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_610_, v___x_620_, v_fst_618_, v_snd_619_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_631_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_631_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc_ref(v_fileMap_616_);
v___x_626_ = l_Lean_FileMap_utf8RangeToLspRange(v_fileMap_616_, v_range_611_);
v___x_627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_622_);
lean_ctor_set(v___x_627_, 2, v___x_620_);
lean_ctor_set(v___x_627_, 3, v___x_620_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_range_611_);
v_a_632_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_621_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_621_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit___boxed(lean_object* v_s_640_, lean_object* v_range_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_s_640_, v_range_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_645_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1 = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible);
res = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_TryThis_format_inputWidth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_format_inputWidth);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_TryThis(builtin);
}
#ifdef __cplusplus
}
#endif
