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
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t v_decorated_113_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error_0interp(lean_interpreter_value* stack)
{
uint8_t v_decorated_113_ = stack[0].m_num;
lean_object* v_res_125_;
v_res_125_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(v_decorated_113_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object* v_decorated_126_){
_start:
{
uint8_t v_decorated_boxed_127_; lean_object* v_res_128_; 
v_decorated_boxed_127_ = lean_unbox(v_decorated_126_);
v_res_128_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(v_decorated_boxed_127_);
return v_res_128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3));
v___x_139_ = l_Lean_Json_mkObj(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8));
v___x_150_ = l_Lean_Json_mkObj(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9);
v___x_152_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11);
v___x_158_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2));
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12);
v___x_161_ = l_Lean_Json_mkObj(v___x_160_);
return v___x_161_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t v_decorated_162_){
_start:
{
if (v_decorated_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13);
return v___x_164_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning_0interp(lean_interpreter_value* stack)
{
uint8_t v_decorated_162_ = stack[0].m_num;
lean_object* v_res_165_;
v_res_165_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(v_decorated_162_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object* v_decorated_166_){
_start:
{
uint8_t v_decorated_boxed_167_; lean_object* v_res_168_; 
v_decorated_boxed_167_ = lean_unbox(v_decorated_166_);
v_res_168_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(v_decorated_boxed_167_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3));
v___x_179_ = l_Lean_Json_mkObj(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3));
v___x_191_ = l_Lean_Json_mkObj(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3));
v___x_203_ = l_Lean_Json_mkObj(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4);
return v___x_204_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0(void){
_start:
{
lean_object* v___x_205_; double v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_float_of_nat(v___x_205_);
return v___x_206_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1(void){
_start:
{
lean_object* v___x_207_; double v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_float_of_nat(v___x_207_);
return v___x_208_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3(void){
_start:
{
lean_object* v___x_210_; double v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(120u);
v___x_211_ = lean_float_of_nat(v___x_210_);
return v___x_211_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5(void){
_start:
{
lean_object* v___x_213_; double v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(60u);
v___x_214_ = lean_float_of_nat(v___x_213_);
return v___x_214_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6(void){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; double v___x_218_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = 1;
v___x_217_ = lean_unsigned_to_nat(5u);
v___x_218_ = l_Float_ofScientific(v___x_217_, v___x_216_, v___x_215_);
return v___x_218_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7(void){
_start:
{
lean_object* v___x_219_; double v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lean_float_of_nat(v___x_219_);
return v___x_220_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8(void){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; double v___x_224_; 
v___x_221_ = lean_unsigned_to_nat(2u);
v___x_222_ = 1;
v___x_223_ = lean_unsigned_to_nat(75u);
v___x_224_ = l_Float_ofScientific(v___x_223_, v___x_222_, v___x_221_);
return v___x_224_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double v_t_230_, uint8_t v_showValueInHoverText_231_){
_start:
{
double v___x_232_; double v___x_233_; double v___x_234_; double v_t_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; double v___x_240_; double v___x_241_; double v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; double v___x_247_; double v___x_248_; double v___x_249_; double v___x_250_; double v___x_251_; double v___x_252_; double v___x_253_; double v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___y_267_; 
v___x_232_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0);
v___x_233_ = lean_float_maximum(v_t_230_, v___x_232_);
v___x_234_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1);
v_t_235_ = lean_float_minimum(v___x_233_, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3));
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_238_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5));
v___x_239_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2));
v___x_240_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3);
v___x_241_ = lean_float_mul(v_t_235_, v___x_240_);
v___x_242_ = round(v___x_241_);
v___x_243_ = lean_float_to_string(v___x_242_);
v___x_244_ = lean_string_append(v___x_239_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_245_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5);
v___x_248_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6);
v___x_249_ = lean_float_sub(v_t_235_, v___x_248_);
v___x_250_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7);
v___x_251_ = pow(v___x_249_, v___x_250_);
v___x_252_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8);
v___x_253_ = lean_float_add(v___x_251_, v___x_252_);
v___x_254_ = lean_float_mul(v___x_247_, v___x_253_);
v___x_255_ = lean_float_to_string(v___x_254_);
v___x_256_ = lean_string_append(v___x_246_, v___x_255_);
lean_dec_ref(v___x_255_);
v___x_257_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9));
v___x_258_ = lean_string_append(v___x_256_, v___x_257_);
v___x_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_238_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_Json_mkObj(v___x_262_);
lean_dec_ref_known(v___x_262_, 2);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_237_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10));
if (v_showValueInHoverText_231_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11));
v___y_267_ = v___x_274_;
goto v___jp_266_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12));
v___x_276_ = lean_float_to_string(v_t_235_);
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13));
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
v___y_267_ = v___x_279_;
goto v___jp_266_;
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___y_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_265_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_261_);
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_264_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_236_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_Json_mkObj(v___x_272_);
lean_dec_ref_known(v___x_272_, 2);
return v___x_273_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value_0interp(lean_interpreter_value* stack)
{
double v_t_230_ = stack[0].m_float;
uint8_t v_showValueInHoverText_231_ = stack[1].m_num;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(v_t_230_, v_showValueInHoverText_231_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object* v_t_281_, lean_object* v_showValueInHoverText_282_){
_start:
{
double v_t_boxed_283_; uint8_t v_showValueInHoverText_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_283_ = lean_unbox_float(v_t_281_);
lean_dec_ref(v_t_281_);
v_showValueInHoverText_boxed_284_ = lean_unbox(v_showValueInHoverText_282_);
v_res_285_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(v_t_boxed_283_, v_showValueInHoverText_boxed_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object* v_s_291_){
_start:
{
lean_object* v_messageData_x3f_292_; 
v_messageData_x3f_292_ = lean_ctor_get(v_s_291_, 4);
if (lean_obj_tag(v_messageData_x3f_292_) == 0)
{
lean_object* v_suggestion_293_; 
v_suggestion_293_ = lean_ctor_get(v_s_291_, 0);
lean_inc_ref(v_suggestion_293_);
lean_dec_ref(v_s_291_);
if (lean_obj_tag(v_suggestion_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; 
v_a_294_ = lean_ctor_get(v_suggestion_293_, 1);
lean_inc(v_a_294_);
lean_dec_ref_known(v_suggestion_293_, 2);
v___x_295_ = l_Lean_MessageData_ofSyntax(v_a_294_);
return v___x_295_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v_a_296_ = lean_ctor_get(v_suggestion_293_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_suggestion_293_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v_suggestion_293_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v_suggestion_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 3);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
return v___x_302_;
}
}
}
}
else
{
lean_object* v_val_305_; 
lean_inc_ref(v_messageData_x3f_292_);
lean_dec_ref(v_s_291_);
v_val_305_ = lean_ctor_get(v_messageData_x3f_292_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_messageData_x3f_292_, 1);
return v_val_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_310_, 0, v_t_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
lean_ctor_set(v___x_310_, 3, v___x_309_);
lean_ctor_set(v___x_310_, 4, v___x_309_);
lean_ctor_set(v___x_310_, 5, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(lean_object* v_s_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v___x_329_; uint8_t v_decide_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v_decide_330_ = lean_nat_dec_eq(v_a_327_, v___x_329_);
if (v_decide_330_ == 0)
{
lean_object* v_str_331_; lean_object* v_startInclusive_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint32_t v___x_340_; uint32_t v___x_341_; uint8_t v___x_342_; 
v_str_331_ = lean_ctor_get(v_s_326_, 0);
v_startInclusive_332_ = lean_ctor_get(v_s_326_, 1);
v___x_333_ = lean_nat_add(v_startInclusive_332_, v_a_327_);
lean_inc(v___x_333_);
lean_inc(v_startInclusive_332_);
lean_inc_ref(v_str_331_);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v_str_331_);
lean_ctor_set(v___x_334_, 1, v_startInclusive_332_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = lean_nat_sub(v___x_333_, v_startInclusive_332_);
lean_dec(v___x_333_);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
v___x_338_ = l_String_Slice_posLE(v___x_334_, v___x_337_);
lean_dec_ref_known(v___x_334_, 3);
v___x_339_ = lean_nat_add(v_startInclusive_332_, v___x_338_);
v___x_340_ = lean_string_utf8_get_fast(v_str_331_, v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = 10;
v___x_342_ = lean_uint32_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_nat_sub(v_a_327_, v___x_336_);
lean_dec(v_a_327_);
v___x_345_ = l_String_Slice_posLE(v_s_326_, v___x_344_);
v_a_327_ = v___x_345_;
v_b_328_ = v___x_343_;
goto _start;
}
else
{
lean_object* v___x_347_; 
lean_dec(v_a_327_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_338_);
return v___x_347_;
}
}
else
{
lean_dec(v_a_327_);
lean_inc(v_b_328_);
return v_b_328_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg___boxed(lean_object* v_s_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_348_, v_a_349_, v_b_350_);
lean_dec(v_b_350_);
lean_dec_ref(v_s_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(lean_object* v_s_352_){
_start:
{
lean_object* v_startInclusive_353_; lean_object* v_endExclusive_354_; lean_object* v_searcher_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_startInclusive_353_ = lean_ctor_get(v_s_352_, 1);
v_endExclusive_354_ = lean_ctor_get(v_s_352_, 2);
v_searcher_355_ = lean_nat_sub(v_endExclusive_354_, v_startInclusive_353_);
v___x_356_ = lean_box(0);
v___x_357_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_352_, v_searcher_355_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0___boxed(lean_object* v_s_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v_s_358_);
lean_dec_ref(v_s_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(lean_object* v_s_360_, lean_object* v_p_361_){
_start:
{
lean_object* v_val_363_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_360_);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v_s_360_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
lean_ctor_set(v___x_369_, 2, v_p_361_);
v___x_370_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v___x_369_);
lean_dec_ref_known(v___x_369_, 3);
if (lean_obj_tag(v___x_370_) == 0)
{
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec_ref(v_s_360_);
return v___x_368_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_370_, 1);
v_val_363_ = v_val_371_;
goto v___jp_362_;
}
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v___x_370_, 1);
v_val_363_ = v_val_372_;
goto v___jp_362_;
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_string_utf8_byte_size(v_s_360_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_s_360_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
v___x_367_ = l_String_Slice_Pos_next_x21(v___x_366_, v_val_363_);
lean_dec(v_val_363_);
lean_dec_ref_known(v___x_366_, 3);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(lean_object* v_s_373_, lean_object* v_inst_374_, lean_object* v_R_375_, lean_object* v_a_376_, lean_object* v_b_377_, lean_object* v_c_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_373_, v_a_376_, v_b_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___boxed(lean_object* v_s_380_, lean_object* v_inst_381_, lean_object* v_R_382_, lean_object* v_a_383_, lean_object* v_b_384_, lean_object* v_c_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(v_s_380_, v_inst_381_, v_R_382_, v_a_383_, v_b_384_, v_c_385_);
lean_dec(v_b_384_);
lean_dec_ref(v_s_380_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
lean_object* v_str_390_; lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; lean_object* v___x_393_; uint8_t v_decide_394_; 
v_str_390_ = lean_ctor_get(v___x_387_, 0);
v_startInclusive_391_ = lean_ctor_get(v___x_387_, 1);
v_endExclusive_392_ = lean_ctor_get(v___x_387_, 2);
v___x_393_ = lean_nat_sub(v_endExclusive_392_, v_startInclusive_391_);
v_decide_394_ = lean_nat_dec_eq(v_a_388_, v___x_393_);
lean_dec(v___x_393_);
if (v_decide_394_ == 0)
{
lean_object* v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_395_ = lean_nat_add(v_startInclusive_391_, v_a_388_);
v___x_396_ = lean_string_utf8_get_fast(v_str_390_, v___x_395_);
v___x_397_ = 32;
v___x_398_ = lean_uint32_dec_eq(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___x_395_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_a_388_);
return v___x_399_;
}
else
{
if (v_decide_394_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_a_388_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_string_utf8_next_fast(v_str_390_, v___x_395_);
lean_dec(v___x_395_);
v___x_402_ = lean_nat_sub(v___x_401_, v_startInclusive_391_);
v_a_388_ = v___x_402_;
v_b_389_ = v___x_400_;
goto _start;
}
else
{
lean_object* v___x_404_; 
lean_dec(v___x_395_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_a_388_);
return v___x_404_;
}
}
}
else
{
lean_dec(v_a_388_);
lean_inc(v_b_389_);
return v_b_389_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg___boxed(lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_405_, v_a_406_, v_b_407_);
lean_dec(v_b_407_);
lean_dec_ref(v___x_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object* v_map_409_, lean_object* v_range_410_){
_start:
{
lean_object* v_source_411_; lean_object* v_start_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_437_; 
v_source_411_ = lean_ctor_get(v_map_409_, 0);
lean_inc_ref(v_source_411_);
lean_dec_ref(v_map_409_);
v_start_412_ = lean_ctor_get(v_range_410_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_range_410_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v_range_410_, 1);
lean_dec(v_unused_438_);
v___x_414_ = v_range_410_;
v_isShared_415_ = v_isSharedCheck_437_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_start_412_);
lean_dec(v_range_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_437_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_searcher_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_rangeStart_419_; lean_object* v_start_420_; lean_object* v___x_421_; lean_object* v___y_423_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_searcher_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_string_utf8_byte_size(v_source_411_);
lean_inc_ref_n(v_source_411_, 2);
v___x_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_418_, 0, v_source_411_);
lean_ctor_set(v___x_418_, 1, v_searcher_416_);
lean_ctor_set(v___x_418_, 2, v___x_417_);
v_rangeStart_419_ = l_String_Slice_pos_x21(v___x_418_, v_start_412_);
lean_dec_ref_known(v___x_418_, 3);
lean_inc(v_rangeStart_419_);
v_start_420_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(v_source_411_, v_rangeStart_419_);
v___x_421_ = l_String_slice_x21(v_source_411_, v_start_420_, v_rangeStart_419_);
lean_dec(v_rangeStart_419_);
v___x_431_ = lean_box(0);
v___x_432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_421_, v_searcher_416_, v___x_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_startInclusive_433_; lean_object* v_endExclusive_434_; lean_object* v___x_435_; 
v_startInclusive_433_ = lean_ctor_get(v___x_421_, 1);
v_endExclusive_434_ = lean_ctor_get(v___x_421_, 2);
v___x_435_ = lean_nat_sub(v_endExclusive_434_, v_startInclusive_433_);
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_432_, 1);
v___y_423_ = v_val_436_;
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v_startInclusive_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v_startInclusive_424_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_startInclusive_424_);
lean_dec_ref(v___x_421_);
v___x_425_ = lean_nat_add(v_startInclusive_424_, v___y_423_);
lean_dec(v___y_423_);
lean_dec(v_startInclusive_424_);
v___x_426_ = lean_nat_sub(v___x_425_, v_start_420_);
lean_dec(v___x_425_);
v___x_427_ = lean_nat_sub(v_start_412_, v_start_420_);
lean_dec(v_start_420_);
lean_dec(v_start_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_427_);
lean_ctor_set(v___x_414_, 0, v___x_426_);
v___x_429_ = v___x_414_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(lean_object* v___x_439_, lean_object* v_inst_440_, lean_object* v_R_441_, lean_object* v_a_442_, lean_object* v_b_443_, lean_object* v_c_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_439_, v_a_442_, v_b_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___boxed(lean_object* v___x_446_, lean_object* v_inst_447_, lean_object* v_R_448_, lean_object* v_a_449_, lean_object* v_b_450_, lean_object* v_c_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(v___x_446_, v_inst_447_, v_R_448_, v_a_449_, v_b_450_, v_c_451_);
lean_dec(v_b_450_);
lean_dec_ref(v___x_446_);
return v_res_452_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(lean_object* v_name_453_, lean_object* v_decl_454_, lean_object* v_ref_455_){
_start:
{
lean_object* v_defValue_457_; lean_object* v_descr_458_; lean_object* v_deprecation_x3f_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_defValue_457_ = lean_ctor_get(v_decl_454_, 0);
v_descr_458_ = lean_ctor_get(v_decl_454_, 1);
v_deprecation_x3f_459_ = lean_ctor_get(v_decl_454_, 2);
lean_inc(v_defValue_457_);
v___x_460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_460_, 0, v_defValue_457_);
lean_inc(v_deprecation_x3f_459_);
lean_inc_ref(v_descr_458_);
lean_inc_n(v_name_453_, 2);
v___x_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_461_, 0, v_name_453_);
lean_ctor_set(v___x_461_, 1, v_ref_455_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
lean_ctor_set(v___x_461_, 3, v_descr_458_);
lean_ctor_set(v___x_461_, 4, v_deprecation_x3f_459_);
v___x_462_ = lean_register_option(v_name_453_, v___x_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_462_, 0);
lean_dec(v_unused_471_);
v___x_464_ = v___x_462_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_inc(v_defValue_457_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_name_453_);
lean_ctor_set(v___x_466_, 1, v_defValue_457_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_name_453_);
v_a_472_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_462_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_462_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_453_ = stack[0].m_obj;
lean_object* v_decl_454_ = stack[1].m_obj;
lean_object* v_ref_455_ = stack[2].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v_name_453_, v_decl_454_, v_ref_455_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_481_, lean_object* v_decl_482_, lean_object* v_ref_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v_name_481_, v_decl_482_, v_ref_483_);
lean_dec_ref(v_decl_482_);
return v_res_485_;
}
}
lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_505_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_507_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v___x_504_, v___x_505_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(lean_object* v_opts_511_, lean_object* v_opt_512_){
_start:
{
lean_object* v_name_513_; lean_object* v_defValue_514_; lean_object* v_map_515_; lean_object* v___x_516_; 
v_name_513_ = lean_ctor_get(v_opt_512_, 0);
v_defValue_514_ = lean_ctor_get(v_opt_512_, 1);
v_map_515_ = lean_ctor_get(v_opts_511_, 0);
v___x_516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_515_, v_name_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_inc(v_defValue_514_);
return v_defValue_514_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_516_, 1);
if (lean_obj_tag(v_val_517_) == 3)
{
lean_object* v_v_518_; 
v_v_518_ = lean_ctor_get(v_val_517_, 0);
lean_inc(v_v_518_);
lean_dec_ref_known(v_val_517_, 1);
return v_v_518_;
}
else
{
lean_dec(v_val_517_);
lean_inc(v_defValue_514_);
return v_defValue_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0___boxed(lean_object* v_opts_519_, lean_object* v_opt_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_opts_519_, v_opt_520_);
lean_dec_ref(v_opt_520_);
lean_dec_ref(v_opts_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object* v_o_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_524_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_o_522_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object* v_o_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_o_525_);
lean_dec_ref(v_o_525_);
return v_res_526_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object* v_x_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_kind_531_; lean_object* v_a_532_; lean_object* v___x_533_; 
v_kind_531_ = lean_ctor_get(v_x_527_, 0);
lean_inc(v_kind_531_);
v_a_532_ = lean_ctor_get(v_x_527_, 1);
lean_inc(v_a_532_);
lean_dec_ref_known(v_x_527_, 2);
v___x_533_ = l_Lean_PrettyPrinter_ppCategory(v_kind_531_, v_a_532_, v_a_528_, v_a_529_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_a_534_ = lean_ctor_get(v_x_527_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_527_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v_x_527_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v_x_527_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 3);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_527_ = stack[0].m_obj;
lean_object* v_a_528_ = stack[1].m_obj;
lean_object* v_a_529_ = stack[2].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(v_x_527_, v_a_528_, v_a_529_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty___boxed(lean_object* v_x_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(v_x_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
return v_res_548_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object* v_s_549_, lean_object* v_w_550_, lean_object* v_indent_551_, lean_object* v_column_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
if (lean_obj_tag(v_s_549_) == 0)
{
lean_object* v_kind_556_; lean_object* v_a_557_; lean_object* v_w_559_; lean_object* v___y_560_; lean_object* v___y_561_; 
v_kind_556_ = lean_ctor_get(v_s_549_, 0);
lean_inc(v_kind_556_);
v_a_557_ = lean_ctor_get(v_s_549_, 1);
lean_inc(v_a_557_);
lean_dec_ref_known(v_s_549_, 2);
if (lean_obj_tag(v_w_550_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_553_);
v___x_581_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v___x_580_);
lean_dec_ref(v___x_580_);
v_w_559_ = v___x_581_;
v___y_560_ = v_a_553_;
v___y_561_ = v_a_554_;
goto v___jp_558_;
}
else
{
lean_object* v_val_582_; 
v_val_582_ = lean_ctor_get(v_w_550_, 0);
lean_inc(v_val_582_);
lean_dec_ref_known(v_w_550_, 1);
v_w_559_ = v_val_582_;
v___y_560_ = v_a_553_;
v___y_561_ = v_a_554_;
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_PrettyPrinter_ppCategory(v_kind_556_, v_a_557_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Std_Format_pretty(v_a_563_, v_w_559_, v_indent_551_, v_column_552_);
lean_dec(v_w_559_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_w_559_);
lean_dec(v_column_552_);
lean_dec(v_indent_551_);
v_a_572_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_562_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_562_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_column_552_);
lean_dec(v_indent_551_);
lean_dec(v_w_550_);
v_a_583_ = lean_ctor_get(v_s_549_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_s_549_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v_s_549_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v_s_549_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_549_ = stack[0].m_obj;
lean_object* v_w_550_ = stack[1].m_obj;
lean_object* v_indent_551_ = stack[2].m_obj;
lean_object* v_column_552_ = stack[3].m_obj;
lean_object* v_a_553_ = stack[4].m_obj;
lean_object* v_a_554_ = stack[5].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_s_549_, v_w_550_, v_indent_551_, v_column_552_, v_a_553_, v_a_554_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___boxed(lean_object* v_s_592_, lean_object* v_w_593_, lean_object* v_indent_594_, lean_object* v_column_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_s_592_, v_w_593_, v_indent_594_, v_column_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
return v_res_599_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(lean_object* v_s_600_, lean_object* v_w_601_, lean_object* v_indent_602_, lean_object* v_column_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_suggestion_607_; lean_object* v___x_608_; 
v_suggestion_607_ = lean_ctor_get(v_s_600_, 0);
lean_inc_ref(v_suggestion_607_);
lean_dec_ref(v_s_600_);
v___x_608_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_suggestion_607_, v_w_601_, v_indent_602_, v_column_603_, v_a_604_, v_a_605_);
return v___x_608_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_Suggestion_pretty_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_600_ = stack[0].m_obj;
lean_object* v_w_601_ = stack[1].m_obj;
lean_object* v_indent_602_ = stack[2].m_obj;
lean_object* v_column_603_ = stack[3].m_obj;
lean_object* v_a_604_ = stack[4].m_obj;
lean_object* v_a_605_ = stack[5].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_600_, v_w_601_, v_indent_602_, v_column_603_, v_a_604_, v_a_605_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty___boxed(lean_object* v_s_610_, lean_object* v_w_611_, lean_object* v_indent_612_, lean_object* v_column_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_610_, v_w_611_, v_indent_612_, v_column_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_617_;
}
}
lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(lean_object* v_s_618_, lean_object* v_range_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_toCold_623_; lean_object* v_fileMap_624_; lean_object* v___x_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_toCold_623_ = lean_ctor_get(v_a_620_, 0);
v_fileMap_624_ = lean_ctor_get(v_toCold_623_, 1);
lean_inc_ref(v_range_619_);
lean_inc_ref(v_fileMap_624_);
v___x_625_ = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(v_fileMap_624_, v_range_619_);
v_fst_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v___x_625_, 1);
lean_inc(v_snd_627_);
lean_dec_ref(v___x_625_);
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_618_, v___x_628_, v_fst_626_, v_snd_627_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_639_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_639_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc_ref(v_fileMap_624_);
v___x_634_ = l_Lean_FileMap_utf8RangeToLspRange(v_fileMap_624_, v_range_619_);
v___x_635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_a_630_);
lean_ctor_set(v___x_635_, 2, v___x_628_);
lean_ctor_set(v___x_635_, 3, v___x_628_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_635_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_range_619_);
v_a_640_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_629_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_629_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_618_ = stack[0].m_obj;
lean_object* v_range_619_ = stack[1].m_obj;
lean_object* v_a_620_ = stack[2].m_obj;
lean_object* v_a_621_ = stack[3].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_s_618_, v_range_619_, v_a_620_, v_a_621_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit___boxed(lean_object* v_s_649_, lean_object* v_range_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_s_649_, v_range_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
return v_res_654_;
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
