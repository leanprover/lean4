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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_mul(double, double);
double round(double);
lean_object* lean_float_to_string(double);
lean_object* lean_string_append(lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_sub(double, double);
double pow(double, double);
double lean_float_add(double, double);
uint8_t lean_float_decLe(double, double);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle;
static const lean_closure_object l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hsl("};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " 95% "};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "%)"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Apply suggestion"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Apply suggestion ("};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inputWidth"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(41, 165, 100, 47, 160, 41, 84, 0)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 147, 146, 63, 150, 233, 253, 32)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ideal input width"};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 55, 191, 109, 224, 169, 145, 115)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 10, 29, 165, 121, 220, 111, 19)}};
static const lean_ctor_object l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(16, 85, 191, 240, 102, 91, 59, 55)}};
static const lean_object* l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_kind_8_; lean_object* v_a_9_; lean_object* v___x_10_; 
v_kind_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_kind_8_);
v_a_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_a_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_kind_8_, v_a_9_);
return v___x_10_;
}
else
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_a_11_);
lean_dec_ref(v_t_6_);
v___x_12_ = lean_apply_1(v_k_7_, v_a_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim___redArg(lean_object* v_t_25_, lean_object* v_tsyntax_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_25_, v_tsyntax_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_tsyntax_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_29_, v_tsyntax_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim___redArg(lean_object* v_t_33_, lean_object* v_string_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_33_, v_string_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_string_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_37_, v_string_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_47_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_a_47_);
lean_dec_ref(v_x_46_);
v___x_48_ = l_Lean_MessageData_ofSyntax(v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
v_a_49_ = lean_ctor_get(v_x_46_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_46_);
if (v_isSharedCheck_57_ == 0)
{
v___x_51_ = v_x_46_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v_x_46_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 3);
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_MessageData_ofFormat(v___x_54_);
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(lean_object* v_kind_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_kind_60_);
lean_ctor_set(v___x_62_, 1, v_a_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object* v_kind_63_){
_start:
{
lean_object* v___f_64_; 
v___f_64_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0), 2, 1);
lean_closure_set(v___f_64_, 0, v_kind_63_);
return v___f_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_a_65_);
return v___x_66_;
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
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9));
v___x_91_ = l_Lean_Json_mkObj(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16));
v___x_106_ = l_Lean_Json_mkObj(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t v_decorated_107_){
_start:
{
lean_object* v___y_109_; 
if (v_decorated_107_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10);
v___y_109_ = v___x_117_;
goto v___jp_108_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17);
v___y_109_ = v___x_118_;
goto v___jp_108_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_110_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3));
v___x_111_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___y_109_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_110_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = l_Lean_Json_mkObj(v___x_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object* v_decorated_119_){
_start:
{
uint8_t v_decorated_boxed_120_; lean_object* v_res_121_; 
v_decorated_boxed_120_ = lean_unbox(v_decorated_119_);
v_res_121_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(v_decorated_boxed_120_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3));
v___x_132_ = l_Lean_Json_mkObj(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8));
v___x_143_ = l_Lean_Json_mkObj(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9);
v___x_145_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11);
v___x_151_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2));
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12);
v___x_154_ = l_Lean_Json_mkObj(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t v_decorated_155_){
_start:
{
if (v_decorated_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object* v_decorated_158_){
_start:
{
uint8_t v_decorated_boxed_159_; lean_object* v_res_160_; 
v_decorated_boxed_159_ = lean_unbox(v_decorated_158_);
v_res_160_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(v_decorated_boxed_159_);
return v_res_160_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3));
v___x_171_ = l_Lean_Json_mkObj(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3));
v___x_183_ = l_Lean_Json_mkObj(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3));
v___x_195_ = l_Lean_Json_mkObj(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4);
return v___x_196_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1(void){
_start:
{
lean_object* v___x_198_; double v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(120u);
v___x_199_ = lean_float_of_nat(v___x_198_);
return v___x_199_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3(void){
_start:
{
lean_object* v___x_201_; double v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(60u);
v___x_202_ = lean_float_of_nat(v___x_201_);
return v___x_202_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4(void){
_start:
{
lean_object* v___x_203_; double v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(2u);
v___x_204_ = lean_float_of_nat(v___x_203_);
return v___x_204_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5(void){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; double v___x_208_; 
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = 1;
v___x_207_ = lean_unsigned_to_nat(75u);
v___x_208_ = l_Float_ofScientific(v___x_207_, v___x_206_, v___x_205_);
return v___x_208_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11(void){
_start:
{
lean_object* v___x_214_; double v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_float_of_nat(v___x_214_);
return v___x_215_;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12(void){
_start:
{
lean_object* v___x_216_; double v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_float_of_nat(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double v_t_218_, uint8_t v_showValueInHoverText_219_){
_start:
{
lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_233_; double v___y_234_; double v___y_274_; double v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12);
v___x_279_ = lean_float_decLe(v_t_218_, v___x_278_);
if (v___x_279_ == 0)
{
v___y_274_ = v_t_218_;
goto v___jp_273_;
}
else
{
v___y_274_ = v___x_278_;
goto v___jp_273_;
}
v___jp_220_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_226_, 0, v___y_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_223_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___y_222_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_221_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___y_224_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Json_mkObj(v___x_230_);
return v___x_231_;
}
v___jp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; double v___x_239_; double v___x_240_; double v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; double v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; double v___x_249_; double v___x_250_; double v___x_251_; double v___x_252_; double v___x_253_; double v___x_254_; double v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3));
v___x_236_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4));
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5));
v___x_238_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0));
v___x_239_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1);
v___x_240_ = lean_float_mul(v___y_234_, v___x_239_);
v___x_241_ = round(v___x_240_);
v___x_242_ = lean_float_to_string(v___x_241_);
v___x_243_ = lean_string_append(v___x_238_, v___x_242_);
lean_dec_ref(v___x_242_);
v___x_244_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2));
v___x_245_ = lean_string_append(v___x_243_, v___x_244_);
v___x_246_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3);
v___x_247_ = lean_unsigned_to_nat(5u);
v___x_248_ = 1;
v___x_249_ = l_Float_ofScientific(v___x_247_, v___x_248_, v___y_233_);
v___x_250_ = lean_float_sub(v___y_234_, v___x_249_);
v___x_251_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4);
v___x_252_ = pow(v___x_250_, v___x_251_);
v___x_253_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5);
v___x_254_ = lean_float_add(v___x_252_, v___x_253_);
v___x_255_ = lean_float_mul(v___x_246_, v___x_254_);
v___x_256_ = lean_float_to_string(v___x_255_);
v___x_257_ = lean_string_append(v___x_245_, v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6));
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
v___x_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_237_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Json_mkObj(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_236_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7));
if (v_showValueInHoverText_219_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8));
v___y_221_ = v___x_265_;
v___y_222_ = v___x_262_;
v___y_223_ = v___x_266_;
v___y_224_ = v___x_235_;
v___y_225_ = v___x_267_;
goto v___jp_220_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9));
v___x_269_ = lean_float_to_string(v___y_234_);
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
lean_dec_ref(v___x_269_);
v___x_271_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10));
v___x_272_ = lean_string_append(v___x_270_, v___x_271_);
v___y_221_ = v___x_265_;
v___y_222_ = v___x_262_;
v___y_223_ = v___x_266_;
v___y_224_ = v___x_235_;
v___y_225_ = v___x_272_;
goto v___jp_220_;
}
}
v___jp_273_:
{
lean_object* v___x_275_; double v___x_276_; uint8_t v___x_277_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_float_once(&l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11, &l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_once, _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11);
v___x_277_ = lean_float_decLe(v___y_274_, v___x_276_);
if (v___x_277_ == 0)
{
v___y_233_ = v___x_275_;
v___y_234_ = v___x_276_;
goto v___jp_232_;
}
else
{
v___y_233_ = v___x_275_;
v___y_234_ = v___y_274_;
goto v___jp_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object* v_t_280_, lean_object* v_showValueInHoverText_281_){
_start:
{
double v_t_boxed_282_; uint8_t v_showValueInHoverText_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_282_ = lean_unbox_float(v_t_280_);
lean_dec_ref(v_t_280_);
v_showValueInHoverText_boxed_283_ = lean_unbox(v_showValueInHoverText_281_);
v_res_284_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(v_t_boxed_282_, v_showValueInHoverText_boxed_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object* v_s_290_){
_start:
{
lean_object* v_messageData_x3f_291_; 
v_messageData_x3f_291_ = lean_ctor_get(v_s_290_, 4);
if (lean_obj_tag(v_messageData_x3f_291_) == 0)
{
lean_object* v_suggestion_292_; 
v_suggestion_292_ = lean_ctor_get(v_s_290_, 0);
lean_inc_ref(v_suggestion_292_);
lean_dec_ref(v_s_290_);
if (lean_obj_tag(v_suggestion_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v_suggestion_292_, 1);
lean_inc(v_a_293_);
lean_dec_ref(v_suggestion_292_);
v___x_294_ = l_Lean_MessageData_ofSyntax(v_a_293_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_a_295_ = lean_ctor_get(v_suggestion_292_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_suggestion_292_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v_suggestion_292_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v_suggestion_292_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 3);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_MessageData_ofFormat(v___x_300_);
return v___x_301_;
}
}
}
}
else
{
lean_object* v_val_304_; 
lean_inc_ref(v_messageData_x3f_291_);
lean_dec_ref(v_s_290_);
v_val_304_ = lean_ctor_get(v_messageData_x3f_291_, 0);
lean_inc(v_val_304_);
lean_dec_ref(v_messageData_x3f_291_);
return v_val_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_309_, 0, v_t_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
lean_ctor_set(v___x_309_, 4, v___x_308_);
lean_ctor_set(v___x_309_, 5, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(lean_object* v_s_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_nat_dec_eq(v_a_326_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v_str_330_; lean_object* v_startInclusive_331_; uint32_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint32_t v___x_340_; uint8_t v___x_341_; 
lean_dec(v_b_327_);
v_str_330_ = lean_ctor_get(v_s_325_, 0);
v_startInclusive_331_ = lean_ctor_get(v_s_325_, 1);
v___x_332_ = 10;
v___x_333_ = lean_nat_add(v_startInclusive_331_, v_a_326_);
lean_inc(v___x_333_);
lean_inc(v_startInclusive_331_);
lean_inc_ref(v_str_330_);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v_str_330_);
lean_ctor_set(v___x_334_, 1, v_startInclusive_331_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = lean_nat_sub(v___x_333_, v_startInclusive_331_);
lean_dec(v___x_333_);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
v___x_338_ = l_String_Slice_posLE(v___x_334_, v___x_337_);
lean_dec_ref(v___x_334_);
v___x_339_ = lean_nat_add(v_startInclusive_331_, v___x_338_);
v___x_340_ = lean_string_utf8_get_fast(v_str_330_, v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_uint32_dec_eq(v___x_340_, v___x_332_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_nat_sub(v_a_326_, v___x_336_);
lean_dec(v_a_326_);
v___x_344_ = l_String_Slice_posLE(v_s_325_, v___x_343_);
v_a_326_ = v___x_344_;
v_b_327_ = v___x_342_;
goto _start;
}
else
{
lean_object* v___x_346_; 
lean_dec(v_a_326_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_338_);
return v___x_346_;
}
}
else
{
lean_dec(v_a_326_);
return v_b_327_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg___boxed(lean_object* v_s_347_, lean_object* v_a_348_, lean_object* v_b_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_347_, v_a_348_, v_b_349_);
lean_dec_ref(v_s_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(lean_object* v_s_351_){
_start:
{
lean_object* v_startInclusive_352_; lean_object* v_endExclusive_353_; lean_object* v_searcher_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_startInclusive_352_ = lean_ctor_get(v_s_351_, 1);
v_endExclusive_353_ = lean_ctor_get(v_s_351_, 2);
v_searcher_354_ = lean_nat_sub(v_endExclusive_353_, v_startInclusive_352_);
v___x_355_ = lean_box(0);
v___x_356_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_351_, v_searcher_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0___boxed(lean_object* v_s_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v_s_357_);
lean_dec_ref(v_s_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(lean_object* v_s_359_, lean_object* v_p_360_){
_start:
{
lean_object* v_val_362_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_359_);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v_s_359_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
lean_ctor_set(v___x_368_, 2, v_p_360_);
v___x_369_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v___x_368_);
lean_dec_ref(v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
if (lean_obj_tag(v___x_369_) == 0)
{
lean_dec_ref(v_s_359_);
return v___x_367_;
}
else
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_370_);
lean_dec_ref(v___x_369_);
v_val_362_ = v_val_370_;
goto v___jp_361_;
}
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v___x_369_);
v_val_362_ = v_val_371_;
goto v___jp_361_;
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_string_utf8_byte_size(v_s_359_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_s_359_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
v___x_366_ = l_String_Slice_Pos_next_x21(v___x_365_, v_val_362_);
lean_dec(v_val_362_);
lean_dec_ref(v___x_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(lean_object* v_s_372_, lean_object* v_inst_373_, lean_object* v_R_374_, lean_object* v_a_375_, lean_object* v_b_376_, lean_object* v_c_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_372_, v_a_375_, v_b_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___boxed(lean_object* v_s_379_, lean_object* v_inst_380_, lean_object* v_R_381_, lean_object* v_a_382_, lean_object* v_b_383_, lean_object* v_c_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(v_s_379_, v_inst_380_, v_R_381_, v_a_382_, v_b_383_, v_c_384_);
lean_dec_ref(v_s_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_str_389_; lean_object* v_startInclusive_390_; lean_object* v_endExclusive_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_str_389_ = lean_ctor_get(v___x_386_, 0);
v_startInclusive_390_ = lean_ctor_get(v___x_386_, 1);
v_endExclusive_391_ = lean_ctor_get(v___x_386_, 2);
v___x_392_ = lean_nat_sub(v_endExclusive_391_, v_startInclusive_390_);
v___x_393_ = lean_nat_dec_eq(v_a_387_, v___x_392_);
lean_dec(v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint8_t v___x_397_; 
lean_dec(v_b_388_);
v___x_394_ = lean_nat_add(v_startInclusive_390_, v_a_387_);
v___x_395_ = lean_string_utf8_get_fast(v_str_389_, v___x_394_);
v___x_396_ = 32;
v___x_397_ = lean_uint32_dec_eq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec(v___x_394_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_a_387_);
return v___x_398_;
}
else
{
if (v___x_393_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v_a_387_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_string_utf8_next_fast(v_str_389_, v___x_394_);
lean_dec(v___x_394_);
v___x_401_ = lean_nat_sub(v___x_400_, v_startInclusive_390_);
v_a_387_ = v___x_401_;
v_b_388_ = v___x_399_;
goto _start;
}
else
{
lean_object* v___x_403_; 
lean_dec(v___x_394_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_a_387_);
return v___x_403_;
}
}
}
else
{
lean_dec(v_a_387_);
return v_b_388_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg___boxed(lean_object* v___x_404_, lean_object* v_a_405_, lean_object* v_b_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_404_, v_a_405_, v_b_406_);
lean_dec_ref(v___x_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object* v_map_408_, lean_object* v_range_409_){
_start:
{
lean_object* v_source_410_; lean_object* v_start_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_436_; 
v_source_410_ = lean_ctor_get(v_map_408_, 0);
lean_inc_ref(v_source_410_);
lean_dec_ref(v_map_408_);
v_start_411_ = lean_ctor_get(v_range_409_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_range_409_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_range_409_, 1);
lean_dec(v_unused_437_);
v___x_413_ = v_range_409_;
v_isShared_414_ = v_isSharedCheck_436_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_start_411_);
lean_dec(v_range_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_436_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_searcher_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_rangeStart_418_; lean_object* v_start_419_; lean_object* v___x_420_; lean_object* v___y_422_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_searcher_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_string_utf8_byte_size(v_source_410_);
lean_inc_ref(v_source_410_);
v___x_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_417_, 0, v_source_410_);
lean_ctor_set(v___x_417_, 1, v_searcher_415_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
v_rangeStart_418_ = l_String_Slice_pos_x21(v___x_417_, v_start_411_);
lean_dec_ref(v___x_417_);
lean_inc(v_rangeStart_418_);
lean_inc_ref(v_source_410_);
v_start_419_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(v_source_410_, v_rangeStart_418_);
v___x_420_ = l_String_slice_x21(v_source_410_, v_start_419_, v_rangeStart_418_);
lean_dec(v_rangeStart_418_);
v___x_430_ = lean_box(0);
v___x_431_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_420_, v_searcher_415_, v___x_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_startInclusive_432_; lean_object* v_endExclusive_433_; lean_object* v___x_434_; 
v_startInclusive_432_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_startInclusive_432_);
v_endExclusive_433_ = lean_ctor_get(v___x_420_, 2);
lean_inc(v_endExclusive_433_);
v___x_434_ = lean_nat_sub(v_endExclusive_433_, v_startInclusive_432_);
lean_dec(v_startInclusive_432_);
lean_dec(v_endExclusive_433_);
v___y_422_ = v___x_434_;
goto v___jp_421_;
}
else
{
lean_object* v_val_435_; 
v_val_435_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v___x_431_);
v___y_422_ = v_val_435_;
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v_startInclusive_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v_startInclusive_423_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_startInclusive_423_);
lean_dec_ref(v___x_420_);
v___x_424_ = lean_nat_add(v_startInclusive_423_, v___y_422_);
lean_dec(v___y_422_);
lean_dec(v_startInclusive_423_);
v___x_425_ = lean_nat_sub(v___x_424_, v_start_419_);
lean_dec(v___x_424_);
v___x_426_ = lean_nat_sub(v_start_411_, v_start_419_);
lean_dec(v_start_419_);
lean_dec(v_start_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_426_);
lean_ctor_set(v___x_413_, 0, v___x_425_);
v___x_428_ = v___x_413_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(lean_object* v___x_438_, lean_object* v_inst_439_, lean_object* v_R_440_, lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_c_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_438_, v_a_441_, v_b_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___boxed(lean_object* v___x_445_, lean_object* v_inst_446_, lean_object* v_R_447_, lean_object* v_a_448_, lean_object* v_b_449_, lean_object* v_c_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(v___x_445_, v_inst_446_, v_R_447_, v_a_448_, v_b_449_, v_c_450_);
lean_dec_ref(v___x_445_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(lean_object* v_name_452_, lean_object* v_decl_453_, lean_object* v_ref_454_){
_start:
{
lean_object* v_defValue_456_; lean_object* v_descr_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_483_; 
v_defValue_456_ = lean_ctor_get(v_decl_453_, 0);
v_descr_457_ = lean_ctor_get(v_decl_453_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_decl_453_);
if (v_isSharedCheck_483_ == 0)
{
v___x_459_ = v_decl_453_;
v_isShared_460_ = v_isSharedCheck_483_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_descr_457_);
lean_inc(v_defValue_456_);
lean_dec(v_decl_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_483_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_defValue_456_);
v___x_461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_461_, 0, v_defValue_456_);
lean_inc(v_name_452_);
v___x_462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_462_, 0, v_name_452_);
lean_ctor_set(v___x_462_, 1, v_ref_454_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set(v___x_462_, 3, v_descr_457_);
lean_inc(v_name_452_);
v___x_463_ = lean_register_option(v_name_452_, v___x_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_473_; 
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_474_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_defValue_456_);
lean_ctor_set(v___x_459_, 0, v_name_452_);
v___x_468_ = v___x_459_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_name_452_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_defValue_456_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
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
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_459_);
lean_dec(v_defValue_456_);
lean_dec(v_name_452_);
v_a_475_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_463_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_463_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_484_, lean_object* v_decl_485_, lean_object* v_ref_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v_name_484_, v_decl_485_, v_ref_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_507_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_508_ = ((lean_object*)(l_Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_));
v___x_509_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(lean_object* v_opts_512_, lean_object* v_opt_513_){
_start:
{
lean_object* v_name_514_; lean_object* v_defValue_515_; lean_object* v_map_516_; lean_object* v___x_517_; 
v_name_514_ = lean_ctor_get(v_opt_513_, 0);
v_defValue_515_ = lean_ctor_get(v_opt_513_, 1);
v_map_516_ = lean_ctor_get(v_opts_512_, 0);
v___x_517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_516_, v_name_514_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_inc(v_defValue_515_);
return v_defValue_515_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_val_518_);
lean_dec_ref(v___x_517_);
if (lean_obj_tag(v_val_518_) == 3)
{
lean_object* v_v_519_; 
v_v_519_ = lean_ctor_get(v_val_518_, 0);
lean_inc(v_v_519_);
lean_dec_ref(v_val_518_);
return v_v_519_;
}
else
{
lean_dec(v_val_518_);
lean_inc(v_defValue_515_);
return v_defValue_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0___boxed(lean_object* v_opts_520_, lean_object* v_opt_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_opts_520_, v_opt_521_);
lean_dec_ref(v_opt_521_);
lean_dec_ref(v_opts_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object* v_o_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_525_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(v_o_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object* v_o_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_o_526_);
lean_dec_ref(v_o_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_kind_532_; lean_object* v_a_533_; lean_object* v___x_534_; 
v_kind_532_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_kind_532_);
v_a_533_ = lean_ctor_get(v_x_528_, 1);
lean_inc(v_a_533_);
lean_dec_ref(v_x_528_);
v___x_534_ = l_Lean_PrettyPrinter_ppCategory(v_kind_532_, v_a_533_, v_a_529_, v_a_530_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
v_a_535_ = lean_ctor_get(v_x_528_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v_x_528_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v_x_528_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 3);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty___boxed(lean_object* v_x_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(v_x_544_, v_a_545_, v_a_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object* v_s_549_, lean_object* v_w_550_, lean_object* v_indent_551_, lean_object* v_column_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
if (lean_obj_tag(v_s_549_) == 0)
{
lean_object* v_kind_556_; lean_object* v_a_557_; lean_object* v_w_559_; lean_object* v___y_560_; lean_object* v___y_561_; 
v_kind_556_ = lean_ctor_get(v_s_549_, 0);
lean_inc(v_kind_556_);
v_a_557_ = lean_ctor_get(v_s_549_, 1);
lean_inc(v_a_557_);
lean_dec_ref(v_s_549_);
if (lean_obj_tag(v_w_550_) == 0)
{
lean_object* v_options_580_; lean_object* v___x_581_; 
v_options_580_ = lean_ctor_get(v_a_553_, 2);
v___x_581_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_options_580_);
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
lean_dec_ref(v_w_550_);
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
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___boxed(lean_object* v_s_591_, lean_object* v_w_592_, lean_object* v_indent_593_, lean_object* v_column_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_s_591_, v_w_592_, v_indent_593_, v_column_594_, v_a_595_, v_a_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(lean_object* v_s_599_, lean_object* v_w_600_, lean_object* v_indent_601_, lean_object* v_column_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_suggestion_606_; lean_object* v___x_607_; 
v_suggestion_606_ = lean_ctor_get(v_s_599_, 0);
lean_inc_ref(v_suggestion_606_);
lean_dec_ref(v_s_599_);
v___x_607_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v_suggestion_606_, v_w_600_, v_indent_601_, v_column_602_, v_a_603_, v_a_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_pretty___boxed(lean_object* v_s_608_, lean_object* v_w_609_, lean_object* v_indent_610_, lean_object* v_column_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_608_, v_w_609_, v_indent_610_, v_column_611_, v_a_612_, v_a_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(lean_object* v_s_616_, lean_object* v_range_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_fileMap_621_; lean_object* v___x_622_; lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_fileMap_621_ = lean_ctor_get(v_a_618_, 1);
lean_inc_ref(v_fileMap_621_);
lean_inc_ref(v_range_617_);
lean_inc_ref(v_fileMap_621_);
v___x_622_ = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(v_fileMap_621_, v_range_617_);
v_fst_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_fst_623_);
v_snd_624_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_snd_624_);
lean_dec_ref(v___x_622_);
v___x_625_ = lean_box(0);
v___x_626_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(v_s_616_, v___x_625_, v_fst_623_, v_snd_624_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_636_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_636_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_631_ = l_Lean_FileMap_utf8RangeToLspRange(v_fileMap_621_, v_range_617_);
v___x_632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v_a_627_);
lean_ctor_set(v___x_632_, 2, v___x_625_);
lean_ctor_set(v___x_632_, 3, v___x_625_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_fileMap_621_);
lean_dec_ref(v_range_617_);
v_a_637_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_626_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_626_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit___boxed(lean_object* v_s_645_, lean_object* v_range_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_s_645_, v_range_646_, v_a_647_, v_a_648_);
return v_res_650_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible);
res = l_Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
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
