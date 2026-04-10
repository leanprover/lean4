// Lean compiler output
// Module: Lake.Config.Pattern
// Imports: public import Init.System.FilePath public import Std.Data.TreeMap.Basic public import Lean.Data.Name import Lake.Util.Name import Init.Data.String.TakeDrop public import Init.Data.String.Basic import Init.Data.Option.Coe import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static const lean_string_object l_Lake_term___x3d_x7e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__0 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__0_value;
static const lean_string_object l_Lake_term___x3d_x7e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_=~_"};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__1 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__1_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_term___x3d_x7e___00__closed__2_value_aux_0),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 9, 58, 153, 13, 139, 75, 99)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__2 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__2_value;
static const lean_string_object l_Lake_term___x3d_x7e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__3 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__3_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__4 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__4_value;
static const lean_string_object l_Lake_term___x3d_x7e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " =~ "};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__5 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__5_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_term___x3d_x7e___00__closed__5_value)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__6 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__6_value;
static const lean_string_object l_Lake_term___x3d_x7e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__7 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__7_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__8 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__8_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_term___x3d_x7e___00__closed__8_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__9 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__9_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_term___x3d_x7e___00__closed__4_value),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__6_value),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__9_value)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__10 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__10_value;
static const lean_ctor_object l_Lake_term___x3d_x7e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lake_term___x3d_x7e___00__closed__2_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__10_value)}};
static const lean_object* l_Lake_term___x3d_x7e___00__closed__11 = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lake_term___x3d_x7e__ = (const lean_object*)&l_Lake_term___x3d_x7e___00__closed__11_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "IsPattern.satisfies"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5_value;
static lean_once_cell_t l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IsPattern"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "satisfies"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(203, 197, 37, 81, 87, 23, 4, 135)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(125, 16, 93, 115, 165, 91, 116, 240)}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term___x3d_x7e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 171, 122, 173, 131, 19, 19, 187)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 192, 140, 178, 195, 226, 127)}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12_value;
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instInhabitedPattern_default__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedPattern_default__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedPattern_default__1___closed__0 = (const lean_object*)&l_Lake_instInhabitedPattern_default__1___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedPattern_default__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPattern_default__1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedPattern_default__1___closed__1 = (const lean_object*)&l_Lake_instInhabitedPattern_default__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPattern___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPatternDescr_default__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPatternDescr_default__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPatternDescr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPatternDescr___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoePatternDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoePatternDescr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoePatternDescr___closed__0 = (const lean_object*)&l_Lake_instCoePatternDescr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instIsPatternPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instIsPatternPattern___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instIsPatternPattern___closed__0 = (const lean_object*)&l_Lake_instIsPatternPattern___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__0 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__0_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__1 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__1_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__2 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__2_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__3 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__3_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__4 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__4_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__5 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__5_value;
static const lean_closure_object l_Lake_PatternDescr_matches___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__6 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__6_value;
static const lean_ctor_object l_Lake_PatternDescr_matches___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__0_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__1_value)}};
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__7 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__7_value;
static const lean_ctor_object l_Lake_PatternDescr_matches___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__7_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__2_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__3_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__4_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__5_value)}};
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__8 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__8_value;
static const lean_ctor_object l_Lake_PatternDescr_matches___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__8_value),((lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__6_value)}};
static const lean_object* l_Lake_PatternDescr_matches___redArg___closed__9 = (const lean_object*)&l_Lake_PatternDescr_matches___redArg___closed__9_value;
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeForallBoolPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeForallBoolPattern___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeForallBoolPattern___closed__0 = (const lean_object*)&l_Lake_instCoeForallBoolPattern___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_PatternDescr_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PatternDescr_empty___closed__0 = (const lean_object*)&l_Lake_PatternDescr_empty___closed__0_value;
static const lean_ctor_object l_Lake_PatternDescr_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_empty___closed__0_value)}};
static const lean_object* l_Lake_PatternDescr_empty___closed__1 = (const lean_object*)&l_Lake_PatternDescr_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object*, lean_object*);
static const lean_string_object l_Lake_Pattern_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "empty"};
static const lean_object* l_Lake_Pattern_empty___closed__0 = (const lean_object*)&l_Lake_Pattern_empty___closed__0_value;
static const lean_ctor_object l_Lake_Pattern_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_empty___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 82, 154, 99, 191, 124, 127, 105)}};
static const lean_object* l_Lake_Pattern_empty___closed__1 = (const lean_object*)&l_Lake_Pattern_empty___closed__1_value;
static lean_once_cell_t l_Lake_Pattern_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___closed__2;
static lean_once_cell_t l_Lake_Pattern_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___closed__3;
static lean_once_cell_t l_Lake_Pattern_empty___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___closed__4;
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instEmptyCollectionPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instEmptyCollectionPattern___closed__0;
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_PatternDescr_star___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_empty___closed__0_value)}};
static const lean_object* l_Lake_PatternDescr_star___closed__0 = (const lean_object*)&l_Lake_PatternDescr_star___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_star___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_star___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Pattern_star___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Pattern_star___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Pattern_star___closed__0 = (const lean_object*)&l_Lake_Pattern_star___closed__0_value;
static const lean_string_object l_Lake_Pattern_star___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l_Lake_Pattern_star___closed__1 = (const lean_object*)&l_Lake_Pattern_star___closed__1_value;
static const lean_ctor_object l_Lake_Pattern_star___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_star___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 171, 138, 133, 66, 70, 83, 43)}};
static const lean_object* l_Lake_Pattern_star___closed__2 = (const lean_object*)&l_Lake_Pattern_star___closed__2_value;
static lean_once_cell_t l_Lake_Pattern_star___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___closed__3;
static lean_once_cell_t l_Lake_Pattern_star___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___closed__4;
static lean_once_cell_t l_Lake_Pattern_star___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___closed__5;
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_instInhabitedStrPatDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedStrPatDescr_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedStrPatDescr_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedStrPatDescr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedStrPatDescr_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedStrPatDescr_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedStrPatDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStrPatDescr_default = (const lean_object*)&l_Lake_instInhabitedStrPatDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStrPatDescr = (const lean_object*)&l_Lake_instInhabitedStrPatDescr_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_StrPatDescr_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instIsPatternStrPatDescrString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StrPatDescr_matches___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instIsPatternStrPatDescrString___closed__0 = (const lean_object*)&l_Lake_instIsPatternStrPatDescrString___closed__0_value;
static const lean_closure_object l_Lake_instIsPatternStrPatDescrString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_flip, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instIsPatternStrPatDescrString___closed__0_value)} };
static const lean_object* l_Lake_instIsPatternStrPatDescrString___closed__1 = (const lean_object*)&l_Lake_instIsPatternStrPatDescrString___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instIsPatternStrPatDescrString = (const lean_object*)&l_Lake_instIsPatternStrPatDescrString___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_StrPat_mem___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeArrayStringStrPatDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeArrayStringStrPatDescr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeArrayStringStrPatDescr___closed__0 = (const lean_object*)&l_Lake_instCoeArrayStringStrPatDescr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeArrayStringStrPatDescr = (const lean_object*)&l_Lake_instCoeArrayStringStrPatDescr___closed__0_value;
static const lean_closure_object l_Lake_instCoeArrayStringStrPat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StrPat_mem, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeArrayStringStrPat___closed__0 = (const lean_object*)&l_Lake_instCoeArrayStringStrPat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeArrayStringStrPat = (const lean_object*)&l_Lake_instCoeArrayStringStrPat___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object*);
LEAN_EXPORT uint8_t l_Lake_StrPat_beq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_StrPat_beq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lake_StrPat_beq___closed__0 = (const lean_object*)&l_Lake_StrPat_beq___closed__0_value;
static const lean_ctor_object l_Lake_StrPat_beq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_StrPat_beq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 198, 220, 8, 234, 83, 51, 77)}};
static const lean_object* l_Lake_StrPat_beq___closed__1 = (const lean_object*)&l_Lake_StrPat_beq___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object*);
static const lean_closure_object l_Lake_instCoeStringStrPatDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StrPatDescr_beq, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeStringStrPatDescr___closed__0 = (const lean_object*)&l_Lake_instCoeStringStrPatDescr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeStringStrPatDescr = (const lean_object*)&l_Lake_instCoeStringStrPatDescr___closed__0_value;
static const lean_closure_object l_Lake_instCoeStringStrPat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StrPat_beq, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeStringStrPat___closed__0 = (const lean_object*)&l_Lake_instCoeStringStrPat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeStringStrPat = (const lean_object*)&l_Lake_instCoeStringStrPat___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPathPatDescr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPathPatDescr_default___closed__0;
static lean_once_cell_t l_Lake_instInhabitedPathPatDescr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPathPatDescr_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPathPatDescr_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPathPatDescr;
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object*);
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PathPatDescr_matches___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instIsPatternPathPatDescrFilePath___closed__0 = (const lean_object*)&l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value;
static const lean_closure_object l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_flip, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instIsPatternPathPatDescrFilePath___closed__0_value)} };
static const lean_object* l_Lake_instIsPatternPathPatDescrFilePath___closed__1 = (const lean_object*)&l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instIsPatternPathPatDescrFilePath = (const lean_object*)&l_Lake_instIsPatternPathPatDescrFilePath___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_PathPat_path___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_isVerLike(lean_object*);
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object*);
static const lean_closure_object l_Lake_StrPat_verLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_isVerLike___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StrPat_verLike___closed__0 = (const lean_object*)&l_Lake_StrPat_verLike___closed__0_value;
static const lean_string_object l_Lake_StrPat_verLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verLike"};
static const lean_object* l_Lake_StrPat_verLike___closed__1 = (const lean_object*)&l_Lake_StrPat_verLike___closed__1_value;
static const lean_ctor_object l_Lake_StrPat_verLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_StrPat_verLike___closed__1_value),LEAN_SCALAR_PTR_LITERAL(106, 174, 94, 161, 245, 97, 255, 76)}};
static const lean_object* l_Lake_StrPat_verLike___closed__2 = (const lean_object*)&l_Lake_StrPat_verLike___closed__2_value;
static const lean_ctor_object l_Lake_StrPat_verLike___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_StrPat_verLike___closed__0_value),((lean_object*)&l_Lake_StrPat_verLike___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_StrPat_verLike___closed__3 = (const lean_object*)&l_Lake_StrPat_verLike___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_StrPat_verLike = (const lean_object*)&l_Lake_StrPat_verLike___closed__3_value;
static const lean_string_object l_Lake_defaultVersionTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lake_defaultVersionTags___closed__0 = (const lean_object*)&l_Lake_defaultVersionTags___closed__0_value;
static const lean_ctor_object l_Lake_defaultVersionTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_defaultVersionTags___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l_Lake_defaultVersionTags___closed__1 = (const lean_object*)&l_Lake_defaultVersionTags___closed__1_value;
static const lean_ctor_object l_Lake_defaultVersionTags___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_StrPat_verLike___closed__0_value),((lean_object*)&l_Lake_defaultVersionTags___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_defaultVersionTags___closed__2 = (const lean_object*)&l_Lake_defaultVersionTags___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_defaultVersionTags = (const lean_object*)&l_Lake_defaultVersionTags___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_versionTagPresets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionTagPresets___closed__0;
static lean_once_cell_t l_Lake_versionTagPresets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionTagPresets___closed__1;
LEAN_EXPORT lean_object* l_Lake_versionTagPresets;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__5));
v___x_39_ = l_String_toRawSubstring_x27(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(lean_object* v_x_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lake_term___x3d_x7e___00__closed__2));
lean_inc(v_x_58_);
v___x_62_ = l_Lean_Syntax_isOfKind(v_x_58_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_x_58_);
v___x_63_ = lean_box(1);
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_a_60_);
return v___x_64_;
}
else
{
lean_object* v_quotContext_65_; lean_object* v_currMacroScope_66_; lean_object* v_ref_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_quotContext_65_ = lean_ctor_get(v_a_59_, 1);
v_currMacroScope_66_ = lean_ctor_get(v_a_59_, 2);
v_ref_67_ = lean_ctor_get(v_a_59_, 5);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = l_Lean_Syntax_getArg(v_x_58_, v___x_68_);
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = l_Lean_Syntax_getArg(v_x_58_, v___x_70_);
lean_dec(v_x_58_);
v___x_72_ = 0;
v___x_73_ = l_Lean_SourceInfo_fromRef(v_ref_67_, v___x_72_);
v___x_74_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4));
v___x_75_ = lean_obj_once(&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6, &l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once, _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6);
v___x_76_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9));
lean_inc(v_currMacroScope_66_);
lean_inc(v_quotContext_65_);
v___x_77_ = l_Lean_addMacroScope(v_quotContext_65_, v___x_76_, v_currMacroScope_66_);
v___x_78_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12));
lean_inc_n(v___x_73_, 2);
v___x_79_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_79_, 0, v___x_73_);
lean_ctor_set(v___x_79_, 1, v___x_75_);
lean_ctor_set(v___x_79_, 2, v___x_77_);
lean_ctor_set(v___x_79_, 3, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14));
v___x_81_ = l_Lean_Syntax_node2(v___x_73_, v___x_80_, v___x_69_, v___x_71_);
v___x_82_ = l_Lean_Syntax_node2(v___x_73_, v___x_74_, v___x_79_, v___x_81_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_60_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___boxed(lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1(v_x_84_, v_a_85_, v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(lean_object* v_x_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4));
lean_inc(v_x_91_);
v___x_95_ = l_Lean_Syntax_isOfKind(v_x_91_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_x_91_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_93_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = l_Lean_Syntax_getArg(v_x_91_, v___x_98_);
v___x_100_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1));
lean_inc(v___x_99_);
v___x_101_ = l_Lean_Syntax_isOfKind(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v___x_99_);
lean_dec(v_x_91_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_a_93_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_91_, v___x_104_);
lean_dec(v_x_91_);
v___x_106_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_105_);
v___x_107_ = l_Lean_Syntax_matchesNull(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v___x_105_);
lean_dec(v___x_99_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_93_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_ref_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_110_ = l_Lean_Syntax_getArg(v___x_105_, v___x_98_);
v___x_111_ = l_Lean_Syntax_getArg(v___x_105_, v___x_104_);
lean_dec(v___x_105_);
v_ref_112_ = l_Lean_replaceRef(v___x_99_, v_a_92_);
lean_dec(v___x_99_);
v___x_113_ = 0;
v___x_114_ = l_Lean_SourceInfo_fromRef(v_ref_112_, v___x_113_);
lean_dec(v_ref_112_);
v___x_115_ = ((lean_object*)(l_Lake_term___x3d_x7e___00__closed__2));
v___x_116_ = ((lean_object*)(l_Lake_term___x3d_x7e___00__closed__5));
lean_inc(v___x_114_);
v___x_117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_114_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Lean_Syntax_node3(v___x_114_, v___x_115_, v___x_110_, v___x_117_, v___x_111_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_93_);
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___boxed(lean_object* v_x_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(v_x_120_, v_a_121_, v_a_122_);
lean_dec(v_a_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg(lean_object* v_x_124_){
_start:
{
switch(lean_obj_tag(v_x_124_))
{
case 0:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(0u);
return v___x_125_;
}
case 1:
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(1u);
return v___x_126_;
}
case 2:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(2u);
return v___x_127_;
}
default: 
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(3u);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg___boxed(lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_129_);
lean_dec_ref(v_x_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___boxed(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_PatternDescr_ctorIdx(v_00_u03b1_135_, v_00_u03b2_136_, v_x_137_);
lean_dec_ref(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___redArg(lean_object* v_t_139_, lean_object* v_k_140_){
_start:
{
if (lean_obj_tag(v_t_139_) == 3)
{
lean_object* v_p_141_; lean_object* v___x_142_; 
v_p_141_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_p_141_);
lean_dec_ref(v_t_139_);
v___x_142_ = lean_apply_1(v_k_140_, v_p_141_);
return v___x_142_;
}
else
{
lean_object* v_p_143_; lean_object* v___x_144_; 
v_p_143_ = lean_ctor_get(v_t_139_, 0);
lean_inc_ref(v_p_143_);
lean_dec_ref(v_t_139_);
v___x_144_ = lean_apply_1(v_k_140_, v_p_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_motive__2_147_, lean_object* v_ctorIdx_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_k_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_149_, v_k_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___boxed(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_motive__2_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_PatternDescr_ctorElim(v_00_u03b1_153_, v_00_u03b2_154_, v_motive__2_155_, v_ctorIdx_156_, v_t_157_, v_h_158_, v_k_159_);
lean_dec(v_ctorIdx_156_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim___redArg(lean_object* v_t_161_, lean_object* v_not_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_161_, v_not_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b2_165_, lean_object* v_motive__2_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_not_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_167_, v_not_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim___redArg(lean_object* v_t_171_, lean_object* v_all_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_171_, v_all_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_motive__2_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_all_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_177_, v_all_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim___redArg(lean_object* v_t_181_, lean_object* v_any_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_181_, v_any_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_motive__2_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_any_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_187_, v_any_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim___redArg(lean_object* v_t_191_, lean_object* v_coe_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_191_, v_coe_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim(lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_motive__2_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_coe_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_197_, v_coe_199_);
return v___x_200_;
}
}
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___lam__0(lean_object* v_x_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___lam__0___boxed(lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lake_instInhabitedPattern_default__1___lam__0(v_x_203_);
lean_dec(v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___closed__1));
return v___x_213_;
}
}
static lean_object* _init_l_Lake_instInhabitedPattern___closed__0(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lake_instInhabitedPattern___closed__0, &l_Lake_instInhabitedPattern___closed__0_once, _init_l_Lake_instInhabitedPattern___closed__0);
return v___x_217_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lake_instInhabitedPattern___closed__0, &l_Lake_instInhabitedPattern___closed__0_once, _init_l_Lake_instInhabitedPattern___closed__0);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_222_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lake_instInhabitedPatternDescr_default__1(lean_box(0), lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr___closed__0, &l_Lake_instInhabitedPatternDescr___closed__0_once, _init_l_Lake_instInhabitedPatternDescr___closed__0);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___lam__0(lean_object* v_p_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_228_, 0, v_p_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object* v_00_u03b2_230_, lean_object* v_00_u03b1_231_){
_start:
{
lean_object* v___f_232_; 
v___f_232_ = ((lean_object*)(l_Lake_instCoePatternDescr___closed__0));
return v___f_232_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object* v_a_233_, lean_object* v_self_234_){
_start:
{
lean_object* v_filter_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_filter_235_ = lean_ctor_get(v_self_234_, 0);
lean_inc_ref(v_filter_235_);
lean_dec_ref(v_self_234_);
v___x_236_ = lean_apply_1(v_filter_235_, v_a_233_);
v___x_237_ = lean_unbox(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object* v_a_238_, lean_object* v_self_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lake_Pattern_matches___redArg(v_a_238_, v_self_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_a_244_, lean_object* v_self_245_){
_start:
{
lean_object* v_filter_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_filter_246_ = lean_ctor_get(v_self_245_, 0);
lean_inc_ref(v_filter_246_);
lean_dec_ref(v_self_245_);
v___x_247_ = lean_apply_1(v_filter_246_, v_a_244_);
v___x_248_ = lean_unbox(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_a_251_, lean_object* v_self_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lake_Pattern_matches(v_00_u03b1_249_, v_00_u03b2_250_, v_a_251_, v_self_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___lam__0(lean_object* v_self_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_filter_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_filter_257_ = lean_ctor_get(v_self_255_, 0);
lean_inc_ref(v_filter_257_);
lean_dec_ref(v_self_255_);
v___x_258_ = lean_apply_1(v_filter_257_, v___y_256_);
v___x_259_ = lean_unbox(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___lam__0___boxed(lean_object* v_self_260_, lean_object* v___y_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lake_instIsPatternPattern___lam__0(v_self_260_, v___y_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object* v_00_u03b1_265_, lean_object* v_00_u03b2_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = ((lean_object*)(l_Lake_instIsPatternPattern___closed__0));
return v___f_267_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object* v_val_268_, uint8_t v___x_269_, lean_object* v_v_270_){
_start:
{
lean_object* v_filter_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_filter_271_ = lean_ctor_get(v_v_270_, 0);
lean_inc_ref(v_filter_271_);
lean_dec_ref(v_v_270_);
v___x_272_ = lean_apply_1(v_filter_271_, v_val_268_);
v___x_273_ = lean_unbox(v___x_272_);
if (v___x_273_ == 0)
{
return v___x_269_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object* v_val_275_, lean_object* v___x_276_, lean_object* v_v_277_){
_start:
{
uint8_t v___x_220__boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v___x_220__boxed_278_ = lean_unbox(v___x_276_);
v_res_279_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_275_, v___x_220__boxed_278_, v_v_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object* v_val_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_filter_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_filter_283_ = lean_ctor_get(v_x_282_, 0);
lean_inc_ref(v_filter_283_);
lean_dec_ref(v_x_282_);
v___x_284_ = lean_apply_1(v_filter_283_, v_val_281_);
v___x_285_ = lean_unbox(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object* v_val_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_286_, v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg(lean_object* v_inst_309_, lean_object* v_val_310_, lean_object* v_self_311_){
_start:
{
switch(lean_obj_tag(v_self_311_))
{
case 0:
{
lean_object* v_p_312_; lean_object* v_filter_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_dec_ref(v_inst_309_);
v_p_312_ = lean_ctor_get(v_self_311_, 0);
lean_inc_ref(v_p_312_);
lean_dec_ref(v_self_311_);
v_filter_313_ = lean_ctor_get(v_p_312_, 0);
lean_inc_ref(v_filter_313_);
lean_dec_ref(v_p_312_);
v___x_314_ = lean_apply_1(v_filter_313_, v_val_310_);
v___x_315_ = lean_unbox(v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 1;
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
}
case 1:
{
lean_object* v_ps_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
lean_dec_ref(v_inst_309_);
v_ps_318_ = lean_ctor_get(v_self_311_, 0);
lean_inc_ref(v_ps_318_);
lean_dec_ref(v_self_311_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_get_size(v_ps_318_);
v___x_321_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_322_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
lean_dec_ref(v_ps_318_);
lean_dec(v_val_310_);
v___x_323_ = 1;
return v___x_323_;
}
else
{
if (v___x_322_ == 0)
{
lean_dec_ref(v_ps_318_);
lean_dec(v_val_310_);
return v___x_322_;
}
else
{
lean_object* v___x_324_; lean_object* v___f_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_324_ = lean_box(v___x_322_);
v___f_325_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_325_, 0, v_val_310_);
lean_closure_set(v___f_325_, 1, v___x_324_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_320_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_321_, v___f_325_, v_ps_318_, v___x_326_, v___x_327_);
v___x_329_ = lean_unbox(v___x_328_);
lean_dec(v___x_328_);
if (v___x_329_ == 0)
{
return v___x_322_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
}
}
}
case 2:
{
lean_object* v_ps_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
lean_dec_ref(v_inst_309_);
v_ps_331_ = lean_ctor_get(v_self_311_, 0);
lean_inc_ref(v_ps_331_);
lean_dec_ref(v_self_311_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_array_get_size(v_ps_331_);
v___x_334_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_335_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
if (v___x_335_ == 0)
{
lean_dec_ref(v_ps_331_);
lean_dec(v_val_310_);
return v___x_335_;
}
else
{
if (v___x_335_ == 0)
{
lean_dec_ref(v_ps_331_);
lean_dec(v_val_310_);
return v___x_335_;
}
else
{
lean_object* v___f_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___f_336_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_336_, 0, v_val_310_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_333_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_334_, v___f_336_, v_ps_331_, v___x_337_, v___x_338_);
v___x_340_ = lean_unbox(v___x_339_);
lean_dec(v___x_339_);
return v___x_340_;
}
}
}
default: 
{
lean_object* v_p_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_p_341_ = lean_ctor_get(v_self_311_, 0);
lean_inc(v_p_341_);
lean_dec_ref(v_self_311_);
v___x_342_ = lean_apply_2(v_inst_309_, v_p_341_, v_val_310_);
v___x_343_ = lean_unbox(v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object* v_inst_344_, lean_object* v_val_345_, lean_object* v_self_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lake_PatternDescr_matches___redArg(v_inst_344_, v_val_345_, v_self_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches(lean_object* v_00_u03b2_349_, lean_object* v_00_u03b1_350_, lean_object* v_inst_351_, lean_object* v_val_352_, lean_object* v_self_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = l_Lake_PatternDescr_matches___redArg(v_inst_351_, v_val_352_, v_self_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object* v_00_u03b2_355_, lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_val_358_, lean_object* v_self_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lake_PatternDescr_matches(v_00_u03b2_355_, v_00_u03b1_356_, v_inst_357_, v_val_358_, v_self_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object* v_inst_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___boxed), 5, 3);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, lean_box(0));
lean_closure_set(v___x_363_, 2, v_inst_362_);
v___x_364_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_364_, 0, lean_box(0));
lean_closure_set(v___x_364_, 1, lean_box(0));
lean_closure_set(v___x_364_, 2, lean_box(0));
lean_closure_set(v___x_364_, 3, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object* v_00_u03b2_365_, lean_object* v_00_u03b1_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object* v_f_369_, lean_object* v_name_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v_f_369_);
lean_ctor_set(v___x_372_, 1, v_name_370_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object* v_00_u03b1_373_, lean_object* v_00_u03b2_374_, lean_object* v_f_375_, lean_object* v_name_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v_f_375_);
lean_ctor_set(v___x_378_, 1, v_name_376_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___lam__0(lean_object* v_f_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_382_, 0, v_f_379_);
lean_ctor_set(v___x_382_, 1, v___x_380_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_){
_start:
{
lean_object* v___f_386_; 
v___f_386_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___closed__0));
return v___f_386_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object* v_inst_387_, lean_object* v_descr_388_, lean_object* v_x_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = l_Lake_PatternDescr_matches___redArg(v_inst_387_, v_x_389_, v_descr_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object* v_inst_391_, lean_object* v_descr_392_, lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_391_, v_descr_392_, v_x_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object* v_inst_396_, lean_object* v_descr_397_, lean_object* v_name_398_){
_start:
{
lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc_ref(v_descr_397_);
v___f_399_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_399_, 0, v_inst_396_);
lean_closure_set(v___f_399_, 1, v_descr_397_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_descr_397_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v___f_399_);
lean_ctor_set(v___x_401_, 1, v_name_398_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object* v_00_u03b2_402_, lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_descr_405_, lean_object* v_name_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc_ref(v_descr_405_);
v___f_407_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_407_, 0, v_inst_404_);
lean_closure_set(v___f_407_, 1, v_descr_405_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_descr_405_);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v___f_407_);
lean_ctor_set(v___x_409_, 1, v_name_406_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object* v_inst_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = l_Lake_PatternDescr_matches___redArg(v_inst_410_, v_x_412_, v_x_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object* v_inst_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_414_, v_x_415_, v_x_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object* v_inst_419_, lean_object* v_x_420_){
_start:
{
lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc_ref(v_x_420_);
v___f_421_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_421_, 0, v_inst_419_);
lean_closure_set(v___f_421_, 1, v_x_420_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v_x_420_);
v___x_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_424_, 0, v___f_421_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object* v_inst_425_){
_start:
{
lean_object* v___f_426_; 
v___f_426_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_426_, 0, v_inst_425_);
return v___f_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object* v_00_u03b2_427_, lean_object* v_00_u03b1_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v___f_430_; 
v___f_430_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_430_, 0, v_inst_429_);
return v___f_430_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object* v_inst_431_, lean_object* v___x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lake_PatternDescr_matches___redArg(v_inst_431_, v_x_433_, v___x_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object* v_inst_435_, lean_object* v___x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_435_, v___x_436_, v_x_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object* v_inst_440_, lean_object* v_p_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_p_441_);
lean_inc_ref(v___x_442_);
v___f_443_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_443_, 0, v_inst_440_);
lean_closure_set(v___f_443_, 1, v___x_442_);
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_442_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___f_443_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object* v_00_u03b2_447_, lean_object* v_00_u03b1_448_, lean_object* v_inst_449_, lean_object* v_p_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_p_450_);
lean_inc_ref(v___x_451_);
v___f_452_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_452_, 0, v_inst_449_);
lean_closure_set(v___f_452_, 1, v___x_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_451_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v___f_452_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object* v_inst_456_, lean_object* v_ps_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_ps_457_);
lean_inc_ref(v___x_458_);
v___f_459_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_459_, 0, v_inst_456_);
lean_closure_set(v___f_459_, 1, v___x_458_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_458_);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v___f_459_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object* v_00_u03b2_463_, lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_ps_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_ps_466_);
lean_inc_ref(v___x_467_);
v___f_468_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_468_, 0, v_inst_465_);
lean_closure_set(v___f_468_, 1, v___x_467_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_467_);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v___f_468_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object* v_inst_472_, lean_object* v_ps_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_474_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_474_, 0, v_ps_473_);
lean_inc_ref(v___x_474_);
v___f_475_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_475_, 0, v_inst_472_);
lean_closure_set(v___f_475_, 1, v___x_474_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_474_);
v___x_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_478_, 0, v___f_475_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object* v_00_u03b2_479_, lean_object* v_00_u03b1_480_, lean_object* v_inst_481_, lean_object* v_ps_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_483_, 0, v_ps_482_);
lean_inc_ref(v___x_483_);
v___f_484_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_484_, 0, v_inst_481_);
lean_closure_set(v___f_484_, 1, v___x_483_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_483_);
v___x_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_487_, 0, v___f_484_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Lake_PatternDescr_empty___closed__1));
return v___x_494_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__2(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lake_PatternDescr_empty(lean_box(0), lean_box(0));
return v___x_498_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__3(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_obj_once(&l_Lake_Pattern_empty___closed__2, &l_Lake_Pattern_empty___closed__2_once, _init_l_Lake_Pattern_empty___closed__2);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__4(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; 
v___x_501_ = lean_obj_once(&l_Lake_Pattern_empty___closed__3, &l_Lake_Pattern_empty___closed__3_once, _init_l_Lake_Pattern_empty___closed__3);
v___x_502_ = ((lean_object*)(l_Lake_Pattern_empty___closed__1));
v___f_503_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___closed__0));
v___x_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_504_, 0, v___f_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
lean_ctor_set(v___x_504_, 2, v___x_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lake_Pattern_empty___closed__4, &l_Lake_Pattern_empty___closed__4_once, _init_l_Lake_Pattern_empty___closed__4);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lake_Pattern_empty___closed__2, &l_Lake_Pattern_empty___closed__2_once, _init_l_Lake_Pattern_empty___closed__2);
return v___x_510_;
}
}
static lean_object* _init_l_Lake_instEmptyCollectionPattern___closed__0(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lake_Pattern_empty(lean_box(0), lean_box(0));
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Lake_instEmptyCollectionPattern___closed__0, &l_Lake_instEmptyCollectionPattern___closed__0_once, _init_l_Lake_instEmptyCollectionPattern___closed__0);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l_Lake_PatternDescr_star___closed__0));
return v___x_519_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_star___lam__0(lean_object* v_x_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = 1;
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___lam__0___boxed(lean_object* v_x_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Lake_Pattern_star___lam__0(v_x_522_);
lean_dec(v_x_522_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__3(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lake_PatternDescr_star(lean_box(0), lean_box(0));
return v___x_529_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__4(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lake_Pattern_star___closed__3, &l_Lake_Pattern_star___closed__3_once, _init_l_Lake_Pattern_star___closed__3);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
v___x_532_ = lean_obj_once(&l_Lake_Pattern_star___closed__4, &l_Lake_Pattern_star___closed__4_once, _init_l_Lake_Pattern_star___closed__4);
v___x_533_ = ((lean_object*)(l_Lake_Pattern_star___closed__2));
v___f_534_ = ((lean_object*)(l_Lake_Pattern_star___closed__0));
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v___f_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
lean_ctor_set(v___x_535_, 2, v___x_532_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lake_Pattern_star___closed__5, &l_Lake_Pattern_star___closed__5_once, _init_l_Lake_Pattern_star___closed__5);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx(lean_object* v_x_539_){
_start:
{
switch(lean_obj_tag(v_x_539_))
{
case 0:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(0u);
return v___x_540_;
}
case 1:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(1u);
return v___x_541_;
}
default: 
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(2u);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___boxed(lean_object* v_x_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lake_StrPatDescr_ctorIdx(v_x_543_);
lean_dec_ref(v_x_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object* v_t_545_, lean_object* v_k_546_){
_start:
{
lean_object* v_xs_547_; lean_object* v___x_548_; 
v_xs_547_ = lean_ctor_get(v_t_545_, 0);
lean_inc_ref(v_xs_547_);
lean_dec_ref(v_t_545_);
v___x_548_ = lean_apply_1(v_k_546_, v_xs_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object* v_motive_549_, lean_object* v_ctorIdx_550_, lean_object* v_t_551_, lean_object* v_h_552_, lean_object* v_k_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_551_, v_k_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object* v_motive_555_, lean_object* v_ctorIdx_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_k_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lake_StrPatDescr_ctorElim(v_motive_555_, v_ctorIdx_556_, v_t_557_, v_h_558_, v_k_559_);
lean_dec(v_ctorIdx_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object* v_t_561_, lean_object* v_mem_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_561_, v_mem_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_mem_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_565_, v_mem_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object* v_t_569_, lean_object* v_startsWith_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_569_, v_startsWith_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_startsWith_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_573_, v_startsWith_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object* v_t_577_, lean_object* v_endsWith_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_577_, v_endsWith_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_endsWith_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_581_, v_endsWith_583_);
return v___x_584_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object* v_a_591_, lean_object* v_as_592_, size_t v_i_593_, size_t v_stop_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_eq(v_i_593_, v_stop_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_array_uget_borrowed(v_as_592_, v_i_593_);
v___x_597_ = lean_string_dec_eq(v_a_591_, v___x_596_);
if (v___x_597_ == 0)
{
size_t v___x_598_; size_t v___x_599_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_add(v_i_593_, v___x_598_);
v_i_593_ = v___x_599_;
goto _start;
}
else
{
return v___x_597_;
}
}
else
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object* v_a_602_, lean_object* v_as_603_, lean_object* v_i_604_, lean_object* v_stop_605_){
_start:
{
size_t v_i_boxed_606_; size_t v_stop_boxed_607_; uint8_t v_res_608_; lean_object* v_r_609_; 
v_i_boxed_606_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_stop_boxed_607_ = lean_unbox_usize(v_stop_605_);
lean_dec(v_stop_605_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_602_, v_as_603_, v_i_boxed_606_, v_stop_boxed_607_);
lean_dec_ref(v_as_603_);
lean_dec_ref(v_a_602_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object* v_as_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_array_get_size(v_as_610_);
v___x_614_ = lean_nat_dec_lt(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
return v___x_614_;
}
else
{
if (v___x_614_ == 0)
{
return v___x_614_;
}
else
{
size_t v___x_615_; size_t v___x_616_; uint8_t v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_613_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_611_, v_as_610_, v___x_615_, v___x_616_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object* v_as_618_, lean_object* v_a_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_618_, v_a_619_);
lean_dec_ref(v_a_619_);
lean_dec_ref(v_as_618_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPatDescr_matches(lean_object* v_s_622_, lean_object* v_self_623_){
_start:
{
switch(lean_obj_tag(v_self_623_))
{
case 0:
{
lean_object* v_xs_624_; uint8_t v___x_625_; 
v_xs_624_ = lean_ctor_get(v_self_623_, 0);
v___x_625_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_624_, v_s_622_);
return v___x_625_;
}
case 1:
{
lean_object* v_affix_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_affix_626_ = lean_ctor_get(v_self_623_, 0);
v___x_627_ = lean_string_utf8_byte_size(v_s_622_);
v___x_628_ = lean_string_utf8_byte_size(v_affix_626_);
v___x_629_ = lean_nat_dec_le(v___x_628_, v___x_627_);
if (v___x_629_ == 0)
{
return v___x_629_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_string_memcmp(v_s_622_, v_affix_626_, v___x_630_, v___x_630_, v___x_628_);
return v___x_631_;
}
}
default: 
{
lean_object* v_affix_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_affix_632_ = lean_ctor_get(v_self_623_, 0);
v___x_633_ = lean_string_utf8_byte_size(v_s_622_);
v___x_634_ = lean_string_utf8_byte_size(v_affix_632_);
v___x_635_ = lean_nat_dec_le(v___x_634_, v___x_633_);
if (v___x_635_ == 0)
{
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_nat_sub(v___x_633_, v___x_634_);
v___x_638_ = lean_string_memcmp(v_s_622_, v_affix_632_, v___x_637_, v___x_636_, v___x_634_);
lean_dec(v___x_637_);
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object* v_s_639_, lean_object* v_self_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lake_StrPatDescr_matches(v_s_639_, v_self_640_);
lean_dec_ref(v_self_640_);
lean_dec_ref(v_s_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_mem___lam__0(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = l_Lake_PatternDescr_matches___redArg(v___x_647_, v_x_649_, v___x_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_x_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lake_StrPat_mem___lam__0(v___x_651_, v___x_652_, v_x_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object* v_xs_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_657_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_xs_656_);
v___x_659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_inc_ref(v___x_659_);
v___f_660_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_660_, 0, v___x_657_);
lean_closure_set(v___f_660_, 1, v___x_659_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_659_);
v___x_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_663_, 0, v___f_660_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object* v_xs_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_xs_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object* v_affix_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_671_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_affix_670_);
v___x_673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_inc_ref(v___x_673_);
v___f_674_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_674_, 0, v___x_671_);
lean_closure_set(v___f_674_, 1, v___x_673_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
v___x_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_677_, 0, v___f_674_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object* v_affix_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_679_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_680_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_680_, 0, v_affix_678_);
v___x_681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_inc_ref(v___x_681_);
v___f_682_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_682_, 0, v___x_679_);
lean_closure_set(v___f_682_, 1, v___x_681_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_681_);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v___f_682_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object* v_s_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_689_ = lean_array_push(v___x_688_, v_s_686_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_beq___lam__0(lean_object* v_s_691_, lean_object* v_x_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = lean_string_dec_eq(v_x_692_, v_s_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object* v_s_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Lake_StrPat_beq___lam__0(v_s_694_, v_x_695_);
lean_dec_ref(v_x_695_);
lean_dec_ref(v_s_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object* v_s_701_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref(v_s_701_);
v___f_702_ = lean_alloc_closure((void*)(l_Lake_StrPat_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_702_, 0, v_s_701_);
v___x_703_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_704_ = l_Lake_StrPatDescr_beq(v_s_701_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_707_, 0, v___f_702_);
lean_ctor_set(v___x_707_, 1, v___x_703_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx(lean_object* v_x_712_){
_start:
{
switch(lean_obj_tag(v_x_712_))
{
case 0:
{
lean_object* v___x_713_; 
v___x_713_ = lean_unsigned_to_nat(0u);
return v___x_713_;
}
case 1:
{
lean_object* v___x_714_; 
v___x_714_ = lean_unsigned_to_nat(1u);
return v___x_714_;
}
default: 
{
lean_object* v___x_715_; 
v___x_715_ = lean_unsigned_to_nat(2u);
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___boxed(lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_PathPatDescr_ctorIdx(v_x_716_);
lean_dec_ref(v_x_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object* v_t_718_, lean_object* v_k_719_){
_start:
{
lean_object* v_p_720_; lean_object* v___x_721_; 
v_p_720_ = lean_ctor_get(v_t_718_, 0);
lean_inc_ref(v_p_720_);
lean_dec_ref(v_t_718_);
v___x_721_ = lean_apply_1(v_k_719_, v_p_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object* v_motive_722_, lean_object* v_ctorIdx_723_, lean_object* v_t_724_, lean_object* v_h_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_724_, v_k_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object* v_motive_728_, lean_object* v_ctorIdx_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_k_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lake_PathPatDescr_ctorElim(v_motive_728_, v_ctorIdx_729_, v_t_730_, v_h_731_, v_k_732_);
lean_dec(v_ctorIdx_729_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object* v_t_734_, lean_object* v_path_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_734_, v_path_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object* v_motive_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_path_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_738_, v_path_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object* v_t_742_, lean_object* v_extension_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_742_, v_extension_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object* v_motive_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_extension_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_746_, v_extension_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object* v_t_750_, lean_object* v_fileName_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_750_, v_fileName_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object* v_motive_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_fileName_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_754_, v_fileName_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__0(void){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return v___x_758_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__0, &l_Lake_instInhabitedPathPatDescr_default___closed__0_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__0);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default(void){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__1, &l_Lake_instInhabitedPathPatDescr_default___closed__1_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__1);
return v___x_761_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lake_instInhabitedPathPatDescr_default;
return v___x_762_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object* v_p_763_, lean_object* v_x_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_string_dec_eq(v_x_764_, v_p_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object* v_p_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lake_PathPatDescr_eq___lam__0(v_p_766_, v_x_767_);
lean_dec_ref(v_x_767_);
lean_dec_ref(v_p_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object* v_p_770_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc_ref(v_p_770_);
v___f_771_ = lean_alloc_closure((void*)(l_Lake_PathPatDescr_eq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_771_, 0, v_p_770_);
v___x_772_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_773_ = l_Lake_StrPatDescr_beq(v_p_770_);
v___x_774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_776_, 0, v___f_771_);
lean_ctor_set(v___x_776_, 1, v___x_772_);
lean_ctor_set(v___x_776_, 2, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_matches(lean_object* v_path_778_, lean_object* v_self_779_){
_start:
{
switch(lean_obj_tag(v_self_779_))
{
case 0:
{
lean_object* v_p_780_; lean_object* v_filter_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_p_780_ = lean_ctor_get(v_self_779_, 0);
lean_inc_ref(v_p_780_);
lean_dec_ref(v_self_779_);
v_filter_781_ = lean_ctor_get(v_p_780_, 0);
lean_inc_ref(v_filter_781_);
lean_dec_ref(v_p_780_);
v___x_782_ = l_System_FilePath_normalize(v_path_778_);
v___x_783_ = lean_apply_1(v_filter_781_, v___x_782_);
v___x_784_ = lean_unbox(v___x_783_);
return v___x_784_;
}
case 1:
{
lean_object* v_p_785_; lean_object* v___x_786_; 
v_p_785_ = lean_ctor_get(v_self_779_, 0);
lean_inc_ref(v_p_785_);
lean_dec_ref(v_self_779_);
v___x_786_ = l_System_FilePath_extension(v_path_778_);
if (lean_obj_tag(v___x_786_) == 0)
{
uint8_t v___x_787_; 
lean_dec_ref(v_p_785_);
v___x_787_ = 0;
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v_filter_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_val_788_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v___x_786_);
v_filter_789_ = lean_ctor_get(v_p_785_, 0);
lean_inc_ref(v_filter_789_);
lean_dec_ref(v_p_785_);
v___x_790_ = lean_apply_1(v_filter_789_, v_val_788_);
v___x_791_ = lean_unbox(v___x_790_);
return v___x_791_;
}
}
default: 
{
lean_object* v_p_792_; lean_object* v___x_793_; 
v_p_792_ = lean_ctor_get(v_self_779_, 0);
lean_inc_ref(v_p_792_);
lean_dec_ref(v_self_779_);
v___x_793_ = l_System_FilePath_fileName(v_path_778_);
if (lean_obj_tag(v___x_793_) == 0)
{
uint8_t v___x_794_; 
lean_dec_ref(v_p_792_);
v___x_794_ = 0;
return v___x_794_;
}
else
{
lean_object* v_val_795_; lean_object* v_filter_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_val_795_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_795_);
lean_dec_ref(v___x_793_);
v_filter_796_ = lean_ctor_get(v_p_792_, 0);
lean_inc_ref(v_filter_796_);
lean_dec_ref(v_p_792_);
v___x_797_ = lean_apply_1(v_filter_796_, v_val_795_);
v___x_798_ = lean_unbox(v___x_797_);
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object* v_path_799_, lean_object* v_self_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Lake_PathPatDescr_matches(v_path_799_, v_self_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPat_path___lam__0(lean_object* v___x_807_, lean_object* v___x_808_, lean_object* v_x_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lake_PatternDescr_matches___redArg(v___x_807_, v_x_809_, v___x_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_x_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Lake_PathPat_path___lam__0(v___x_811_, v___x_812_, v_x_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object* v_p_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_817_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v_p_816_);
v___x_819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_inc_ref(v___x_819_);
v___f_820_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_820_, 0, v___x_817_);
lean_closure_set(v___f_820_, 1, v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_819_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___f_820_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object* v_p_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_825_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_p_824_);
v___x_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_inc_ref(v___x_827_);
v___f_828_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_828_, 0, v___x_825_);
lean_closure_set(v___f_828_, 1, v___x_827_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_827_);
v___x_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_831_, 0, v___f_828_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object* v_p_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_833_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_834_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_834_, 0, v_p_832_);
v___x_835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_inc_ref(v___x_835_);
v___f_836_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_836_, 0, v___x_833_);
lean_closure_set(v___f_836_, 1, v___x_835_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_835_);
v___x_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_839_, 0, v___f_836_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_h__1_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_h__1_842_, v_x_840_, v_x_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_h__1_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lean_apply_2(v_h__1_847_, v_x_845_, v_x_846_);
return v___x_848_;
}
}
LEAN_EXPORT uint8_t l_Lake_isVerLike(lean_object* v_s_849_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = lean_unsigned_to_nat(2u);
v___x_851_ = lean_string_utf8_byte_size(v_s_849_);
v___x_852_ = lean_nat_dec_le(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
return v___x_852_;
}
else
{
lean_object* v___x_853_; uint32_t v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_string_utf8_get_fast(v_s_849_, v___x_853_);
v___x_855_ = 118;
v___x_856_ = lean_uint32_dec_eq(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
return v___x_856_;
}
else
{
lean_object* v___x_857_; uint32_t v___x_858_; uint32_t v___x_859_; uint8_t v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_string_utf8_get_fast(v_s_849_, v___x_857_);
v___x_859_ = 48;
v___x_860_ = lean_uint32_dec_le(v___x_859_, v___x_858_);
if (v___x_860_ == 0)
{
return v___x_860_;
}
else
{
uint32_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 57;
v___x_862_ = lean_uint32_dec_le(v___x_858_, v___x_861_);
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object* v_s_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lake_isVerLike(v_s_863_);
lean_dec_ref(v_s_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object* v_k_883_, lean_object* v_v_884_, lean_object* v_t_885_){
_start:
{
if (lean_obj_tag(v_t_885_) == 0)
{
lean_object* v_size_886_; lean_object* v_k_887_; lean_object* v_v_888_; lean_object* v_l_889_; lean_object* v_r_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_1170_; 
v_size_886_ = lean_ctor_get(v_t_885_, 0);
v_k_887_ = lean_ctor_get(v_t_885_, 1);
v_v_888_ = lean_ctor_get(v_t_885_, 2);
v_l_889_ = lean_ctor_get(v_t_885_, 3);
v_r_890_ = lean_ctor_get(v_t_885_, 4);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_t_885_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_892_ = v_t_885_;
v_isShared_893_ = v_isSharedCheck_1170_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_r_890_);
lean_inc(v_l_889_);
lean_inc(v_v_888_);
lean_inc(v_k_887_);
lean_inc(v_size_886_);
lean_dec(v_t_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_1170_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_883_, v_k_887_);
switch(v___x_894_)
{
case 0:
{
lean_object* v_impl_895_; lean_object* v___x_896_; 
lean_dec(v_size_886_);
v_impl_895_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_883_, v_v_884_, v_l_889_);
v___x_896_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_890_) == 0)
{
lean_object* v_size_897_; lean_object* v_size_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_l_901_; lean_object* v_r_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_size_897_ = lean_ctor_get(v_r_890_, 0);
v_size_898_ = lean_ctor_get(v_impl_895_, 0);
lean_inc(v_size_898_);
v_k_899_ = lean_ctor_get(v_impl_895_, 1);
lean_inc(v_k_899_);
v_v_900_ = lean_ctor_get(v_impl_895_, 2);
lean_inc(v_v_900_);
v_l_901_ = lean_ctor_get(v_impl_895_, 3);
lean_inc(v_l_901_);
v_r_902_ = lean_ctor_get(v_impl_895_, 4);
lean_inc(v_r_902_);
v___x_903_ = lean_unsigned_to_nat(3u);
v___x_904_ = lean_nat_mul(v___x_903_, v_size_897_);
v___x_905_ = lean_nat_dec_lt(v___x_904_, v_size_898_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_r_902_);
lean_dec(v_l_901_);
lean_dec(v_v_900_);
lean_dec(v_k_899_);
v___x_906_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_907_ = lean_nat_add(v___x_906_, v_size_897_);
lean_dec(v___x_906_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 3, v_impl_895_);
lean_ctor_set(v___x_892_, 0, v___x_907_);
v___x_909_ = v___x_892_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_impl_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_r_890_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_977_ = lean_ctor_get(v_impl_895_, 4);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_impl_895_, 2);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_impl_895_, 1);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_981_);
v___x_912_ = v_impl_895_;
v_isShared_913_ = v_isSharedCheck_976_;
goto v_resetjp_911_;
}
else
{
lean_dec(v_impl_895_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_976_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_size_914_; lean_object* v_size_915_; lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v_l_918_; lean_object* v_r_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_size_914_ = lean_ctor_get(v_l_901_, 0);
v_size_915_ = lean_ctor_get(v_r_902_, 0);
v_k_916_ = lean_ctor_get(v_r_902_, 1);
v_v_917_ = lean_ctor_get(v_r_902_, 2);
v_l_918_ = lean_ctor_get(v_r_902_, 3);
v_r_919_ = lean_ctor_get(v_r_902_, 4);
v___x_920_ = lean_unsigned_to_nat(2u);
v___x_921_ = lean_nat_mul(v___x_920_, v_size_914_);
v___x_922_ = lean_nat_dec_lt(v_size_915_, v___x_921_);
lean_dec(v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_r_919_);
lean_inc(v_l_918_);
lean_inc(v_v_917_);
lean_inc(v_k_916_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_r_902_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_r_902_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_r_902_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_902_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_902_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_902_, 0);
lean_dec(v_unused_956_);
v___x_924_ = v_r_902_;
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_r_902_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___x_939_; lean_object* v___y_941_; 
v___x_926_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_927_ = lean_nat_add(v___x_926_, v_size_897_);
lean_dec(v___x_926_);
v___x_939_ = lean_nat_add(v___x_896_, v_size_914_);
if (lean_obj_tag(v_l_918_) == 0)
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_l_918_, 0);
lean_inc(v_size_949_);
v___y_941_ = v_size_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_941_ = v___x_950_;
goto v___jp_940_;
}
v___jp_928_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_nat_add(v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 4, v_r_890_);
lean_ctor_set(v___x_924_, 3, v_r_919_);
lean_ctor_set(v___x_924_, 2, v_v_888_);
lean_ctor_set(v___x_924_, 1, v_k_887_);
lean_ctor_set(v___x_924_, 0, v___x_932_);
v___x_934_ = v___x_924_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_r_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_r_890_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 4, v___x_934_);
lean_ctor_set(v___x_912_, 3, v___y_929_);
lean_ctor_set(v___x_912_, 2, v_v_917_);
lean_ctor_set(v___x_912_, 1, v_k_916_);
lean_ctor_set(v___x_912_, 0, v___x_927_);
v___x_936_ = v___x_912_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_k_916_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_v_917_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v___y_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_nat_add(v___x_939_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___x_939_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_918_);
lean_ctor_set(v___x_892_, 3, v_l_901_);
lean_ctor_set(v___x_892_, 2, v_v_900_);
lean_ctor_set(v___x_892_, 1, v_k_899_);
lean_ctor_set(v___x_892_, 0, v___x_942_);
v___x_944_ = v___x_892_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_l_901_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_l_918_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_nat_add(v___x_896_, v_size_897_);
if (lean_obj_tag(v_r_919_) == 0)
{
lean_object* v_size_946_; 
v_size_946_ = lean_ctor_get(v_r_919_, 0);
lean_inc(v_size_946_);
v___y_929_ = v___x_944_;
v___y_930_ = v___x_945_;
v___y_931_ = v_size_946_;
goto v___jp_928_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___y_929_ = v___x_944_;
v___y_930_ = v___x_945_;
v___y_931_ = v___x_947_;
goto v___jp_928_;
}
}
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_892_);
v___x_957_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_958_ = lean_nat_add(v___x_957_, v_size_897_);
lean_dec(v___x_957_);
v___x_959_ = lean_nat_add(v___x_896_, v_size_897_);
v___x_960_ = lean_nat_add(v___x_959_, v_size_915_);
lean_dec(v___x_959_);
lean_inc_ref(v_r_890_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 4, v_r_890_);
lean_ctor_set(v___x_912_, 3, v_r_902_);
lean_ctor_set(v___x_912_, 2, v_v_888_);
lean_ctor_set(v___x_912_, 1, v_k_887_);
lean_ctor_set(v___x_912_, 0, v___x_960_);
v___x_962_ = v___x_912_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_r_902_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_r_890_);
v___x_962_ = v_reuseFailAlloc_975_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_isSharedCheck_969_ = !lean_is_exclusive(v_r_890_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; 
v_unused_970_ = lean_ctor_get(v_r_890_, 4);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_r_890_, 3);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_r_890_, 2);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_r_890_, 1);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_890_, 0);
lean_dec(v_unused_974_);
v___x_964_ = v_r_890_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_dec(v_r_890_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v___x_962_);
lean_ctor_set(v___x_964_, 3, v_l_901_);
lean_ctor_set(v___x_964_, 2, v_v_900_);
lean_ctor_set(v___x_964_, 1, v_k_899_);
lean_ctor_set(v___x_964_, 0, v___x_958_);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_l_901_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v___x_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_982_; 
v_l_982_ = lean_ctor_get(v_impl_895_, 3);
lean_inc(v_l_982_);
if (lean_obj_tag(v_l_982_) == 0)
{
lean_object* v_r_983_; lean_object* v_k_984_; lean_object* v_v_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_996_; 
v_r_983_ = lean_ctor_get(v_impl_895_, 4);
v_k_984_ = lean_ctor_get(v_impl_895_, 1);
v_v_985_ = lean_ctor_get(v_impl_895_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_997_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_998_);
v___x_987_ = v_impl_895_;
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_r_983_);
lean_inc(v_v_985_);
lean_inc(v_k_984_);
lean_dec(v_impl_895_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_983_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 3, v_r_983_);
lean_ctor_set(v___x_987_, 2, v_v_888_);
lean_ctor_set(v___x_987_, 1, v_k_887_);
lean_ctor_set(v___x_987_, 0, v___x_896_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_r_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_r_983_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_991_);
lean_ctor_set(v___x_892_, 3, v_l_982_);
lean_ctor_set(v___x_892_, 2, v_v_985_);
lean_ctor_set(v___x_892_, 1, v_k_984_);
lean_ctor_set(v___x_892_, 0, v___x_989_);
v___x_993_ = v___x_892_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_r_999_; 
v_r_999_ = lean_ctor_get(v_impl_895_, 4);
lean_inc(v_r_999_);
if (lean_obj_tag(v_r_999_) == 0)
{
lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1024_; 
v_k_1000_ = lean_ctor_get(v_impl_895_, 1);
v_v_1001_ = lean_ctor_get(v_impl_895_, 2);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1025_ = lean_ctor_get(v_impl_895_, 4);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_1027_);
v___x_1003_ = v_impl_895_;
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_v_1001_);
lean_inc(v_k_1000_);
lean_dec(v_impl_895_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_k_1005_; lean_object* v_v_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1020_; 
v_k_1005_ = lean_ctor_get(v_r_999_, 1);
v_v_1006_ = lean_ctor_get(v_r_999_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_r_999_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1021_ = lean_ctor_get(v_r_999_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_r_999_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_999_, 0);
lean_dec(v_unused_1023_);
v___x_1008_ = v_r_999_;
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_v_1006_);
lean_inc(v_k_1005_);
lean_dec(v_r_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(3u);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_l_982_);
lean_ctor_set(v___x_1008_, 3, v_l_982_);
lean_ctor_set(v___x_1008_, 2, v_v_1001_);
lean_ctor_set(v___x_1008_, 1, v_k_1000_);
lean_ctor_set(v___x_1008_, 0, v___x_896_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_l_982_);
v___x_1012_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 4, v_l_982_);
lean_ctor_set(v___x_1003_, 2, v_v_888_);
lean_ctor_set(v___x_1003_, 1, v_k_887_);
lean_ctor_set(v___x_1003_, 0, v___x_896_);
v___x_1014_ = v___x_1003_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_l_982_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1014_);
lean_ctor_set(v___x_892_, 3, v___x_1012_);
lean_ctor_set(v___x_892_, 2, v_v_1006_);
lean_ctor_set(v___x_892_, 1, v_k_1005_);
lean_ctor_set(v___x_892_, 0, v___x_1010_);
v___x_1016_ = v___x_892_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_999_);
lean_ctor_set(v___x_892_, 3, v_impl_895_);
lean_ctor_set(v___x_892_, 0, v___x_1028_);
v___x_1030_ = v___x_892_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_impl_895_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_r_999_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1033_; 
lean_dec(v_v_888_);
lean_dec(v_k_887_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v_v_884_);
lean_ctor_set(v___x_892_, 1, v_k_883_);
v___x_1033_ = v___x_892_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_size_886_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_r_890_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
default: 
{
lean_object* v_impl_1035_; lean_object* v___x_1036_; 
lean_dec(v_size_886_);
v_impl_1035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_883_, v_v_884_, v_r_890_);
v___x_1036_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_889_) == 0)
{
lean_object* v_size_1037_; lean_object* v_size_1038_; lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v_l_1041_; lean_object* v_r_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_size_1037_ = lean_ctor_get(v_l_889_, 0);
v_size_1038_ = lean_ctor_get(v_impl_1035_, 0);
lean_inc(v_size_1038_);
v_k_1039_ = lean_ctor_get(v_impl_1035_, 1);
lean_inc(v_k_1039_);
v_v_1040_ = lean_ctor_get(v_impl_1035_, 2);
lean_inc(v_v_1040_);
v_l_1041_ = lean_ctor_get(v_impl_1035_, 3);
lean_inc(v_l_1041_);
v_r_1042_ = lean_ctor_get(v_impl_1035_, 4);
lean_inc(v_r_1042_);
v___x_1043_ = lean_unsigned_to_nat(3u);
v___x_1044_ = lean_nat_mul(v___x_1043_, v_size_1037_);
v___x_1045_ = lean_nat_dec_lt(v___x_1044_, v_size_1038_);
lean_dec(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_dec(v_r_1042_);
lean_dec(v_l_1041_);
lean_dec(v_v_1040_);
lean_dec(v_k_1039_);
v___x_1046_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1047_ = lean_nat_add(v___x_1046_, v_size_1038_);
lean_dec(v_size_1038_);
lean_dec(v___x_1046_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_1035_);
lean_ctor_set(v___x_892_, 0, v___x_1047_);
v___x_1049_ = v___x_892_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_impl_1035_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1114_; 
v_isSharedCheck_1114_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1115_ = lean_ctor_get(v_impl_1035_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_impl_1035_, 2);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1035_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1119_);
v___x_1052_ = v_impl_1035_;
v_isShared_1053_ = v_isSharedCheck_1114_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v_impl_1035_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1114_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_size_1054_; lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v_r_1058_; lean_object* v_size_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_size_1054_ = lean_ctor_get(v_l_1041_, 0);
v_k_1055_ = lean_ctor_get(v_l_1041_, 1);
v_v_1056_ = lean_ctor_get(v_l_1041_, 2);
v_l_1057_ = lean_ctor_get(v_l_1041_, 3);
v_r_1058_ = lean_ctor_get(v_l_1041_, 4);
v_size_1059_ = lean_ctor_get(v_r_1042_, 0);
v___x_1060_ = lean_unsigned_to_nat(2u);
v___x_1061_ = lean_nat_mul(v___x_1060_, v_size_1059_);
v___x_1062_ = lean_nat_dec_lt(v_size_1054_, v___x_1061_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1090_; 
lean_inc(v_r_1058_);
lean_inc(v_l_1057_);
lean_inc(v_v_1056_);
lean_inc(v_k_1055_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_l_1041_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1091_ = lean_ctor_get(v_l_1041_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_1041_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_1041_, 2);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_1041_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_l_1041_, 0);
lean_dec(v_unused_1095_);
v___x_1064_ = v_l_1041_;
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_l_1041_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1080_; 
v___x_1066_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1067_ = lean_nat_add(v___x_1066_, v_size_1038_);
lean_dec(v_size_1038_);
if (lean_obj_tag(v_l_1057_) == 0)
{
lean_object* v_size_1088_; 
v_size_1088_ = lean_ctor_get(v_l_1057_, 0);
lean_inc(v_size_1088_);
v___y_1080_ = v_size_1088_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___y_1080_ = v___x_1089_;
goto v___jp_1079_;
}
v___jp_1068_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_nat_add(v___y_1069_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec(v___y_1069_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 4, v_r_1042_);
lean_ctor_set(v___x_1064_, 3, v_r_1058_);
lean_ctor_set(v___x_1064_, 2, v_v_1040_);
lean_ctor_set(v___x_1064_, 1, v_k_1039_);
lean_ctor_set(v___x_1064_, 0, v___x_1072_);
v___x_1074_ = v___x_1064_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_r_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_r_1042_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1074_);
lean_ctor_set(v___x_1052_, 3, v___y_1070_);
lean_ctor_set(v___x_1052_, 2, v_v_1056_);
lean_ctor_set(v___x_1052_, 1, v_k_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1067_);
v___x_1076_ = v___x_1052_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_1056_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___y_1070_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_nat_add(v___x_1066_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v___x_1066_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_1057_);
lean_ctor_set(v___x_892_, 0, v___x_1081_);
v___x_1083_ = v___x_892_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_l_1057_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_nat_add(v___x_1036_, v_size_1059_);
if (lean_obj_tag(v_r_1058_) == 0)
{
lean_object* v_size_1085_; 
v_size_1085_ = lean_ctor_get(v_r_1058_, 0);
lean_inc(v_size_1085_);
v___y_1069_ = v___x_1084_;
v___y_1070_ = v___x_1083_;
v___y_1071_ = v_size_1085_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___y_1069_ = v___x_1084_;
v___y_1070_ = v___x_1083_;
v___y_1071_ = v___x_1086_;
goto v___jp_1068_;
}
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_del_object(v___x_892_);
v___x_1096_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1097_ = lean_nat_add(v___x_1096_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1098_ = lean_nat_add(v___x_1096_, v_size_1054_);
lean_dec(v___x_1096_);
lean_inc_ref(v_l_889_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_l_1041_);
lean_ctor_set(v___x_1052_, 3, v_l_889_);
lean_ctor_set(v___x_1052_, 2, v_v_888_);
lean_ctor_set(v___x_1052_, 1, v_k_887_);
lean_ctor_set(v___x_1052_, 0, v___x_1098_);
v___x_1100_ = v___x_1052_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_l_1041_);
v___x_1100_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v_l_889_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; 
v_unused_1108_ = lean_ctor_get(v_l_889_, 4);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_l_889_, 3);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_l_889_, 2);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_l_889_, 1);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_l_889_, 0);
lean_dec(v_unused_1112_);
v___x_1102_ = v_l_889_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_l_889_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_1042_);
lean_ctor_set(v___x_1102_, 3, v___x_1100_);
lean_ctor_set(v___x_1102_, 2, v_v_1040_);
lean_ctor_set(v___x_1102_, 1, v_k_1039_);
lean_ctor_set(v___x_1102_, 0, v___x_1097_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_r_1042_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1120_; 
v_l_1120_ = lean_ctor_get(v_impl_1035_, 3);
lean_inc(v_l_1120_);
if (lean_obj_tag(v_l_1120_) == 0)
{
lean_object* v_r_1121_; lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1146_; 
v_r_1121_ = lean_ctor_get(v_impl_1035_, 4);
v_k_1122_ = lean_ctor_get(v_impl_1035_, 1);
v_v_1123_ = lean_ctor_get(v_impl_1035_, 2);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1147_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1148_);
v___x_1125_ = v_impl_1035_;
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_r_1121_);
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_impl_1035_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_k_1127_ = lean_ctor_get(v_l_1120_, 1);
v_v_1128_ = lean_ctor_get(v_l_1120_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_l_1120_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1143_ = lean_ctor_get(v_l_1120_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_1120_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_l_1120_, 0);
lean_dec(v_unused_1145_);
v___x_1130_ = v_l_1120_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
lean_dec(v_l_1120_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1121_, 2);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v_r_1121_);
lean_ctor_set(v___x_1130_, 3, v_r_1121_);
lean_ctor_set(v___x_1130_, 2, v_v_888_);
lean_ctor_set(v___x_1130_, 1, v_k_887_);
lean_ctor_set(v___x_1130_, 0, v___x_1036_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_1121_);
v___x_1134_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
lean_inc(v_r_1121_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 3, v_r_1121_);
lean_ctor_set(v___x_1125_, 0, v___x_1036_);
v___x_1136_ = v___x_1125_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_r_1121_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1136_);
lean_ctor_set(v___x_892_, 3, v___x_1134_);
lean_ctor_set(v___x_892_, 2, v_v_1128_);
lean_ctor_set(v___x_892_, 1, v_k_1127_);
lean_ctor_set(v___x_892_, 0, v___x_1132_);
v___x_1138_ = v___x_892_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
else
{
lean_object* v_r_1149_; 
v_r_1149_ = lean_ctor_get(v_impl_1035_, 4);
lean_inc(v_r_1149_);
if (lean_obj_tag(v_r_1149_) == 0)
{
lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1162_; 
v_k_1150_ = lean_ctor_get(v_impl_1035_, 1);
v_v_1151_ = lean_ctor_get(v_impl_1035_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1163_ = lean_ctor_get(v_impl_1035_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1165_);
v___x_1153_ = v_impl_1035_;
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_v_1151_);
lean_inc(v_k_1150_);
lean_dec(v_impl_1035_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(3u);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 4, v_l_1120_);
lean_ctor_set(v___x_1153_, 2, v_v_888_);
lean_ctor_set(v___x_1153_, 1, v_k_887_);
lean_ctor_set(v___x_1153_, 0, v___x_1036_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_l_1120_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_l_1120_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_1149_);
lean_ctor_set(v___x_892_, 3, v___x_1157_);
lean_ctor_set(v___x_892_, 2, v_v_1151_);
lean_ctor_set(v___x_892_, 1, v_k_1150_);
lean_ctor_set(v___x_892_, 0, v___x_1155_);
v___x_1159_ = v___x_892_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1151_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1149_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_1035_);
lean_ctor_set(v___x_892_, 3, v_r_1149_);
lean_ctor_set(v___x_892_, 0, v___x_1166_);
v___x_1168_ = v___x_892_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_r_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_impl_1035_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_k_883_);
lean_ctor_set(v___x_1172_, 2, v_v_884_);
lean_ctor_set(v___x_1172_, 3, v_t_885_);
lean_ctor_set(v___x_1172_, 4, v_t_885_);
return v___x_1172_;
}
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__0(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_box(1);
v___x_1174_ = ((lean_object*)(l_Lake_StrPat_verLike));
v___x_1175_ = ((lean_object*)(l_Lake_StrPat_verLike___closed__2));
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1175_, v___x_1174_, v___x_1173_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_obj_once(&l_Lake_versionTagPresets___closed__0, &l_Lake_versionTagPresets___closed__0_once, _init_l_Lake_versionTagPresets___closed__0);
v___x_1178_ = ((lean_object*)(l_Lake_defaultVersionTags));
v___x_1179_ = ((lean_object*)(l_Lake_defaultVersionTags___closed__1));
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v___x_1179_, v___x_1178_, v___x_1177_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lake_versionTagPresets(void){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_obj_once(&l_Lake_versionTagPresets___closed__1, &l_Lake_versionTagPresets___closed__1_once, _init_l_Lake_versionTagPresets___closed__1);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object* v_00_u03b2_1182_, lean_object* v_k_1183_, lean_object* v_v_1184_, lean_object* v_t_1185_, lean_object* v_hl_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_1183_, v_v_1184_, v_t_1185_);
return v___x_1187_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedPathPatDescr_default = _init_l_Lake_instInhabitedPathPatDescr_default();
lean_mark_persistent(l_Lake_instInhabitedPathPatDescr_default);
l_Lake_instInhabitedPathPatDescr = _init_l_Lake_instInhabitedPathPatDescr();
lean_mark_persistent(l_Lake_instInhabitedPathPatDescr);
l_Lake_versionTagPresets = _init_l_Lake_versionTagPresets();
lean_mark_persistent(l_Lake_versionTagPresets);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Pattern(builtin);
}
#ifdef __cplusplus
}
#endif
