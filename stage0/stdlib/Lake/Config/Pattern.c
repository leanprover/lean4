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
lean_dec_ref(v_a_59_);
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
lean_inc(v_quotContext_65_);
v_currMacroScope_66_ = lean_ctor_get(v_a_59_, 2);
lean_inc(v_currMacroScope_66_);
v_ref_67_ = lean_ctor_get(v_a_59_, 5);
lean_inc(v_ref_67_);
lean_dec_ref(v_a_59_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = l_Lean_Syntax_getArg(v_x_58_, v___x_68_);
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = l_Lean_Syntax_getArg(v_x_58_, v___x_70_);
lean_dec(v_x_58_);
v___x_72_ = 0;
v___x_73_ = l_Lean_SourceInfo_fromRef(v_ref_67_, v___x_72_);
lean_dec(v_ref_67_);
v___x_74_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4));
v___x_75_ = lean_obj_once(&l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6, &l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6_once, _init_l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__6);
v___x_76_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__9));
v___x_77_ = l_Lean_addMacroScope(v_quotContext_65_, v___x_76_, v_currMacroScope_66_);
v___x_78_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__12));
lean_inc(v___x_73_);
v___x_79_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_79_, 0, v___x_73_);
lean_ctor_set(v___x_79_, 1, v___x_75_);
lean_ctor_set(v___x_79_, 2, v___x_77_);
lean_ctor_set(v___x_79_, 3, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__14));
lean_inc(v___x_73_);
v___x_81_ = l_Lean_Syntax_node2(v___x_73_, v___x_80_, v___x_69_, v___x_71_);
v___x_82_ = l_Lean_Syntax_node2(v___x_73_, v___x_74_, v___x_79_, v___x_81_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_60_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______macroRules__Lake__term___x3d_x7e____1___closed__4));
lean_inc(v_x_87_);
v___x_91_ = l_Lean_Syntax_isOfKind(v_x_87_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_x_87_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_a_89_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = l_Lean_Syntax_getArg(v_x_87_, v___x_94_);
v___x_96_ = ((lean_object*)(l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___closed__1));
lean_inc(v___x_95_);
v___x_97_ = l_Lean_Syntax_isOfKind(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v___x_95_);
lean_dec(v_x_87_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_89_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = l_Lean_Syntax_getArg(v_x_87_, v___x_100_);
lean_dec(v_x_87_);
v___x_102_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_101_);
v___x_103_ = l_Lean_Syntax_matchesNull(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v___x_101_);
lean_dec(v___x_95_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_89_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_ref_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_106_ = l_Lean_Syntax_getArg(v___x_101_, v___x_94_);
v___x_107_ = l_Lean_Syntax_getArg(v___x_101_, v___x_100_);
lean_dec(v___x_101_);
v_ref_108_ = l_Lean_replaceRef(v___x_95_, v_a_88_);
lean_dec(v___x_95_);
v___x_109_ = 0;
v___x_110_ = l_Lean_SourceInfo_fromRef(v_ref_108_, v___x_109_);
lean_dec(v_ref_108_);
v___x_111_ = ((lean_object*)(l_Lake_term___x3d_x7e___00__closed__2));
v___x_112_ = ((lean_object*)(l_Lake_term___x3d_x7e___00__closed__5));
lean_inc(v___x_110_);
v___x_113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_110_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = l_Lean_Syntax_node3(v___x_110_, v___x_111_, v___x_106_, v___x_113_, v___x_107_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_89_);
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1___boxed(lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lake___aux__Lake__Config__Pattern______unexpand__Lake__IsPattern__satisfies__1(v_x_116_, v_a_117_, v_a_118_);
lean_dec(v_a_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg(lean_object* v_x_120_){
_start:
{
switch(lean_obj_tag(v_x_120_))
{
case 0:
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(0u);
return v___x_121_;
}
case 1:
{
lean_object* v___x_122_; 
v___x_122_ = lean_unsigned_to_nat(1u);
return v___x_122_;
}
case 2:
{
lean_object* v___x_123_; 
v___x_123_ = lean_unsigned_to_nat(2u);
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(3u);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___redArg___boxed(lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_125_);
lean_dec_ref(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lake_PatternDescr_ctorIdx___redArg(v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___boxed(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_PatternDescr_ctorIdx(v_00_u03b1_131_, v_00_u03b2_132_, v_x_133_);
lean_dec_ref(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___redArg(lean_object* v_t_135_, lean_object* v_k_136_){
_start:
{
if (lean_obj_tag(v_t_135_) == 3)
{
lean_object* v_p_137_; lean_object* v___x_138_; 
v_p_137_ = lean_ctor_get(v_t_135_, 0);
lean_inc(v_p_137_);
lean_dec_ref(v_t_135_);
v___x_138_ = lean_apply_1(v_k_136_, v_p_137_);
return v___x_138_;
}
else
{
lean_object* v_p_139_; lean_object* v___x_140_; 
v_p_139_ = lean_ctor_get(v_t_135_, 0);
lean_inc_ref(v_p_139_);
lean_dec_ref(v_t_135_);
v___x_140_ = lean_apply_1(v_k_136_, v_p_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_motive__2_143_, lean_object* v_ctorIdx_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_k_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_145_, v_k_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_motive__2_151_, lean_object* v_ctorIdx_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lake_PatternDescr_ctorElim(v_00_u03b1_149_, v_00_u03b2_150_, v_motive__2_151_, v_ctorIdx_152_, v_t_153_, v_h_154_, v_k_155_);
lean_dec(v_ctorIdx_152_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim___redArg(lean_object* v_t_157_, lean_object* v_not_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_157_, v_not_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_motive__2_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_not_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_163_, v_not_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim___redArg(lean_object* v_t_167_, lean_object* v_all_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_167_, v_all_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_motive__2_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_all_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_173_, v_all_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim___redArg(lean_object* v_t_177_, lean_object* v_any_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_177_, v_any_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_motive__2_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_any_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_183_, v_any_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim___redArg(lean_object* v_t_187_, lean_object* v_coe_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_187_, v_coe_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_motive__2_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_coe_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_193_, v_coe_195_);
return v___x_196_;
}
}
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___lam__0(lean_object* v_x_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___lam__0___boxed(lean_object* v_x_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lake_instInhabitedPattern_default__1___lam__0(v_x_199_);
lean_dec(v_x_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___closed__1));
return v___x_209_;
}
}
static lean_object* _init_l_Lake_instInhabitedPattern___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Lake_instInhabitedPattern___closed__0, &l_Lake_instInhabitedPattern___closed__0_once, _init_l_Lake_instInhabitedPattern___closed__0);
return v___x_213_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lake_instInhabitedPattern___closed__0, &l_Lake_instInhabitedPattern___closed__0_once, _init_l_Lake_instInhabitedPattern___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_218_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr___closed__0(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lake_instInhabitedPatternDescr_default__1(lean_box(0), lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr___closed__0, &l_Lake_instInhabitedPatternDescr___closed__0_once, _init_l_Lake_instInhabitedPatternDescr___closed__0);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___lam__0(lean_object* v_p_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_224_, 0, v_p_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object* v_00_u03b2_226_, lean_object* v_00_u03b1_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = ((lean_object*)(l_Lake_instCoePatternDescr___closed__0));
return v___f_228_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object* v_a_229_, lean_object* v_self_230_){
_start:
{
lean_object* v_filter_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_filter_231_ = lean_ctor_get(v_self_230_, 0);
lean_inc_ref(v_filter_231_);
lean_dec_ref(v_self_230_);
v___x_232_ = lean_apply_1(v_filter_231_, v_a_229_);
v___x_233_ = lean_unbox(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object* v_a_234_, lean_object* v_self_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lake_Pattern_matches___redArg(v_a_234_, v_self_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_a_240_, lean_object* v_self_241_){
_start:
{
lean_object* v_filter_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_filter_242_ = lean_ctor_get(v_self_241_, 0);
lean_inc_ref(v_filter_242_);
lean_dec_ref(v_self_241_);
v___x_243_ = lean_apply_1(v_filter_242_, v_a_240_);
v___x_244_ = lean_unbox(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_a_247_, lean_object* v_self_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lake_Pattern_matches(v_00_u03b1_245_, v_00_u03b2_246_, v_a_247_, v_self_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___lam__0(lean_object* v_self_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_filter_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_filter_253_ = lean_ctor_get(v_self_251_, 0);
lean_inc_ref(v_filter_253_);
lean_dec_ref(v_self_251_);
v___x_254_ = lean_apply_1(v_filter_253_, v___y_252_);
v___x_255_ = lean_unbox(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___lam__0___boxed(lean_object* v_self_256_, lean_object* v___y_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Lake_instIsPatternPattern___lam__0(v_self_256_, v___y_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_){
_start:
{
lean_object* v___f_263_; 
v___f_263_ = ((lean_object*)(l_Lake_instIsPatternPattern___closed__0));
return v___f_263_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object* v_val_264_, uint8_t v___x_265_, lean_object* v_v_266_){
_start:
{
lean_object* v_filter_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_filter_267_ = lean_ctor_get(v_v_266_, 0);
lean_inc_ref(v_filter_267_);
lean_dec_ref(v_v_266_);
v___x_268_ = lean_apply_1(v_filter_267_, v_val_264_);
v___x_269_ = lean_unbox(v___x_268_);
if (v___x_269_ == 0)
{
return v___x_265_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object* v_val_271_, lean_object* v___x_272_, lean_object* v_v_273_){
_start:
{
uint8_t v___x_220__boxed_274_; uint8_t v_res_275_; lean_object* v_r_276_; 
v___x_220__boxed_274_ = lean_unbox(v___x_272_);
v_res_275_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_271_, v___x_220__boxed_274_, v_v_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object* v_val_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_filter_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_filter_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc_ref(v_filter_279_);
lean_dec_ref(v_x_278_);
v___x_280_ = lean_apply_1(v_filter_279_, v_val_277_);
v___x_281_ = lean_unbox(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object* v_val_282_, lean_object* v_x_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_282_, v_x_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg(lean_object* v_inst_305_, lean_object* v_val_306_, lean_object* v_self_307_){
_start:
{
switch(lean_obj_tag(v_self_307_))
{
case 0:
{
lean_object* v_p_308_; lean_object* v_filter_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
lean_dec_ref(v_inst_305_);
v_p_308_ = lean_ctor_get(v_self_307_, 0);
lean_inc_ref(v_p_308_);
lean_dec_ref(v_self_307_);
v_filter_309_ = lean_ctor_get(v_p_308_, 0);
lean_inc_ref(v_filter_309_);
lean_dec_ref(v_p_308_);
v___x_310_ = lean_apply_1(v_filter_309_, v_val_306_);
v___x_311_ = lean_unbox(v___x_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
case 1:
{
lean_object* v_ps_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
lean_dec_ref(v_inst_305_);
v_ps_314_ = lean_ctor_get(v_self_307_, 0);
lean_inc_ref(v_ps_314_);
lean_dec_ref(v_self_307_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_array_get_size(v_ps_314_);
v___x_317_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_318_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_318_ == 0)
{
uint8_t v___x_319_; 
lean_dec_ref(v_ps_314_);
lean_dec(v_val_306_);
v___x_319_ = 1;
return v___x_319_;
}
else
{
if (v___x_318_ == 0)
{
lean_dec_ref(v_ps_314_);
lean_dec(v_val_306_);
return v___x_318_;
}
else
{
lean_object* v___x_320_; lean_object* v___f_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_320_ = lean_box(v___x_318_);
v___f_321_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_321_, 0, v_val_306_);
lean_closure_set(v___f_321_, 1, v___x_320_);
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_316_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_317_, v___f_321_, v_ps_314_, v___x_322_, v___x_323_);
v___x_325_ = lean_unbox(v___x_324_);
lean_dec(v___x_324_);
if (v___x_325_ == 0)
{
return v___x_318_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
}
}
}
case 2:
{
lean_object* v_ps_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
lean_dec_ref(v_inst_305_);
v_ps_327_ = lean_ctor_get(v_self_307_, 0);
lean_inc_ref(v_ps_327_);
lean_dec_ref(v_self_307_);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_array_get_size(v_ps_327_);
v___x_330_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_331_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
if (v___x_331_ == 0)
{
lean_dec_ref(v_ps_327_);
lean_dec(v_val_306_);
return v___x_331_;
}
else
{
if (v___x_331_ == 0)
{
lean_dec_ref(v_ps_327_);
lean_dec(v_val_306_);
return v___x_331_;
}
else
{
lean_object* v___f_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___f_332_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_332_, 0, v_val_306_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_329_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_330_, v___f_332_, v_ps_327_, v___x_333_, v___x_334_);
v___x_336_ = lean_unbox(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
}
}
default: 
{
lean_object* v_p_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_p_337_ = lean_ctor_get(v_self_307_, 0);
lean_inc(v_p_337_);
lean_dec_ref(v_self_307_);
v___x_338_ = lean_apply_2(v_inst_305_, v_p_337_, v_val_306_);
v___x_339_ = lean_unbox(v___x_338_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object* v_inst_340_, lean_object* v_val_341_, lean_object* v_self_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Lake_PatternDescr_matches___redArg(v_inst_340_, v_val_341_, v_self_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches(lean_object* v_00_u03b2_345_, lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_val_348_, lean_object* v_self_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l_Lake_PatternDescr_matches___redArg(v_inst_347_, v_val_348_, v_self_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object* v_00_u03b2_351_, lean_object* v_00_u03b1_352_, lean_object* v_inst_353_, lean_object* v_val_354_, lean_object* v_self_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lake_PatternDescr_matches(v_00_u03b2_351_, v_00_u03b1_352_, v_inst_353_, v_val_354_, v_self_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object* v_inst_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___boxed), 5, 3);
lean_closure_set(v___x_359_, 0, lean_box(0));
lean_closure_set(v___x_359_, 1, lean_box(0));
lean_closure_set(v___x_359_, 2, v_inst_358_);
v___x_360_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_360_, 0, lean_box(0));
lean_closure_set(v___x_360_, 1, lean_box(0));
lean_closure_set(v___x_360_, 2, lean_box(0));
lean_closure_set(v___x_360_, 3, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object* v_00_u03b2_361_, lean_object* v_00_u03b1_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object* v_f_365_, lean_object* v_name_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(0);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v_f_365_);
lean_ctor_set(v___x_368_, 1, v_name_366_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_f_371_, lean_object* v_name_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_374_, 0, v_f_371_);
lean_ctor_set(v___x_374_, 1, v_name_372_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___lam__0(lean_object* v_f_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v_f_375_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_){
_start:
{
lean_object* v___f_382_; 
v___f_382_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___closed__0));
return v___f_382_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object* v_inst_383_, lean_object* v_descr_384_, lean_object* v_x_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = l_Lake_PatternDescr_matches___redArg(v_inst_383_, v_x_385_, v_descr_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object* v_inst_387_, lean_object* v_descr_388_, lean_object* v_x_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_387_, v_descr_388_, v_x_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object* v_inst_392_, lean_object* v_descr_393_, lean_object* v_name_394_){
_start:
{
lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc_ref(v_descr_393_);
v___f_395_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_395_, 0, v_inst_392_);
lean_closure_set(v___f_395_, 1, v_descr_393_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_descr_393_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v___f_395_);
lean_ctor_set(v___x_397_, 1, v_name_394_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object* v_00_u03b2_398_, lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_descr_401_, lean_object* v_name_402_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc_ref(v_descr_401_);
v___f_403_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_403_, 0, v_inst_400_);
lean_closure_set(v___f_403_, 1, v_descr_401_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_descr_401_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___f_403_);
lean_ctor_set(v___x_405_, 1, v_name_402_);
lean_ctor_set(v___x_405_, 2, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object* v_inst_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Lake_PatternDescr_matches___redArg(v_inst_406_, v_x_408_, v_x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object* v_inst_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_410_, v_x_411_, v_x_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object* v_inst_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc_ref(v_x_416_);
v___f_417_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_417_, 0, v_inst_415_);
lean_closure_set(v___f_417_, 1, v_x_416_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_x_416_);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v___f_417_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object* v_inst_421_){
_start:
{
lean_object* v___f_422_; 
v___f_422_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_422_, 0, v_inst_421_);
return v___f_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object* v_00_u03b2_423_, lean_object* v_00_u03b1_424_, lean_object* v_inst_425_){
_start:
{
lean_object* v___f_426_; 
v___f_426_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_426_, 0, v_inst_425_);
return v___f_426_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object* v_inst_427_, lean_object* v___x_428_, lean_object* v_x_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = l_Lake_PatternDescr_matches___redArg(v_inst_427_, v_x_429_, v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object* v_inst_431_, lean_object* v___x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_431_, v___x_432_, v_x_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object* v_inst_436_, lean_object* v_p_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v_p_437_);
lean_inc_ref(v___x_438_);
v___f_439_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_439_, 0, v_inst_436_);
lean_closure_set(v___f_439_, 1, v___x_438_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v___f_439_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object* v_00_u03b2_443_, lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_p_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_p_446_);
lean_inc_ref(v___x_447_);
v___f_448_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_448_, 0, v_inst_445_);
lean_closure_set(v___f_448_, 1, v___x_447_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_447_);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v___f_448_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object* v_inst_452_, lean_object* v_ps_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_ps_453_);
lean_inc_ref(v___x_454_);
v___f_455_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_455_, 0, v_inst_452_);
lean_closure_set(v___f_455_, 1, v___x_454_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_454_);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v___f_455_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object* v_00_u03b2_459_, lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_ps_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_ps_462_);
lean_inc_ref(v___x_463_);
v___f_464_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_464_, 0, v_inst_461_);
lean_closure_set(v___f_464_, 1, v___x_463_);
v___x_465_ = lean_box(0);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_463_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v___f_464_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object* v_inst_468_, lean_object* v_ps_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_470_, 0, v_ps_469_);
lean_inc_ref(v___x_470_);
v___f_471_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_471_, 0, v_inst_468_);
lean_closure_set(v___f_471_, 1, v___x_470_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_470_);
v___x_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_474_, 0, v___f_471_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object* v_00_u03b2_475_, lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_ps_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_479_, 0, v_ps_478_);
lean_inc_ref(v___x_479_);
v___f_480_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_480_, 0, v_inst_477_);
lean_closure_set(v___f_480_, 1, v___x_479_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_479_);
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v___f_480_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Lake_PatternDescr_empty___closed__1));
return v___x_490_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__2(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lake_PatternDescr_empty(lean_box(0), lean_box(0));
return v___x_494_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__3(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l_Lake_Pattern_empty___closed__2, &l_Lake_Pattern_empty___closed__2_once, _init_l_Lake_Pattern_empty___closed__2);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__4(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v___x_497_ = lean_obj_once(&l_Lake_Pattern_empty___closed__3, &l_Lake_Pattern_empty___closed__3_once, _init_l_Lake_Pattern_empty___closed__3);
v___x_498_ = ((lean_object*)(l_Lake_Pattern_empty___closed__1));
v___f_499_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___closed__0));
v___x_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_500_, 0, v___f_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
lean_ctor_set(v___x_500_, 2, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lake_Pattern_empty___closed__4, &l_Lake_Pattern_empty___closed__4_once, _init_l_Lake_Pattern_empty___closed__4);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lake_Pattern_empty___closed__2, &l_Lake_Pattern_empty___closed__2_once, _init_l_Lake_Pattern_empty___closed__2);
return v___x_506_;
}
}
static lean_object* _init_l_Lake_instEmptyCollectionPattern___closed__0(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lake_Pattern_empty(lean_box(0), lean_box(0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lake_instEmptyCollectionPattern___closed__0, &l_Lake_instEmptyCollectionPattern___closed__0_once, _init_l_Lake_instEmptyCollectionPattern___closed__0);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Lake_PatternDescr_star___closed__0));
return v___x_515_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_star___lam__0(lean_object* v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = 1;
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___lam__0___boxed(lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lake_Pattern_star___lam__0(v_x_518_);
lean_dec(v_x_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__3(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lake_PatternDescr_star(lean_box(0), lean_box(0));
return v___x_525_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lake_Pattern_star___closed__3, &l_Lake_Pattern_star___closed__3_once, _init_l_Lake_Pattern_star___closed__3);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__5(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v___x_528_ = lean_obj_once(&l_Lake_Pattern_star___closed__4, &l_Lake_Pattern_star___closed__4_once, _init_l_Lake_Pattern_star___closed__4);
v___x_529_ = ((lean_object*)(l_Lake_Pattern_star___closed__2));
v___f_530_ = ((lean_object*)(l_Lake_Pattern_star___closed__0));
v___x_531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_531_, 0, v___f_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
lean_ctor_set(v___x_531_, 2, v___x_528_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Lake_Pattern_star___closed__5, &l_Lake_Pattern_star___closed__5_once, _init_l_Lake_Pattern_star___closed__5);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx(lean_object* v_x_535_){
_start:
{
switch(lean_obj_tag(v_x_535_))
{
case 0:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(0u);
return v___x_536_;
}
case 1:
{
lean_object* v___x_537_; 
v___x_537_ = lean_unsigned_to_nat(1u);
return v___x_537_;
}
default: 
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(2u);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___boxed(lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_StrPatDescr_ctorIdx(v_x_539_);
lean_dec_ref(v_x_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object* v_t_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_xs_543_; lean_object* v___x_544_; 
v_xs_543_ = lean_ctor_get(v_t_541_, 0);
lean_inc_ref(v_xs_543_);
lean_dec_ref(v_t_541_);
v___x_544_ = lean_apply_1(v_k_542_, v_xs_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object* v_motive_545_, lean_object* v_ctorIdx_546_, lean_object* v_t_547_, lean_object* v_h_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_547_, v_k_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object* v_motive_551_, lean_object* v_ctorIdx_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lake_StrPatDescr_ctorElim(v_motive_551_, v_ctorIdx_552_, v_t_553_, v_h_554_, v_k_555_);
lean_dec(v_ctorIdx_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object* v_t_557_, lean_object* v_mem_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_557_, v_mem_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object* v_motive_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_mem_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_561_, v_mem_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object* v_t_565_, lean_object* v_startsWith_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_565_, v_startsWith_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object* v_motive_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_startsWith_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_569_, v_startsWith_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object* v_t_573_, lean_object* v_endsWith_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_573_, v_endsWith_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_endsWith_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_577_, v_endsWith_579_);
return v___x_580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object* v_a_587_, lean_object* v_as_588_, size_t v_i_589_, size_t v_stop_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_589_, v_stop_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_uget_borrowed(v_as_588_, v_i_589_);
v___x_593_ = lean_string_dec_eq(v_a_587_, v___x_592_);
if (v___x_593_ == 0)
{
size_t v___x_594_; size_t v___x_595_; 
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_589_, v___x_594_);
v_i_589_ = v___x_595_;
goto _start;
}
else
{
return v___x_593_;
}
}
else
{
uint8_t v___x_597_; 
v___x_597_ = 0;
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object* v_a_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_stop_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; uint8_t v_res_604_; lean_object* v_r_605_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_601_);
lean_dec(v_stop_601_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_598_, v_as_599_, v_i_boxed_602_, v_stop_boxed_603_);
lean_dec_ref(v_as_599_);
lean_dec_ref(v_a_598_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object* v_as_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_array_get_size(v_as_606_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
return v___x_610_;
}
else
{
if (v___x_610_ == 0)
{
return v___x_610_;
}
else
{
size_t v___x_611_; size_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_609_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_607_, v_as_606_, v___x_611_, v___x_612_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object* v_as_614_, lean_object* v_a_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_614_, v_a_615_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_as_614_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPatDescr_matches(lean_object* v_s_618_, lean_object* v_self_619_){
_start:
{
switch(lean_obj_tag(v_self_619_))
{
case 0:
{
lean_object* v_xs_620_; uint8_t v___x_621_; 
v_xs_620_ = lean_ctor_get(v_self_619_, 0);
v___x_621_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_620_, v_s_618_);
return v___x_621_;
}
case 1:
{
lean_object* v_affix_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_affix_622_ = lean_ctor_get(v_self_619_, 0);
v___x_623_ = lean_string_utf8_byte_size(v_s_618_);
v___x_624_ = lean_string_utf8_byte_size(v_affix_622_);
v___x_625_ = lean_nat_dec_le(v___x_624_, v___x_623_);
if (v___x_625_ == 0)
{
return v___x_625_;
}
else
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_string_memcmp(v_s_618_, v_affix_622_, v___x_626_, v___x_626_, v___x_624_);
return v___x_627_;
}
}
default: 
{
lean_object* v_affix_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_affix_628_ = lean_ctor_get(v_self_619_, 0);
v___x_629_ = lean_string_utf8_byte_size(v_s_618_);
v___x_630_ = lean_string_utf8_byte_size(v_affix_628_);
v___x_631_ = lean_nat_dec_le(v___x_630_, v___x_629_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_sub(v___x_629_, v___x_630_);
v___x_634_ = lean_string_memcmp(v_s_618_, v_affix_628_, v___x_633_, v___x_632_, v___x_630_);
lean_dec(v___x_633_);
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object* v_s_635_, lean_object* v_self_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Lake_StrPatDescr_matches(v_s_635_, v_self_636_);
lean_dec_ref(v_self_636_);
lean_dec_ref(v_s_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_mem___lam__0(lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lake_PatternDescr_matches___redArg(v___x_643_, v_x_645_, v___x_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lake_StrPat_mem___lam__0(v___x_647_, v___x_648_, v_x_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object* v_xs_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_653_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_xs_652_);
v___x_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_inc_ref(v___x_655_);
v___f_656_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_656_, 0, v___x_653_);
lean_closure_set(v___f_656_, 1, v___x_655_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_655_);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v___f_656_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object* v_xs_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v_xs_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object* v_affix_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_affix_666_);
v___x_669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_inc_ref(v___x_669_);
v___f_670_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_670_, 0, v___x_667_);
lean_closure_set(v___f_670_, 1, v___x_669_);
v___x_671_ = lean_box(0);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_669_);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v___f_670_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object* v_affix_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_676_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_676_, 0, v_affix_674_);
v___x_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_inc_ref(v___x_677_);
v___f_678_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_678_, 0, v___x_675_);
lean_closure_set(v___f_678_, 1, v___x_677_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_677_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v___f_678_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object* v_s_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_mk_empty_array_with_capacity(v___x_683_);
v___x_685_ = lean_array_push(v___x_684_, v_s_682_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_beq___lam__0(lean_object* v_s_687_, lean_object* v_x_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = lean_string_dec_eq(v_x_688_, v_s_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object* v_s_690_, lean_object* v_x_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lake_StrPat_beq___lam__0(v_s_690_, v_x_691_);
lean_dec_ref(v_x_691_);
lean_dec_ref(v_s_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object* v_s_697_){
_start:
{
lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc_ref(v_s_697_);
v___f_698_ = lean_alloc_closure((void*)(l_Lake_StrPat_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_698_, 0, v_s_697_);
v___x_699_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_700_ = l_Lake_StrPatDescr_beq(v_s_697_);
v___x_701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v___f_698_);
lean_ctor_set(v___x_703_, 1, v___x_699_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx(lean_object* v_x_708_){
_start:
{
switch(lean_obj_tag(v_x_708_))
{
case 0:
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
return v___x_709_;
}
case 1:
{
lean_object* v___x_710_; 
v___x_710_ = lean_unsigned_to_nat(1u);
return v___x_710_;
}
default: 
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(2u);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___boxed(lean_object* v_x_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lake_PathPatDescr_ctorIdx(v_x_712_);
lean_dec_ref(v_x_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object* v_t_714_, lean_object* v_k_715_){
_start:
{
lean_object* v_p_716_; lean_object* v___x_717_; 
v_p_716_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_p_716_);
lean_dec_ref(v_t_714_);
v___x_717_ = lean_apply_1(v_k_715_, v_p_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object* v_motive_718_, lean_object* v_ctorIdx_719_, lean_object* v_t_720_, lean_object* v_h_721_, lean_object* v_k_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_720_, v_k_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object* v_motive_724_, lean_object* v_ctorIdx_725_, lean_object* v_t_726_, lean_object* v_h_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lake_PathPatDescr_ctorElim(v_motive_724_, v_ctorIdx_725_, v_t_726_, v_h_727_, v_k_728_);
lean_dec(v_ctorIdx_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object* v_t_730_, lean_object* v_path_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_730_, v_path_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object* v_motive_733_, lean_object* v_t_734_, lean_object* v_h_735_, lean_object* v_path_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_734_, v_path_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object* v_t_738_, lean_object* v_extension_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_738_, v_extension_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object* v_motive_741_, lean_object* v_t_742_, lean_object* v_h_743_, lean_object* v_extension_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_742_, v_extension_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object* v_t_746_, lean_object* v_fileName_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_746_, v_fileName_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object* v_motive_749_, lean_object* v_t_750_, lean_object* v_h_751_, lean_object* v_fileName_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_750_, v_fileName_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__0(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lake_instInhabitedPattern_default__1(lean_box(0), lean_box(0));
return v___x_754_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__0, &l_Lake_instInhabitedPathPatDescr_default___closed__0_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__0);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default(void){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__1, &l_Lake_instInhabitedPathPatDescr_default___closed__1_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__1);
return v___x_757_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr(void){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lake_instInhabitedPathPatDescr_default;
return v___x_758_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object* v_p_759_, lean_object* v_x_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = lean_string_dec_eq(v_x_760_, v_p_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object* v_p_762_, lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lake_PathPatDescr_eq___lam__0(v_p_762_, v_x_763_);
lean_dec_ref(v_x_763_);
lean_dec_ref(v_p_762_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object* v_p_766_){
_start:
{
lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_inc_ref(v_p_766_);
v___f_767_ = lean_alloc_closure((void*)(l_Lake_PathPatDescr_eq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_767_, 0, v_p_766_);
v___x_768_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_769_ = l_Lake_StrPatDescr_beq(v_p_766_);
v___x_770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v___f_767_);
lean_ctor_set(v___x_772_, 1, v___x_768_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_matches(lean_object* v_path_774_, lean_object* v_self_775_){
_start:
{
switch(lean_obj_tag(v_self_775_))
{
case 0:
{
lean_object* v_p_776_; lean_object* v_filter_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_p_776_ = lean_ctor_get(v_self_775_, 0);
lean_inc_ref(v_p_776_);
lean_dec_ref(v_self_775_);
v_filter_777_ = lean_ctor_get(v_p_776_, 0);
lean_inc_ref(v_filter_777_);
lean_dec_ref(v_p_776_);
v___x_778_ = l_System_FilePath_normalize(v_path_774_);
v___x_779_ = lean_apply_1(v_filter_777_, v___x_778_);
v___x_780_ = lean_unbox(v___x_779_);
return v___x_780_;
}
case 1:
{
lean_object* v_p_781_; lean_object* v___x_782_; 
v_p_781_ = lean_ctor_get(v_self_775_, 0);
lean_inc_ref(v_p_781_);
lean_dec_ref(v_self_775_);
v___x_782_ = l_System_FilePath_extension(v_path_774_);
if (lean_obj_tag(v___x_782_) == 0)
{
uint8_t v___x_783_; 
lean_dec_ref(v_p_781_);
v___x_783_ = 0;
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v_filter_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_val_784_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_784_);
lean_dec_ref(v___x_782_);
v_filter_785_ = lean_ctor_get(v_p_781_, 0);
lean_inc_ref(v_filter_785_);
lean_dec_ref(v_p_781_);
v___x_786_ = lean_apply_1(v_filter_785_, v_val_784_);
v___x_787_ = lean_unbox(v___x_786_);
return v___x_787_;
}
}
default: 
{
lean_object* v_p_788_; lean_object* v___x_789_; 
v_p_788_ = lean_ctor_get(v_self_775_, 0);
lean_inc_ref(v_p_788_);
lean_dec_ref(v_self_775_);
v___x_789_ = l_System_FilePath_fileName(v_path_774_);
if (lean_obj_tag(v___x_789_) == 0)
{
uint8_t v___x_790_; 
lean_dec_ref(v_p_788_);
v___x_790_ = 0;
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v_filter_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_val_791_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_val_791_);
lean_dec_ref(v___x_789_);
v_filter_792_ = lean_ctor_get(v_p_788_, 0);
lean_inc_ref(v_filter_792_);
lean_dec_ref(v_p_788_);
v___x_793_ = lean_apply_1(v_filter_792_, v_val_791_);
v___x_794_ = lean_unbox(v___x_793_);
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object* v_path_795_, lean_object* v_self_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Lake_PathPatDescr_matches(v_path_795_, v_self_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPat_path___lam__0(lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = l_Lake_PatternDescr_matches___redArg(v___x_803_, v_x_805_, v___x_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object* v___x_807_, lean_object* v___x_808_, lean_object* v_x_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Lake_PathPat_path___lam__0(v___x_807_, v___x_808_, v_x_809_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object* v_p_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_p_812_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_inc_ref(v___x_815_);
v___f_816_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_816_, 0, v___x_813_);
lean_closure_set(v___f_816_, 1, v___x_815_);
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_815_);
v___x_819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_819_, 0, v___f_816_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object* v_p_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_p_820_);
v___x_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_inc_ref(v___x_823_);
v___f_824_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_824_, 0, v___x_821_);
lean_closure_set(v___f_824_, 1, v___x_823_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
v___x_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_827_, 0, v___f_824_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object* v_p_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_829_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_830_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_830_, 0, v_p_828_);
v___x_831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_inc_ref(v___x_831_);
v___f_832_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_832_, 0, v___x_829_);
lean_closure_set(v___f_832_, 1, v___x_831_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_831_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v___f_832_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_h__1_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_apply_2(v_h__1_838_, v_x_836_, v_x_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_h__1_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_apply_2(v_h__1_843_, v_x_841_, v_x_842_);
return v___x_844_;
}
}
LEAN_EXPORT uint8_t l_Lake_isVerLike(lean_object* v_s_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_unsigned_to_nat(2u);
v___x_847_ = lean_string_utf8_byte_size(v_s_845_);
v___x_848_ = lean_nat_dec_le(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
return v___x_848_;
}
else
{
lean_object* v___x_849_; uint32_t v___x_850_; uint32_t v___x_851_; uint8_t v___x_852_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_string_utf8_get_fast(v_s_845_, v___x_849_);
v___x_851_ = 118;
v___x_852_ = lean_uint32_dec_eq(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
return v___x_852_;
}
else
{
lean_object* v___x_853_; uint32_t v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_string_utf8_get_fast(v_s_845_, v___x_853_);
v___x_855_ = 48;
v___x_856_ = lean_uint32_dec_le(v___x_855_, v___x_854_);
if (v___x_856_ == 0)
{
return v___x_856_;
}
else
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 57;
v___x_858_ = lean_uint32_dec_le(v___x_854_, v___x_857_);
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object* v_s_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lake_isVerLike(v_s_859_);
lean_dec_ref(v_s_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object* v_k_879_, lean_object* v_v_880_, lean_object* v_t_881_){
_start:
{
if (lean_obj_tag(v_t_881_) == 0)
{
lean_object* v_size_882_; lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_l_885_; lean_object* v_r_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_1166_; 
v_size_882_ = lean_ctor_get(v_t_881_, 0);
v_k_883_ = lean_ctor_get(v_t_881_, 1);
v_v_884_ = lean_ctor_get(v_t_881_, 2);
v_l_885_ = lean_ctor_get(v_t_881_, 3);
v_r_886_ = lean_ctor_get(v_t_881_, 4);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_t_881_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_888_ = v_t_881_;
v_isShared_889_ = v_isSharedCheck_1166_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_r_886_);
lean_inc(v_l_885_);
lean_inc(v_v_884_);
lean_inc(v_k_883_);
lean_inc(v_size_882_);
lean_dec(v_t_881_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_1166_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
uint8_t v___x_890_; 
v___x_890_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_879_, v_k_883_);
switch(v___x_890_)
{
case 0:
{
lean_object* v_impl_891_; lean_object* v___x_892_; 
lean_dec(v_size_882_);
v_impl_891_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_879_, v_v_880_, v_l_885_);
v___x_892_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_886_) == 0)
{
lean_object* v_size_893_; lean_object* v_size_894_; lean_object* v_k_895_; lean_object* v_v_896_; lean_object* v_l_897_; lean_object* v_r_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_size_893_ = lean_ctor_get(v_r_886_, 0);
v_size_894_ = lean_ctor_get(v_impl_891_, 0);
lean_inc(v_size_894_);
v_k_895_ = lean_ctor_get(v_impl_891_, 1);
lean_inc(v_k_895_);
v_v_896_ = lean_ctor_get(v_impl_891_, 2);
lean_inc(v_v_896_);
v_l_897_ = lean_ctor_get(v_impl_891_, 3);
lean_inc(v_l_897_);
v_r_898_ = lean_ctor_get(v_impl_891_, 4);
lean_inc(v_r_898_);
v___x_899_ = lean_unsigned_to_nat(3u);
v___x_900_ = lean_nat_mul(v___x_899_, v_size_893_);
v___x_901_ = lean_nat_dec_lt(v___x_900_, v_size_894_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_dec(v_r_898_);
lean_dec(v_l_897_);
lean_dec(v_v_896_);
lean_dec(v_k_895_);
v___x_902_ = lean_nat_add(v___x_892_, v_size_894_);
lean_dec(v_size_894_);
v___x_903_ = lean_nat_add(v___x_902_, v_size_893_);
lean_dec(v___x_902_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 3, v_impl_891_);
lean_ctor_set(v___x_888_, 0, v___x_903_);
v___x_905_ = v___x_888_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_impl_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_r_886_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_972_; 
v_isSharedCheck_972_ = !lean_is_exclusive(v_impl_891_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; lean_object* v_unused_977_; 
v_unused_973_ = lean_ctor_get(v_impl_891_, 4);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_impl_891_, 3);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_impl_891_, 2);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_impl_891_, 1);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_impl_891_, 0);
lean_dec(v_unused_977_);
v___x_908_ = v_impl_891_;
v_isShared_909_ = v_isSharedCheck_972_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_impl_891_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_972_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_size_910_; lean_object* v_size_911_; lean_object* v_k_912_; lean_object* v_v_913_; lean_object* v_l_914_; lean_object* v_r_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_size_910_ = lean_ctor_get(v_l_897_, 0);
v_size_911_ = lean_ctor_get(v_r_898_, 0);
v_k_912_ = lean_ctor_get(v_r_898_, 1);
v_v_913_ = lean_ctor_get(v_r_898_, 2);
v_l_914_ = lean_ctor_get(v_r_898_, 3);
v_r_915_ = lean_ctor_get(v_r_898_, 4);
v___x_916_ = lean_unsigned_to_nat(2u);
v___x_917_ = lean_nat_mul(v___x_916_, v_size_910_);
v___x_918_ = lean_nat_dec_lt(v_size_911_, v___x_917_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_947_; 
lean_inc(v_r_915_);
lean_inc(v_l_914_);
lean_inc(v_v_913_);
lean_inc(v_k_912_);
v_isSharedCheck_947_ = !lean_is_exclusive(v_r_898_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; 
v_unused_948_ = lean_ctor_get(v_r_898_, 4);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_898_, 3);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_r_898_, 2);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_r_898_, 1);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_r_898_, 0);
lean_dec(v_unused_952_);
v___x_920_ = v_r_898_;
v_isShared_921_ = v_isSharedCheck_947_;
goto v_resetjp_919_;
}
else
{
lean_dec(v_r_898_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_947_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___x_935_; lean_object* v___y_937_; 
v___x_922_ = lean_nat_add(v___x_892_, v_size_894_);
lean_dec(v_size_894_);
v___x_923_ = lean_nat_add(v___x_922_, v_size_893_);
lean_dec(v___x_922_);
v___x_935_ = lean_nat_add(v___x_892_, v_size_910_);
if (lean_obj_tag(v_l_914_) == 0)
{
lean_object* v_size_945_; 
v_size_945_ = lean_ctor_get(v_l_914_, 0);
lean_inc(v_size_945_);
v___y_937_ = v_size_945_;
goto v___jp_936_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___y_937_ = v___x_946_;
goto v___jp_936_;
}
v___jp_924_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_nat_add(v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 4, v_r_886_);
lean_ctor_set(v___x_920_, 3, v_r_915_);
lean_ctor_set(v___x_920_, 2, v_v_884_);
lean_ctor_set(v___x_920_, 1, v_k_883_);
lean_ctor_set(v___x_920_, 0, v___x_928_);
v___x_930_ = v___x_920_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_r_915_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_r_886_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v___x_930_);
lean_ctor_set(v___x_908_, 3, v___y_925_);
lean_ctor_set(v___x_908_, 2, v_v_913_);
lean_ctor_set(v___x_908_, 1, v_k_912_);
lean_ctor_set(v___x_908_, 0, v___x_923_);
v___x_932_ = v___x_908_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_912_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v___y_925_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_nat_add(v___x_935_, v___y_937_);
lean_dec(v___y_937_);
lean_dec(v___x_935_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_l_914_);
lean_ctor_set(v___x_888_, 3, v_l_897_);
lean_ctor_set(v___x_888_, 2, v_v_896_);
lean_ctor_set(v___x_888_, 1, v_k_895_);
lean_ctor_set(v___x_888_, 0, v___x_938_);
v___x_940_ = v___x_888_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_895_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_896_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_l_897_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_l_914_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_nat_add(v___x_892_, v_size_893_);
if (lean_obj_tag(v_r_915_) == 0)
{
lean_object* v_size_942_; 
v_size_942_ = lean_ctor_get(v_r_915_, 0);
lean_inc(v_size_942_);
v___y_925_ = v___x_940_;
v___y_926_ = v___x_941_;
v___y_927_ = v_size_942_;
goto v___jp_924_;
}
else
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___y_925_ = v___x_940_;
v___y_926_ = v___x_941_;
v___y_927_ = v___x_943_;
goto v___jp_924_;
}
}
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
lean_del_object(v___x_888_);
v___x_953_ = lean_nat_add(v___x_892_, v_size_894_);
lean_dec(v_size_894_);
v___x_954_ = lean_nat_add(v___x_953_, v_size_893_);
lean_dec(v___x_953_);
v___x_955_ = lean_nat_add(v___x_892_, v_size_893_);
v___x_956_ = lean_nat_add(v___x_955_, v_size_911_);
lean_dec(v___x_955_);
lean_inc_ref(v_r_886_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v_r_886_);
lean_ctor_set(v___x_908_, 3, v_r_898_);
lean_ctor_set(v___x_908_, 2, v_v_884_);
lean_ctor_set(v___x_908_, 1, v_k_883_);
lean_ctor_set(v___x_908_, 0, v___x_956_);
v___x_958_ = v___x_908_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_r_898_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v_r_886_);
v___x_958_ = v_reuseFailAlloc_971_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_isSharedCheck_965_ = !lean_is_exclusive(v_r_886_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_966_ = lean_ctor_get(v_r_886_, 4);
lean_dec(v_unused_966_);
v_unused_967_ = lean_ctor_get(v_r_886_, 3);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_r_886_, 2);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_r_886_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_r_886_, 0);
lean_dec(v_unused_970_);
v___x_960_ = v_r_886_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_r_886_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v___x_958_);
lean_ctor_set(v___x_960_, 3, v_l_897_);
lean_ctor_set(v___x_960_, 2, v_v_896_);
lean_ctor_set(v___x_960_, 1, v_k_895_);
lean_ctor_set(v___x_960_, 0, v___x_954_);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_k_895_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_v_896_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_l_897_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v___x_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_978_; 
v_l_978_ = lean_ctor_get(v_impl_891_, 3);
lean_inc(v_l_978_);
if (lean_obj_tag(v_l_978_) == 0)
{
lean_object* v_r_979_; lean_object* v_k_980_; lean_object* v_v_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
v_r_979_ = lean_ctor_get(v_impl_891_, 4);
v_k_980_ = lean_ctor_get(v_impl_891_, 1);
v_v_981_ = lean_ctor_get(v_impl_891_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_impl_891_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; 
v_unused_993_ = lean_ctor_get(v_impl_891_, 3);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_impl_891_, 0);
lean_dec(v_unused_994_);
v___x_983_ = v_impl_891_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_r_979_);
lean_inc(v_v_981_);
lean_inc(v_k_980_);
lean_dec(v_impl_891_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_979_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 3, v_r_979_);
lean_ctor_set(v___x_983_, 2, v_v_884_);
lean_ctor_set(v___x_983_, 1, v_k_883_);
lean_ctor_set(v___x_983_, 0, v___x_892_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_r_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_r_979_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v___x_987_);
lean_ctor_set(v___x_888_, 3, v_l_978_);
lean_ctor_set(v___x_888_, 2, v_v_981_);
lean_ctor_set(v___x_888_, 1, v_k_980_);
lean_ctor_set(v___x_888_, 0, v___x_985_);
v___x_989_ = v___x_888_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_981_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_l_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v_r_995_; 
v_r_995_ = lean_ctor_get(v_impl_891_, 4);
lean_inc(v_r_995_);
if (lean_obj_tag(v_r_995_) == 0)
{
lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1020_; 
v_k_996_ = lean_ctor_get(v_impl_891_, 1);
v_v_997_ = lean_ctor_get(v_impl_891_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_impl_891_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1021_ = lean_ctor_get(v_impl_891_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_impl_891_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_impl_891_, 0);
lean_dec(v_unused_1023_);
v___x_999_ = v_impl_891_;
v_isShared_1000_ = v_isSharedCheck_1020_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_v_997_);
lean_inc(v_k_996_);
lean_dec(v_impl_891_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1020_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_k_1001_; lean_object* v_v_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1016_; 
v_k_1001_ = lean_ctor_get(v_r_995_, 1);
v_v_1002_ = lean_ctor_get(v_r_995_, 2);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_r_995_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1017_ = lean_ctor_get(v_r_995_, 4);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_995_, 3);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_r_995_, 0);
lean_dec(v_unused_1019_);
v___x_1004_ = v_r_995_;
v_isShared_1005_ = v_isSharedCheck_1016_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_v_1002_);
lean_inc(v_k_1001_);
lean_dec(v_r_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1016_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_unsigned_to_nat(3u);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 4, v_l_978_);
lean_ctor_set(v___x_1004_, 3, v_l_978_);
lean_ctor_set(v___x_1004_, 2, v_v_997_);
lean_ctor_set(v___x_1004_, 1, v_k_996_);
lean_ctor_set(v___x_1004_, 0, v___x_892_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_996_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_997_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_l_978_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_l_978_);
v___x_1008_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 4, v_l_978_);
lean_ctor_set(v___x_999_, 2, v_v_884_);
lean_ctor_set(v___x_999_, 1, v_k_883_);
lean_ctor_set(v___x_999_, 0, v___x_892_);
v___x_1010_ = v___x_999_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_l_978_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v_l_978_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v___x_1010_);
lean_ctor_set(v___x_888_, 3, v___x_1008_);
lean_ctor_set(v___x_888_, 2, v_v_1002_);
lean_ctor_set(v___x_888_, 1, v_k_1001_);
lean_ctor_set(v___x_888_, 0, v___x_1006_);
v___x_1012_ = v___x_888_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_k_1001_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_v_1002_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_unsigned_to_nat(2u);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_r_995_);
lean_ctor_set(v___x_888_, 3, v_impl_891_);
lean_ctor_set(v___x_888_, 0, v___x_1024_);
v___x_1026_ = v___x_888_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_impl_891_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_r_995_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1029_; 
lean_dec(v_v_884_);
lean_dec(v_k_883_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 2, v_v_880_);
lean_ctor_set(v___x_888_, 1, v_k_879_);
v___x_1029_ = v___x_888_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_size_882_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_879_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_880_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_l_885_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_r_886_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
default: 
{
lean_object* v_impl_1031_; lean_object* v___x_1032_; 
lean_dec(v_size_882_);
v_impl_1031_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_879_, v_v_880_, v_r_886_);
v___x_1032_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_885_) == 0)
{
lean_object* v_size_1033_; lean_object* v_size_1034_; lean_object* v_k_1035_; lean_object* v_v_1036_; lean_object* v_l_1037_; lean_object* v_r_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_size_1033_ = lean_ctor_get(v_l_885_, 0);
v_size_1034_ = lean_ctor_get(v_impl_1031_, 0);
lean_inc(v_size_1034_);
v_k_1035_ = lean_ctor_get(v_impl_1031_, 1);
lean_inc(v_k_1035_);
v_v_1036_ = lean_ctor_get(v_impl_1031_, 2);
lean_inc(v_v_1036_);
v_l_1037_ = lean_ctor_get(v_impl_1031_, 3);
lean_inc(v_l_1037_);
v_r_1038_ = lean_ctor_get(v_impl_1031_, 4);
lean_inc(v_r_1038_);
v___x_1039_ = lean_unsigned_to_nat(3u);
v___x_1040_ = lean_nat_mul(v___x_1039_, v_size_1033_);
v___x_1041_ = lean_nat_dec_lt(v___x_1040_, v_size_1034_);
lean_dec(v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v_r_1038_);
lean_dec(v_l_1037_);
lean_dec(v_v_1036_);
lean_dec(v_k_1035_);
v___x_1042_ = lean_nat_add(v___x_1032_, v_size_1033_);
v___x_1043_ = lean_nat_add(v___x_1042_, v_size_1034_);
lean_dec(v_size_1034_);
lean_dec(v___x_1042_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_impl_1031_);
lean_ctor_set(v___x_888_, 0, v___x_1043_);
v___x_1045_ = v___x_888_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_l_885_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v_impl_1031_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1110_; 
v_isSharedCheck_1110_ = !lean_is_exclusive(v_impl_1031_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1111_ = lean_ctor_get(v_impl_1031_, 4);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_impl_1031_, 3);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_impl_1031_, 2);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_impl_1031_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_impl_1031_, 0);
lean_dec(v_unused_1115_);
v___x_1048_ = v_impl_1031_;
v_isShared_1049_ = v_isSharedCheck_1110_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_impl_1031_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1110_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_size_1050_; lean_object* v_k_1051_; lean_object* v_v_1052_; lean_object* v_l_1053_; lean_object* v_r_1054_; lean_object* v_size_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_size_1050_ = lean_ctor_get(v_l_1037_, 0);
v_k_1051_ = lean_ctor_get(v_l_1037_, 1);
v_v_1052_ = lean_ctor_get(v_l_1037_, 2);
v_l_1053_ = lean_ctor_get(v_l_1037_, 3);
v_r_1054_ = lean_ctor_get(v_l_1037_, 4);
v_size_1055_ = lean_ctor_get(v_r_1038_, 0);
v___x_1056_ = lean_unsigned_to_nat(2u);
v___x_1057_ = lean_nat_mul(v___x_1056_, v_size_1055_);
v___x_1058_ = lean_nat_dec_lt(v_size_1050_, v___x_1057_);
lean_dec(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1086_; 
lean_inc(v_r_1054_);
lean_inc(v_l_1053_);
lean_inc(v_v_1052_);
lean_inc(v_k_1051_);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_l_1037_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; lean_object* v_unused_1091_; 
v_unused_1087_ = lean_ctor_get(v_l_1037_, 4);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_l_1037_, 3);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_l_1037_, 2);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_l_1037_, 1);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_l_1037_, 0);
lean_dec(v_unused_1091_);
v___x_1060_ = v_l_1037_;
v_isShared_1061_ = v_isSharedCheck_1086_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v_l_1037_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1086_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1076_; 
v___x_1062_ = lean_nat_add(v___x_1032_, v_size_1033_);
v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1034_);
lean_dec(v_size_1034_);
if (lean_obj_tag(v_l_1053_) == 0)
{
lean_object* v_size_1084_; 
v_size_1084_ = lean_ctor_get(v_l_1053_, 0);
lean_inc(v_size_1084_);
v___y_1076_ = v_size_1084_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___y_1076_ = v___x_1085_;
goto v___jp_1075_;
}
v___jp_1064_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_nat_add(v___y_1065_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec(v___y_1065_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 4, v_r_1038_);
lean_ctor_set(v___x_1060_, 3, v_r_1054_);
lean_ctor_set(v___x_1060_, 2, v_v_1036_);
lean_ctor_set(v___x_1060_, 1, v_k_1035_);
lean_ctor_set(v___x_1060_, 0, v___x_1068_);
v___x_1070_ = v___x_1060_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_1035_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_1036_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_r_1054_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_r_1038_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 4, v___x_1070_);
lean_ctor_set(v___x_1048_, 3, v___y_1066_);
lean_ctor_set(v___x_1048_, 2, v_v_1052_);
lean_ctor_set(v___x_1048_, 1, v_k_1051_);
lean_ctor_set(v___x_1048_, 0, v___x_1063_);
v___x_1072_ = v___x_1048_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1051_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1052_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v___y_1066_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
v___jp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_nat_add(v___x_1062_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec(v___x_1062_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_l_1053_);
lean_ctor_set(v___x_888_, 0, v___x_1077_);
v___x_1079_ = v___x_888_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_l_885_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_l_1053_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_nat_add(v___x_1032_, v_size_1055_);
if (lean_obj_tag(v_r_1054_) == 0)
{
lean_object* v_size_1081_; 
v_size_1081_ = lean_ctor_get(v_r_1054_, 0);
lean_inc(v_size_1081_);
v___y_1065_ = v___x_1080_;
v___y_1066_ = v___x_1079_;
v___y_1067_ = v_size_1081_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___y_1065_ = v___x_1080_;
v___y_1066_ = v___x_1079_;
v___y_1067_ = v___x_1082_;
goto v___jp_1064_;
}
}
}
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_del_object(v___x_888_);
v___x_1092_ = lean_nat_add(v___x_1032_, v_size_1033_);
v___x_1093_ = lean_nat_add(v___x_1092_, v_size_1034_);
lean_dec(v_size_1034_);
v___x_1094_ = lean_nat_add(v___x_1092_, v_size_1050_);
lean_dec(v___x_1092_);
lean_inc_ref(v_l_885_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 4, v_l_1037_);
lean_ctor_set(v___x_1048_, 3, v_l_885_);
lean_ctor_set(v___x_1048_, 2, v_v_884_);
lean_ctor_set(v___x_1048_, 1, v_k_883_);
lean_ctor_set(v___x_1048_, 0, v___x_1094_);
v___x_1096_ = v___x_1048_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_l_885_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_l_1037_);
v___x_1096_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_isSharedCheck_1103_ = !lean_is_exclusive(v_l_885_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1104_ = lean_ctor_get(v_l_885_, 4);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_l_885_, 3);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_l_885_, 2);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_l_885_, 1);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_l_885_, 0);
lean_dec(v_unused_1108_);
v___x_1098_ = v_l_885_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v_l_885_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_r_1038_);
lean_ctor_set(v___x_1098_, 3, v___x_1096_);
lean_ctor_set(v___x_1098_, 2, v_v_1036_);
lean_ctor_set(v___x_1098_, 1, v_k_1035_);
lean_ctor_set(v___x_1098_, 0, v___x_1093_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_k_1035_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_v_1036_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_r_1038_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1116_; 
v_l_1116_ = lean_ctor_get(v_impl_1031_, 3);
lean_inc(v_l_1116_);
if (lean_obj_tag(v_l_1116_) == 0)
{
lean_object* v_r_1117_; lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1142_; 
v_r_1117_ = lean_ctor_get(v_impl_1031_, 4);
v_k_1118_ = lean_ctor_get(v_impl_1031_, 1);
v_v_1119_ = lean_ctor_get(v_impl_1031_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_impl_1031_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1143_ = lean_ctor_get(v_impl_1031_, 3);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_impl_1031_, 0);
lean_dec(v_unused_1144_);
v___x_1121_ = v_impl_1031_;
v_isShared_1122_ = v_isSharedCheck_1142_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_r_1117_);
lean_inc(v_v_1119_);
lean_inc(v_k_1118_);
lean_dec(v_impl_1031_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1142_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_k_1123_; lean_object* v_v_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1138_; 
v_k_1123_ = lean_ctor_get(v_l_1116_, 1);
v_v_1124_ = lean_ctor_get(v_l_1116_, 2);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_l_1116_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1139_ = lean_ctor_get(v_l_1116_, 4);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_l_1116_, 3);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_l_1116_, 0);
lean_dec(v_unused_1141_);
v___x_1126_ = v_l_1116_;
v_isShared_1127_ = v_isSharedCheck_1138_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_v_1124_);
lean_inc(v_k_1123_);
lean_dec(v_l_1116_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1138_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1117_, 2);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1117_);
lean_ctor_set(v___x_1126_, 3, v_r_1117_);
lean_ctor_set(v___x_1126_, 2, v_v_884_);
lean_ctor_set(v___x_1126_, 1, v_k_883_);
lean_ctor_set(v___x_1126_, 0, v___x_1032_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_r_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_r_1117_);
v___x_1130_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
lean_inc(v_r_1117_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 3, v_r_1117_);
lean_ctor_set(v___x_1121_, 0, v___x_1032_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1119_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_r_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_r_1117_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v___x_1132_);
lean_ctor_set(v___x_888_, 3, v___x_1130_);
lean_ctor_set(v___x_888_, 2, v_v_1124_);
lean_ctor_set(v___x_888_, 1, v_k_1123_);
lean_ctor_set(v___x_888_, 0, v___x_1128_);
v___x_1134_ = v___x_888_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1124_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
else
{
lean_object* v_r_1145_; 
v_r_1145_ = lean_ctor_get(v_impl_1031_, 4);
lean_inc(v_r_1145_);
if (lean_obj_tag(v_r_1145_) == 0)
{
lean_object* v_k_1146_; lean_object* v_v_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1158_; 
v_k_1146_ = lean_ctor_get(v_impl_1031_, 1);
v_v_1147_ = lean_ctor_get(v_impl_1031_, 2);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_impl_1031_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1159_ = lean_ctor_get(v_impl_1031_, 4);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_impl_1031_, 3);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_impl_1031_, 0);
lean_dec(v_unused_1161_);
v___x_1149_ = v_impl_1031_;
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_v_1147_);
lean_inc(v_k_1146_);
lean_dec(v_impl_1031_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(3u);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 4, v_l_1116_);
lean_ctor_set(v___x_1149_, 2, v_v_884_);
lean_ctor_set(v___x_1149_, 1, v_k_883_);
lean_ctor_set(v___x_1149_, 0, v___x_1032_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_l_1116_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_l_1116_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_r_1145_);
lean_ctor_set(v___x_888_, 3, v___x_1153_);
lean_ctor_set(v___x_888_, 2, v_v_1147_);
lean_ctor_set(v___x_888_, 1, v_k_1146_);
lean_ctor_set(v___x_888_, 0, v___x_1151_);
v___x_1155_ = v___x_888_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_k_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_v_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_r_1145_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(2u);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_impl_1031_);
lean_ctor_set(v___x_888_, 3, v_r_1145_);
lean_ctor_set(v___x_888_, 0, v___x_1162_);
v___x_1164_ = v___x_888_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_r_1145_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_impl_1031_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
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
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v_k_879_);
lean_ctor_set(v___x_1168_, 2, v_v_880_);
lean_ctor_set(v___x_1168_, 3, v_t_881_);
lean_ctor_set(v___x_1168_, 4, v_t_881_);
return v___x_1168_;
}
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = lean_box(1);
v___x_1170_ = ((lean_object*)(l_Lake_StrPat_verLike));
v___x_1171_ = ((lean_object*)(l_Lake_StrPat_verLike___closed__2));
v___x_1172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1171_, v___x_1170_, v___x_1169_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__1(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_obj_once(&l_Lake_versionTagPresets___closed__0, &l_Lake_versionTagPresets___closed__0_once, _init_l_Lake_versionTagPresets___closed__0);
v___x_1174_ = ((lean_object*)(l_Lake_defaultVersionTags));
v___x_1175_ = ((lean_object*)(l_Lake_defaultVersionTags___closed__1));
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v___x_1175_, v___x_1174_, v___x_1173_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lake_versionTagPresets(void){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_obj_once(&l_Lake_versionTagPresets___closed__1, &l_Lake_versionTagPresets___closed__1_once, _init_l_Lake_versionTagPresets___closed__1);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object* v_00_u03b2_1178_, lean_object* v_k_1179_, lean_object* v_v_1180_, lean_object* v_t_1181_, lean_object* v_hl_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_1179_, v_v_1180_, v_t_1181_);
return v___x_1183_;
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
