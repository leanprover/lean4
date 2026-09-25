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
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instInhabitedPattern_default__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedPattern_default__1___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedPattern_default__1___redArg___closed__0 = (const lean_object*)&l_Lake_instInhabitedPattern_default__1___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedPattern_default__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedPattern_default__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedPattern_default__1___redArg___closed__1 = (const lean_object*)&l_Lake_instInhabitedPattern_default__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPattern_default__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPattern_default__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPatternDescr_default__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPatternDescr_default__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg();
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoePatternDescr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoePatternDescr___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoePatternDescr___redArg___closed__0 = (const lean_object*)&l_Lake_instCoePatternDescr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg();
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instIsPatternPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instIsPatternPattern___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instIsPatternPattern___redArg___closed__0 = (const lean_object*)&l_Lake_instIsPatternPattern___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg();
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeForallBoolPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeForallBoolPattern___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeForallBoolPattern___redArg___closed__0 = (const lean_object*)&l_Lake_instCoeForallBoolPattern___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg();
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___boxed(lean_object*);
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
static const lean_array_object l_Lake_PatternDescr_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PatternDescr_empty___redArg___closed__0 = (const lean_object*)&l_Lake_PatternDescr_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lake_PatternDescr_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_empty___redArg___closed__0_value)}};
static const lean_object* l_Lake_PatternDescr_empty___redArg___closed__1 = (const lean_object*)&l_Lake_PatternDescr_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PatternDescr_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PatternDescr_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object*, lean_object*);
static const lean_string_object l_Lake_Pattern_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "empty"};
static const lean_object* l_Lake_Pattern_empty___redArg___closed__0 = (const lean_object*)&l_Lake_Pattern_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Pattern_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_empty___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 82, 154, 99, 191, 124, 127, 105)}};
static const lean_object* l_Lake_Pattern_empty___redArg___closed__1 = (const lean_object*)&l_Lake_Pattern_empty___redArg___closed__1_value;
static lean_once_cell_t l_Lake_Pattern_empty___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___redArg___closed__2;
static lean_once_cell_t l_Lake_Pattern_empty___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_Pattern_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg();
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg();
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_PatternDescr_star___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PatternDescr_empty___redArg___closed__0_value)}};
static const lean_object* l_Lake_PatternDescr_star___redArg___closed__0 = (const lean_object*)&l_Lake_PatternDescr_star___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg();
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_PatternDescr_star___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PatternDescr_star___closed__0;
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Pattern_star___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Pattern_star___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Pattern_star___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Pattern_star___redArg___closed__0 = (const lean_object*)&l_Lake_Pattern_star___redArg___closed__0_value;
static const lean_string_object l_Lake_Pattern_star___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l_Lake_Pattern_star___redArg___closed__1 = (const lean_object*)&l_Lake_Pattern_star___redArg___closed__1_value;
static const lean_ctor_object l_Lake_Pattern_star___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Pattern_star___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 171, 138, 133, 66, 70, 83, 43)}};
static const lean_object* l_Lake_Pattern_star___redArg___closed__2 = (const lean_object*)&l_Lake_Pattern_star___redArg___closed__2_value;
static lean_once_cell_t l_Lake_Pattern_star___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___redArg___closed__3;
static lean_once_cell_t l_Lake_Pattern_star___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg();
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_Pattern_star___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Pattern_star___closed__0;
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
lean_dec_ref_known(v_t_139_, 1);
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
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___redArg___lam__0(lean_object* v_x_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___lam__0___boxed(lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lake_instInhabitedPattern_default__1___redArg___lam__0(v_x_203_);
lean_dec(v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg(){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__1));
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___boxed(lean_object* v___dummy_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v_res_214_;
}
}
static lean_object* _init_l_Lake_instInhabitedPattern_default__1___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg(){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg___boxed(lean_object* v___dummy_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_instInhabitedPattern___redArg();
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_225_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg(){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg___boxed(lean_object* v___dummy_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v_res_231_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg(){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg___boxed(lean_object* v___dummy_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lake_instInhabitedPatternDescr___redArg();
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___lam__0(lean_object* v_p_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_244_, 0, v_p_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg(){
_start:
{
lean_object* v___f_247_; 
v___f_247_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___boxed(lean_object* v___dummy_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lake_instCoePatternDescr___redArg();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object* v_00_u03b2_250_, lean_object* v_00_u03b1_251_){
_start:
{
lean_object* v___f_252_; 
v___f_252_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_252_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object* v_a_253_, lean_object* v_self_254_){
_start:
{
lean_object* v_filter_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_filter_255_ = lean_ctor_get(v_self_254_, 0);
lean_inc_ref(v_filter_255_);
lean_dec_ref(v_self_254_);
v___x_256_ = lean_apply_1(v_filter_255_, v_a_253_);
v___x_257_ = lean_unbox(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object* v_a_258_, lean_object* v_self_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Lake_Pattern_matches___redArg(v_a_258_, v_self_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_self_265_){
_start:
{
lean_object* v_filter_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_filter_266_ = lean_ctor_get(v_self_265_, 0);
lean_inc_ref(v_filter_266_);
lean_dec_ref(v_self_265_);
v___x_267_ = lean_apply_1(v_filter_266_, v_a_264_);
v___x_268_ = lean_unbox(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_a_271_, lean_object* v_self_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lake_Pattern_matches(v_00_u03b1_269_, v_00_u03b2_270_, v_a_271_, v_self_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___redArg___lam__0(lean_object* v_self_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_filter_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_filter_277_ = lean_ctor_get(v_self_275_, 0);
lean_inc_ref(v_filter_277_);
lean_dec_ref(v_self_275_);
v___x_278_ = lean_apply_1(v_filter_277_, v___y_276_);
v___x_279_ = lean_unbox(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___lam__0___boxed(lean_object* v_self_280_, lean_object* v___y_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Lake_instIsPatternPattern___redArg___lam__0(v_self_280_, v___y_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg(){
_start:
{
lean_object* v___f_286_; 
v___f_286_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___boxed(lean_object* v___dummy_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lake_instIsPatternPattern___redArg();
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_291_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object* v_val_292_, uint8_t v___x_293_, lean_object* v_v_294_){
_start:
{
lean_object* v_filter_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_filter_295_ = lean_ctor_get(v_v_294_, 0);
lean_inc_ref(v_filter_295_);
lean_dec_ref(v_v_294_);
v___x_296_ = lean_apply_1(v_filter_295_, v_val_292_);
v___x_297_ = lean_unbox(v___x_296_);
if (v___x_297_ == 0)
{
return v___x_293_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object* v_val_299_, lean_object* v___x_300_, lean_object* v_v_301_){
_start:
{
uint8_t v___x_202__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v___x_202__boxed_302_ = lean_unbox(v___x_300_);
v_res_303_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_299_, v___x_202__boxed_302_, v_v_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object* v_val_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_filter_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_filter_307_ = lean_ctor_get(v_x_306_, 0);
lean_inc_ref(v_filter_307_);
lean_dec_ref(v_x_306_);
v___x_308_ = lean_apply_1(v_filter_307_, v_val_305_);
v___x_309_ = lean_unbox(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object* v_val_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_310_, v_x_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg(lean_object* v_inst_333_, lean_object* v_val_334_, lean_object* v_self_335_){
_start:
{
switch(lean_obj_tag(v_self_335_))
{
case 0:
{
lean_object* v_p_336_; lean_object* v_filter_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
lean_dec_ref(v_inst_333_);
v_p_336_ = lean_ctor_get(v_self_335_, 0);
lean_inc_ref(v_p_336_);
lean_dec_ref_known(v_self_335_, 1);
v_filter_337_ = lean_ctor_get(v_p_336_, 0);
lean_inc_ref(v_filter_337_);
lean_dec_ref(v_p_336_);
v___x_338_ = lean_apply_1(v_filter_337_, v_val_334_);
v___x_339_ = lean_unbox(v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
case 1:
{
lean_object* v_ps_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
lean_dec_ref(v_inst_333_);
v_ps_342_ = lean_ctor_get(v_self_335_, 0);
lean_inc_ref(v_ps_342_);
lean_dec_ref_known(v_self_335_, 1);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_ps_342_);
v___x_345_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_346_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
lean_dec_ref(v_ps_342_);
lean_dec(v_val_334_);
v___x_347_ = 1;
return v___x_347_;
}
else
{
if (v___x_346_ == 0)
{
lean_dec_ref(v_ps_342_);
lean_dec(v_val_334_);
return v___x_346_;
}
else
{
lean_object* v___x_348_; lean_object* v___f_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_348_ = lean_box(v___x_346_);
v___f_349_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_349_, 0, v_val_334_);
lean_closure_set(v___f_349_, 1, v___x_348_);
v___x_350_ = ((size_t)0ULL);
v___x_351_ = lean_usize_of_nat(v___x_344_);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_345_, v___f_349_, v_ps_342_, v___x_350_, v___x_351_);
v___x_353_ = lean_unbox(v___x_352_);
lean_dec(v___x_352_);
if (v___x_353_ == 0)
{
return v___x_346_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
}
}
case 2:
{
lean_object* v_ps_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_dec_ref(v_inst_333_);
v_ps_355_ = lean_ctor_get(v_self_335_, 0);
lean_inc_ref(v_ps_355_);
lean_dec_ref_known(v_self_335_, 1);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_array_get_size(v_ps_355_);
v___x_358_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_359_ = lean_nat_dec_lt(v___x_356_, v___x_357_);
if (v___x_359_ == 0)
{
lean_dec_ref(v_ps_355_);
lean_dec(v_val_334_);
return v___x_359_;
}
else
{
if (v___x_359_ == 0)
{
lean_dec_ref(v_ps_355_);
lean_dec(v_val_334_);
return v___x_359_;
}
else
{
lean_object* v___f_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___f_360_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_360_, 0, v_val_334_);
v___x_361_ = ((size_t)0ULL);
v___x_362_ = lean_usize_of_nat(v___x_357_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_358_, v___f_360_, v_ps_355_, v___x_361_, v___x_362_);
v___x_364_ = lean_unbox(v___x_363_);
lean_dec(v___x_363_);
return v___x_364_;
}
}
}
default: 
{
lean_object* v_p_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_p_365_ = lean_ctor_get(v_self_335_, 0);
lean_inc(v_p_365_);
lean_dec_ref_known(v_self_335_, 1);
v___x_366_ = lean_apply_2(v_inst_333_, v_p_365_, v_val_334_);
v___x_367_ = lean_unbox(v___x_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object* v_inst_368_, lean_object* v_val_369_, lean_object* v_self_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lake_PatternDescr_matches___redArg(v_inst_368_, v_val_369_, v_self_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches(lean_object* v_00_u03b2_373_, lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_val_376_, lean_object* v_self_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lake_PatternDescr_matches___redArg(v_inst_375_, v_val_376_, v_self_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object* v_00_u03b2_379_, lean_object* v_00_u03b1_380_, lean_object* v_inst_381_, lean_object* v_val_382_, lean_object* v_self_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lake_PatternDescr_matches(v_00_u03b2_379_, v_00_u03b1_380_, v_inst_381_, v_val_382_, v_self_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object* v_inst_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___boxed), 5, 3);
lean_closure_set(v___x_387_, 0, lean_box(0));
lean_closure_set(v___x_387_, 1, lean_box(0));
lean_closure_set(v___x_387_, 2, v_inst_386_);
v___x_388_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_388_, 0, lean_box(0));
lean_closure_set(v___x_388_, 1, lean_box(0));
lean_closure_set(v___x_388_, 2, lean_box(0));
lean_closure_set(v___x_388_, 3, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object* v_00_u03b2_389_, lean_object* v_00_u03b1_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object* v_f_393_, lean_object* v_name_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v_f_393_);
lean_ctor_set(v___x_396_, 1, v_name_394_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_f_399_, lean_object* v_name_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v_f_399_);
lean_ctor_set(v___x_402_, 1, v_name_400_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___lam__0(lean_object* v_f_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_box(0);
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v_f_403_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg(){
_start:
{
lean_object* v___f_409_; 
v___f_409_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___boxed(lean_object* v___dummy_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lake_instCoeForallBoolPattern___redArg();
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_){
_start:
{
lean_object* v___f_414_; 
v___f_414_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_414_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object* v_inst_415_, lean_object* v_descr_416_, lean_object* v_x_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = l_Lake_PatternDescr_matches___redArg(v_inst_415_, v_x_417_, v_descr_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object* v_inst_419_, lean_object* v_descr_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_419_, v_descr_420_, v_x_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object* v_inst_424_, lean_object* v_descr_425_, lean_object* v_name_426_){
_start:
{
lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc_ref(v_descr_425_);
v___f_427_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_427_, 0, v_inst_424_);
lean_closure_set(v___f_427_, 1, v_descr_425_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v_descr_425_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v___f_427_);
lean_ctor_set(v___x_429_, 1, v_name_426_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object* v_00_u03b2_430_, lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_descr_433_, lean_object* v_name_434_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc_ref(v_descr_433_);
v___f_435_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_435_, 0, v_inst_432_);
lean_closure_set(v___f_435_, 1, v_descr_433_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_descr_433_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v___f_435_);
lean_ctor_set(v___x_437_, 1, v_name_434_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object* v_inst_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lake_PatternDescr_matches___redArg(v_inst_438_, v_x_440_, v_x_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object* v_inst_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_442_, v_x_443_, v_x_444_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object* v_inst_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref(v_x_448_);
v___f_449_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_449_, 0, v_inst_447_);
lean_closure_set(v___f_449_, 1, v_x_448_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v_x_448_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v___f_449_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object* v_inst_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_454_, 0, v_inst_453_);
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object* v_00_u03b2_455_, lean_object* v_00_u03b1_456_, lean_object* v_inst_457_){
_start:
{
lean_object* v___f_458_; 
v___f_458_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_458_, 0, v_inst_457_);
return v___f_458_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object* v_inst_459_, lean_object* v___x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lake_PatternDescr_matches___redArg(v_inst_459_, v_x_461_, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object* v_inst_463_, lean_object* v___x_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_463_, v___x_464_, v_x_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object* v_inst_468_, lean_object* v_p_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_p_469_);
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
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object* v_00_u03b2_475_, lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_p_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_p_478_);
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
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object* v_inst_484_, lean_object* v_ps_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_ps_485_);
lean_inc_ref(v___x_486_);
v___f_487_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_487_, 0, v_inst_484_);
lean_closure_set(v___f_487_, 1, v___x_486_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_486_);
v___x_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_490_, 0, v___f_487_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object* v_00_u03b2_491_, lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_ps_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_ps_494_);
lean_inc_ref(v___x_495_);
v___f_496_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_496_, 0, v_inst_493_);
lean_closure_set(v___f_496_, 1, v___x_495_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_495_);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v___f_496_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object* v_inst_500_, lean_object* v_ps_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_502_, 0, v_ps_501_);
lean_inc_ref(v___x_502_);
v___f_503_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_503_, 0, v_inst_500_);
lean_closure_set(v___f_503_, 1, v___x_502_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_502_);
v___x_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_506_, 0, v___f_503_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object* v_00_u03b2_507_, lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_ps_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___f_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_511_, 0, v_ps_510_);
lean_inc_ref(v___x_511_);
v___f_512_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_512_, 0, v_inst_509_);
lean_closure_set(v___f_512_, 1, v___x_511_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
v___x_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_515_, 0, v___f_512_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg(){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Lake_PatternDescr_empty___redArg___closed__1));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg___boxed(lean_object* v___dummy_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lake_PatternDescr_empty___redArg();
return v_res_523_;
}
}
static lean_object* _init_l_Lake_PatternDescr_empty___closed__0(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lake_PatternDescr_empty___redArg();
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_527_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
v___x_533_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__2, &l_Lake_Pattern_empty___redArg___closed__2_once, _init_l_Lake_Pattern_empty___redArg___closed__2);
v___x_534_ = ((lean_object*)(l_Lake_Pattern_empty___redArg___closed__1));
v___f_535_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__0));
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v___f_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg(){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__3, &l_Lake_Pattern_empty___redArg___closed__3_once, _init_l_Lake_Pattern_empty___redArg___closed__3);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg___boxed(lean_object* v___dummy_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_Pattern_empty___redArg();
return v_res_540_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__0(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lake_Pattern_empty___redArg();
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg(){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg___boxed(lean_object* v___dummy_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lake_instEmptyCollectionPatternDescr___redArg();
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg(){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg___boxed(lean_object* v___dummy_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lake_instEmptyCollectionPattern___redArg();
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg(){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Lake_PatternDescr_star___redArg___closed__0));
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg___boxed(lean_object* v___dummy_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lake_PatternDescr_star___redArg();
return v_res_564_;
}
}
static lean_object* _init_l_Lake_PatternDescr_star___closed__0(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lake_PatternDescr_star___redArg();
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
return v___x_568_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_star___redArg___lam__0(lean_object* v_x_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = 1;
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___lam__0___boxed(lean_object* v_x_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lake_Pattern_star___redArg___lam__0(v_x_571_);
lean_dec(v_x_571_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__3(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__4(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v___x_580_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__3, &l_Lake_Pattern_star___redArg___closed__3_once, _init_l_Lake_Pattern_star___redArg___closed__3);
v___x_581_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__2));
v___f_582_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__0));
v___x_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_583_, 0, v___f_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg(){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__4, &l_Lake_Pattern_star___redArg___closed__4_once, _init_l_Lake_Pattern_star___redArg___closed__4);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___boxed(lean_object* v___dummy_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lake_Pattern_star___redArg();
return v_res_587_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__0(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lake_Pattern_star___redArg();
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lake_Pattern_star___closed__0, &l_Lake_Pattern_star___closed__0_once, _init_l_Lake_Pattern_star___closed__0);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx(lean_object* v_x_592_){
_start:
{
switch(lean_obj_tag(v_x_592_))
{
case 0:
{
lean_object* v___x_593_; 
v___x_593_ = lean_unsigned_to_nat(0u);
return v___x_593_;
}
case 1:
{
lean_object* v___x_594_; 
v___x_594_ = lean_unsigned_to_nat(1u);
return v___x_594_;
}
default: 
{
lean_object* v___x_595_; 
v___x_595_ = lean_unsigned_to_nat(2u);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___boxed(lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lake_StrPatDescr_ctorIdx(v_x_596_);
lean_dec_ref(v_x_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object* v_t_598_, lean_object* v_k_599_){
_start:
{
lean_object* v_xs_600_; lean_object* v___x_601_; 
v_xs_600_ = lean_ctor_get(v_t_598_, 0);
lean_inc_ref(v_xs_600_);
lean_dec_ref(v_t_598_);
v___x_601_ = lean_apply_1(v_k_599_, v_xs_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object* v_motive_602_, lean_object* v_ctorIdx_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_k_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_604_, v_k_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object* v_motive_608_, lean_object* v_ctorIdx_609_, lean_object* v_t_610_, lean_object* v_h_611_, lean_object* v_k_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lake_StrPatDescr_ctorElim(v_motive_608_, v_ctorIdx_609_, v_t_610_, v_h_611_, v_k_612_);
lean_dec(v_ctorIdx_609_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object* v_t_614_, lean_object* v_mem_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_614_, v_mem_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object* v_motive_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_mem_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_618_, v_mem_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object* v_t_622_, lean_object* v_startsWith_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_622_, v_startsWith_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object* v_motive_625_, lean_object* v_t_626_, lean_object* v_h_627_, lean_object* v_startsWith_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_626_, v_startsWith_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object* v_t_630_, lean_object* v_endsWith_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_630_, v_endsWith_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object* v_motive_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_endsWith_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_634_, v_endsWith_636_);
return v___x_637_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object* v_a_644_, lean_object* v_as_645_, size_t v_i_646_, size_t v_stop_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_usize_dec_eq(v_i_646_, v_stop_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_array_uget_borrowed(v_as_645_, v_i_646_);
v___x_650_ = lean_string_dec_eq(v_a_644_, v___x_649_);
if (v___x_650_ == 0)
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_646_, v___x_651_);
v_i_646_ = v___x_652_;
goto _start;
}
else
{
return v___x_650_;
}
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object* v_a_655_, lean_object* v_as_656_, lean_object* v_i_657_, lean_object* v_stop_658_){
_start:
{
size_t v_i_boxed_659_; size_t v_stop_boxed_660_; uint8_t v_res_661_; lean_object* v_r_662_; 
v_i_boxed_659_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_stop_boxed_660_ = lean_unbox_usize(v_stop_658_);
lean_dec(v_stop_658_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_655_, v_as_656_, v_i_boxed_659_, v_stop_boxed_660_);
lean_dec_ref(v_as_656_);
lean_dec_ref(v_a_655_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object* v_as_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_as_663_);
v___x_667_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
size_t v___x_668_; size_t v___x_669_; uint8_t v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_666_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_664_, v_as_663_, v___x_668_, v___x_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object* v_as_671_, lean_object* v_a_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_671_, v_a_672_);
lean_dec_ref(v_a_672_);
lean_dec_ref(v_as_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPatDescr_matches(lean_object* v_s_675_, lean_object* v_self_676_){
_start:
{
switch(lean_obj_tag(v_self_676_))
{
case 0:
{
lean_object* v_xs_677_; uint8_t v___x_678_; 
v_xs_677_ = lean_ctor_get(v_self_676_, 0);
v___x_678_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_677_, v_s_675_);
return v___x_678_;
}
case 1:
{
lean_object* v_affix_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_affix_679_ = lean_ctor_get(v_self_676_, 0);
v___x_680_ = lean_string_utf8_byte_size(v_s_675_);
v___x_681_ = lean_string_utf8_byte_size(v_affix_679_);
v___x_682_ = lean_nat_dec_le(v___x_681_, v___x_680_);
if (v___x_682_ == 0)
{
return v___x_682_;
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_string_memcmp(v_s_675_, v_affix_679_, v___x_683_, v___x_683_, v___x_681_);
return v___x_684_;
}
}
default: 
{
lean_object* v_affix_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_affix_685_ = lean_ctor_get(v_self_676_, 0);
v___x_686_ = lean_string_utf8_byte_size(v_s_675_);
v___x_687_ = lean_string_utf8_byte_size(v_affix_685_);
v___x_688_ = lean_nat_dec_le(v___x_687_, v___x_686_);
if (v___x_688_ == 0)
{
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_nat_sub(v___x_686_, v___x_687_);
v___x_691_ = lean_string_memcmp(v_s_675_, v_affix_685_, v___x_690_, v___x_689_, v___x_687_);
lean_dec(v___x_690_);
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object* v_s_692_, lean_object* v_self_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Lake_StrPatDescr_matches(v_s_692_, v_self_693_);
lean_dec_ref(v_self_693_);
lean_dec_ref(v_s_692_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_mem___lam__0(lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v_x_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lake_PatternDescr_matches___redArg(v___x_700_, v_x_702_, v___x_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_Lake_StrPat_mem___lam__0(v___x_704_, v___x_705_, v_x_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object* v_xs_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_710_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_xs_709_);
v___x_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_inc_ref(v___x_712_);
v___f_713_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_713_, 0, v___x_710_);
lean_closure_set(v___f_713_, 1, v___x_712_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v___f_713_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object* v_xs_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_xs_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object* v_affix_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_724_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_affix_723_);
v___x_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_inc_ref(v___x_726_);
v___f_727_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_727_, 0, v___x_724_);
lean_closure_set(v___f_727_, 1, v___x_726_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
v___x_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_730_, 0, v___f_727_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object* v_affix_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_732_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_733_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_733_, 0, v_affix_731_);
v___x_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_inc_ref(v___x_734_);
v___f_735_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_735_, 0, v___x_732_);
lean_closure_set(v___f_735_, 1, v___x_734_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_734_);
v___x_738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_738_, 0, v___f_735_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object* v_s_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
v___x_742_ = lean_array_push(v___x_741_, v_s_739_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_beq___lam__0(lean_object* v_s_744_, lean_object* v_x_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_string_dec_eq(v_x_745_, v_s_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object* v_s_747_, lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lake_StrPat_beq___lam__0(v_s_747_, v_x_748_);
lean_dec_ref(v_x_748_);
lean_dec_ref(v_s_747_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object* v_s_754_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_inc_ref(v_s_754_);
v___f_755_ = lean_alloc_closure((void*)(l_Lake_StrPat_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_755_, 0, v_s_754_);
v___x_756_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_757_ = l_Lake_StrPatDescr_beq(v_s_754_);
v___x_758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_760_, 0, v___f_755_);
lean_ctor_set(v___x_760_, 1, v___x_756_);
lean_ctor_set(v___x_760_, 2, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx(lean_object* v_x_765_){
_start:
{
switch(lean_obj_tag(v_x_765_))
{
case 0:
{
lean_object* v___x_766_; 
v___x_766_ = lean_unsigned_to_nat(0u);
return v___x_766_;
}
case 1:
{
lean_object* v___x_767_; 
v___x_767_ = lean_unsigned_to_nat(1u);
return v___x_767_;
}
default: 
{
lean_object* v___x_768_; 
v___x_768_ = lean_unsigned_to_nat(2u);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___boxed(lean_object* v_x_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_PathPatDescr_ctorIdx(v_x_769_);
lean_dec_ref(v_x_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object* v_t_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_p_773_; lean_object* v___x_774_; 
v_p_773_ = lean_ctor_get(v_t_771_, 0);
lean_inc_ref(v_p_773_);
lean_dec_ref(v_t_771_);
v___x_774_ = lean_apply_1(v_k_772_, v_p_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object* v_motive_775_, lean_object* v_ctorIdx_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_777_, v_k_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object* v_motive_781_, lean_object* v_ctorIdx_782_, lean_object* v_t_783_, lean_object* v_h_784_, lean_object* v_k_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_PathPatDescr_ctorElim(v_motive_781_, v_ctorIdx_782_, v_t_783_, v_h_784_, v_k_785_);
lean_dec(v_ctorIdx_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object* v_t_787_, lean_object* v_path_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_787_, v_path_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object* v_motive_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_path_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_791_, v_path_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object* v_t_795_, lean_object* v_extension_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_795_, v_extension_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object* v_motive_798_, lean_object* v_t_799_, lean_object* v_h_800_, lean_object* v_extension_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_799_, v_extension_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object* v_t_803_, lean_object* v_fileName_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_803_, v_fileName_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object* v_motive_806_, lean_object* v_t_807_, lean_object* v_h_808_, lean_object* v_fileName_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_807_, v_fileName_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__0(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default(void){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__0, &l_Lake_instInhabitedPathPatDescr_default___closed__0_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__0);
return v___x_813_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lake_instInhabitedPathPatDescr_default;
return v___x_814_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object* v_p_815_, lean_object* v_x_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_string_dec_eq(v_x_816_, v_p_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object* v_p_818_, lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Lake_PathPatDescr_eq___lam__0(v_p_818_, v_x_819_);
lean_dec_ref(v_x_819_);
lean_dec_ref(v_p_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object* v_p_822_){
_start:
{
lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_inc_ref(v_p_822_);
v___f_823_ = lean_alloc_closure((void*)(l_Lake_PathPatDescr_eq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_823_, 0, v_p_822_);
v___x_824_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_825_ = l_Lake_StrPatDescr_beq(v_p_822_);
v___x_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_828_, 0, v___f_823_);
lean_ctor_set(v___x_828_, 1, v___x_824_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_matches(lean_object* v_path_830_, lean_object* v_self_831_){
_start:
{
switch(lean_obj_tag(v_self_831_))
{
case 0:
{
lean_object* v_p_832_; lean_object* v_filter_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_p_832_ = lean_ctor_get(v_self_831_, 0);
lean_inc_ref(v_p_832_);
lean_dec_ref_known(v_self_831_, 1);
v_filter_833_ = lean_ctor_get(v_p_832_, 0);
lean_inc_ref(v_filter_833_);
lean_dec_ref(v_p_832_);
v___x_834_ = l_System_FilePath_normalize(v_path_830_);
v___x_835_ = lean_apply_1(v_filter_833_, v___x_834_);
v___x_836_ = lean_unbox(v___x_835_);
return v___x_836_;
}
case 1:
{
lean_object* v_p_837_; lean_object* v___x_838_; 
v_p_837_ = lean_ctor_get(v_self_831_, 0);
lean_inc_ref(v_p_837_);
lean_dec_ref_known(v_self_831_, 1);
v___x_838_ = l_System_FilePath_extension(v_path_830_);
if (lean_obj_tag(v___x_838_) == 0)
{
uint8_t v___x_839_; 
lean_dec_ref(v_p_837_);
v___x_839_ = 0;
return v___x_839_;
}
else
{
lean_object* v_val_840_; lean_object* v_filter_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_val_840_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v___x_838_, 1);
v_filter_841_ = lean_ctor_get(v_p_837_, 0);
lean_inc_ref(v_filter_841_);
lean_dec_ref(v_p_837_);
v___x_842_ = lean_apply_1(v_filter_841_, v_val_840_);
v___x_843_ = lean_unbox(v___x_842_);
return v___x_843_;
}
}
default: 
{
lean_object* v_p_844_; lean_object* v___x_845_; 
v_p_844_ = lean_ctor_get(v_self_831_, 0);
lean_inc_ref(v_p_844_);
lean_dec_ref_known(v_self_831_, 1);
v___x_845_ = l_System_FilePath_fileName(v_path_830_);
if (lean_obj_tag(v___x_845_) == 0)
{
uint8_t v___x_846_; 
lean_dec_ref(v_p_844_);
v___x_846_ = 0;
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v_filter_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_val_847_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_845_, 1);
v_filter_848_ = lean_ctor_get(v_p_844_, 0);
lean_inc_ref(v_filter_848_);
lean_dec_ref(v_p_844_);
v___x_849_ = lean_apply_1(v_filter_848_, v_val_847_);
v___x_850_ = lean_unbox(v___x_849_);
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object* v_path_851_, lean_object* v_self_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Lake_PathPatDescr_matches(v_path_851_, v_self_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPat_path___lam__0(lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Lake_PatternDescr_matches___redArg(v___x_859_, v_x_861_, v___x_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v_x_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lake_PathPat_path___lam__0(v___x_863_, v___x_864_, v_x_865_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object* v_p_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_869_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_p_868_);
v___x_871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_inc_ref(v___x_871_);
v___f_872_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_872_, 0, v___x_869_);
lean_closure_set(v___f_872_, 1, v___x_871_);
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_871_);
v___x_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_875_, 0, v___f_872_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object* v_p_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_p_876_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_inc_ref(v___x_879_);
v___f_880_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_880_, 0, v___x_877_);
lean_closure_set(v___f_880_, 1, v___x_879_);
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_879_);
v___x_883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_883_, 0, v___f_880_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
lean_ctor_set(v___x_883_, 2, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object* v_p_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_885_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_886_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_886_, 0, v_p_884_);
v___x_887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_inc_ref(v___x_887_);
v___f_888_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_888_, 0, v___x_885_);
lean_closure_set(v___f_888_, 1, v___x_887_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_887_);
v___x_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_891_, 0, v___f_888_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_h__1_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_apply_2(v_h__1_894_, v_x_892_, v_x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_h__1_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_2(v_h__1_899_, v_x_897_, v_x_898_);
return v___x_900_;
}
}
LEAN_EXPORT uint8_t l_Lake_isVerLike(lean_object* v_s_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_unsigned_to_nat(2u);
v___x_903_ = lean_string_utf8_byte_size(v_s_901_);
v___x_904_ = lean_nat_dec_le(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
return v___x_904_;
}
else
{
lean_object* v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint8_t v___x_908_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_string_utf8_get_fast(v_s_901_, v___x_905_);
v___x_907_ = 118;
v___x_908_ = lean_uint32_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
return v___x_908_;
}
else
{
lean_object* v___x_909_; uint32_t v___x_910_; uint32_t v___x_911_; uint8_t v___x_912_; 
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_string_utf8_get_fast(v_s_901_, v___x_909_);
v___x_911_ = 48;
v___x_912_ = lean_uint32_dec_le(v___x_911_, v___x_910_);
if (v___x_912_ == 0)
{
return v___x_912_;
}
else
{
uint32_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 57;
v___x_914_ = lean_uint32_dec_le(v___x_910_, v___x_913_);
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object* v_s_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Lake_isVerLike(v_s_915_);
lean_dec_ref(v_s_915_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object* v_k_935_, lean_object* v_v_936_, lean_object* v_t_937_){
_start:
{
if (lean_obj_tag(v_t_937_) == 0)
{
lean_object* v_size_938_; lean_object* v_k_939_; lean_object* v_v_940_; lean_object* v_l_941_; lean_object* v_r_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1222_; 
v_size_938_ = lean_ctor_get(v_t_937_, 0);
v_k_939_ = lean_ctor_get(v_t_937_, 1);
v_v_940_ = lean_ctor_get(v_t_937_, 2);
v_l_941_ = lean_ctor_get(v_t_937_, 3);
v_r_942_ = lean_ctor_get(v_t_937_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_t_937_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_944_ = v_t_937_;
v_isShared_945_ = v_isSharedCheck_1222_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_r_942_);
lean_inc(v_l_941_);
lean_inc(v_v_940_);
lean_inc(v_k_939_);
lean_inc(v_size_938_);
lean_dec(v_t_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1222_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v___x_946_; 
v___x_946_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_935_, v_k_939_);
switch(v___x_946_)
{
case 0:
{
lean_object* v_impl_947_; lean_object* v___x_948_; 
lean_dec(v_size_938_);
v_impl_947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_935_, v_v_936_, v_l_941_);
v___x_948_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_942_) == 0)
{
lean_object* v_size_949_; lean_object* v_size_950_; lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v_l_953_; lean_object* v_r_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_size_949_ = lean_ctor_get(v_r_942_, 0);
v_size_950_ = lean_ctor_get(v_impl_947_, 0);
lean_inc(v_size_950_);
v_k_951_ = lean_ctor_get(v_impl_947_, 1);
lean_inc(v_k_951_);
v_v_952_ = lean_ctor_get(v_impl_947_, 2);
lean_inc(v_v_952_);
v_l_953_ = lean_ctor_get(v_impl_947_, 3);
lean_inc(v_l_953_);
v_r_954_ = lean_ctor_get(v_impl_947_, 4);
lean_inc(v_r_954_);
v___x_955_ = lean_unsigned_to_nat(3u);
v___x_956_ = lean_nat_mul(v___x_955_, v_size_949_);
v___x_957_ = lean_nat_dec_lt(v___x_956_, v_size_950_);
lean_dec(v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v_r_954_);
lean_dec(v_l_953_);
lean_dec(v_v_952_);
lean_dec(v_k_951_);
v___x_958_ = lean_nat_add(v___x_948_, v_size_950_);
lean_dec(v_size_950_);
v___x_959_ = lean_nat_add(v___x_958_, v_size_949_);
lean_dec(v___x_958_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 3, v_impl_947_);
lean_ctor_set(v___x_944_, 0, v___x_959_);
v___x_961_ = v___x_944_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_impl_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_r_942_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1028_; 
v_isSharedCheck_1028_ = !lean_is_exclusive(v_impl_947_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1029_ = lean_ctor_get(v_impl_947_, 4);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_impl_947_, 3);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_impl_947_, 2);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_impl_947_, 1);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_impl_947_, 0);
lean_dec(v_unused_1033_);
v___x_964_ = v_impl_947_;
v_isShared_965_ = v_isSharedCheck_1028_;
goto v_resetjp_963_;
}
else
{
lean_dec(v_impl_947_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1028_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_size_966_; lean_object* v_size_967_; lean_object* v_k_968_; lean_object* v_v_969_; lean_object* v_l_970_; lean_object* v_r_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_size_966_ = lean_ctor_get(v_l_953_, 0);
v_size_967_ = lean_ctor_get(v_r_954_, 0);
v_k_968_ = lean_ctor_get(v_r_954_, 1);
v_v_969_ = lean_ctor_get(v_r_954_, 2);
v_l_970_ = lean_ctor_get(v_r_954_, 3);
v_r_971_ = lean_ctor_get(v_r_954_, 4);
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = lean_nat_mul(v___x_972_, v_size_966_);
v___x_974_ = lean_nat_dec_lt(v_size_967_, v___x_973_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1003_; 
lean_inc(v_r_971_);
lean_inc(v_l_970_);
lean_inc(v_v_969_);
lean_inc(v_k_968_);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_r_954_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1004_ = lean_ctor_get(v_r_954_, 4);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_r_954_, 3);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_r_954_, 2);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_r_954_, 1);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_r_954_, 0);
lean_dec(v_unused_1008_);
v___x_976_ = v_r_954_;
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
else
{
lean_dec(v_r_954_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___x_991_; lean_object* v___y_993_; 
v___x_978_ = lean_nat_add(v___x_948_, v_size_950_);
lean_dec(v_size_950_);
v___x_979_ = lean_nat_add(v___x_978_, v_size_949_);
lean_dec(v___x_978_);
v___x_991_ = lean_nat_add(v___x_948_, v_size_966_);
if (lean_obj_tag(v_l_970_) == 0)
{
lean_object* v_size_1001_; 
v_size_1001_ = lean_ctor_get(v_l_970_, 0);
lean_inc(v_size_1001_);
v___y_993_ = v_size_1001_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___y_993_ = v___x_1002_;
goto v___jp_992_;
}
v___jp_980_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_nat_add(v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec(v___y_982_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 4, v_r_942_);
lean_ctor_set(v___x_976_, 3, v_r_971_);
lean_ctor_set(v___x_976_, 2, v_v_940_);
lean_ctor_set(v___x_976_, 1, v_k_939_);
lean_ctor_set(v___x_976_, 0, v___x_984_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_r_971_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_r_942_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v___x_986_);
lean_ctor_set(v___x_964_, 3, v___y_981_);
lean_ctor_set(v___x_964_, 2, v_v_969_);
lean_ctor_set(v___x_964_, 1, v_k_968_);
lean_ctor_set(v___x_964_, 0, v___x_979_);
v___x_988_ = v___x_964_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_k_968_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_v_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v___y_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
v___jp_992_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_nat_add(v___x_991_, v___y_993_);
lean_dec(v___y_993_);
lean_dec(v___x_991_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_l_970_);
lean_ctor_set(v___x_944_, 3, v_l_953_);
lean_ctor_set(v___x_944_, 2, v_v_952_);
lean_ctor_set(v___x_944_, 1, v_k_951_);
lean_ctor_set(v___x_944_, 0, v___x_994_);
v___x_996_ = v___x_944_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_k_951_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_v_952_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_l_953_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_l_970_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = lean_nat_add(v___x_948_, v_size_949_);
if (lean_obj_tag(v_r_971_) == 0)
{
lean_object* v_size_998_; 
v_size_998_ = lean_ctor_get(v_r_971_, 0);
lean_inc(v_size_998_);
v___y_981_ = v___x_996_;
v___y_982_ = v___x_997_;
v___y_983_ = v_size_998_;
goto v___jp_980_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___y_981_ = v___x_996_;
v___y_982_ = v___x_997_;
v___y_983_ = v___x_999_;
goto v___jp_980_;
}
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_del_object(v___x_944_);
v___x_1009_ = lean_nat_add(v___x_948_, v_size_950_);
lean_dec(v_size_950_);
v___x_1010_ = lean_nat_add(v___x_1009_, v_size_949_);
lean_dec(v___x_1009_);
v___x_1011_ = lean_nat_add(v___x_948_, v_size_949_);
v___x_1012_ = lean_nat_add(v___x_1011_, v_size_967_);
lean_dec(v___x_1011_);
lean_inc_ref(v_r_942_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v_r_942_);
lean_ctor_set(v___x_964_, 3, v_r_954_);
lean_ctor_set(v___x_964_, 2, v_v_940_);
lean_ctor_set(v___x_964_, 1, v_k_939_);
lean_ctor_set(v___x_964_, 0, v___x_1012_);
v___x_1014_ = v___x_964_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_r_954_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_r_942_);
v___x_1014_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_isSharedCheck_1021_ = !lean_is_exclusive(v_r_942_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1022_ = lean_ctor_get(v_r_942_, 4);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_942_, 3);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_r_942_, 2);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_r_942_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_r_942_, 0);
lean_dec(v_unused_1026_);
v___x_1016_ = v_r_942_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v_r_942_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 4, v___x_1014_);
lean_ctor_set(v___x_1016_, 3, v_l_953_);
lean_ctor_set(v___x_1016_, 2, v_v_952_);
lean_ctor_set(v___x_1016_, 1, v_k_951_);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_951_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_952_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_l_953_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v___x_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1034_; 
v_l_1034_ = lean_ctor_get(v_impl_947_, 3);
lean_inc(v_l_1034_);
if (lean_obj_tag(v_l_1034_) == 0)
{
lean_object* v_r_1035_; lean_object* v_k_1036_; lean_object* v_v_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1048_; 
v_r_1035_ = lean_ctor_get(v_impl_947_, 4);
v_k_1036_ = lean_ctor_get(v_impl_947_, 1);
v_v_1037_ = lean_ctor_get(v_impl_947_, 2);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_impl_947_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; lean_object* v_unused_1050_; 
v_unused_1049_ = lean_ctor_get(v_impl_947_, 3);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_impl_947_, 0);
lean_dec(v_unused_1050_);
v___x_1039_ = v_impl_947_;
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_r_1035_);
lean_inc(v_v_1037_);
lean_inc(v_k_1036_);
lean_dec(v_impl_947_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v_r_1035_);
lean_ctor_set(v___x_1039_, 2, v_v_940_);
lean_ctor_set(v___x_1039_, 1, v_k_939_);
lean_ctor_set(v___x_1039_, 0, v___x_948_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_r_1035_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_r_1035_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v___x_1043_);
lean_ctor_set(v___x_944_, 3, v_l_1034_);
lean_ctor_set(v___x_944_, 2, v_v_1037_);
lean_ctor_set(v___x_944_, 1, v_k_1036_);
lean_ctor_set(v___x_944_, 0, v___x_1041_);
v___x_1045_ = v___x_944_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_k_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_v_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_l_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_r_1051_; 
v_r_1051_ = lean_ctor_get(v_impl_947_, 4);
lean_inc(v_r_1051_);
if (lean_obj_tag(v_r_1051_) == 0)
{
lean_object* v_k_1052_; lean_object* v_v_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1076_; 
v_k_1052_ = lean_ctor_get(v_impl_947_, 1);
v_v_1053_ = lean_ctor_get(v_impl_947_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_impl_947_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1077_ = lean_ctor_get(v_impl_947_, 4);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_impl_947_, 3);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_impl_947_, 0);
lean_dec(v_unused_1079_);
v___x_1055_ = v_impl_947_;
v_isShared_1056_ = v_isSharedCheck_1076_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_v_1053_);
lean_inc(v_k_1052_);
lean_dec(v_impl_947_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1076_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_k_1057_; lean_object* v_v_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1072_; 
v_k_1057_ = lean_ctor_get(v_r_1051_, 1);
v_v_1058_ = lean_ctor_get(v_r_1051_, 2);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_r_1051_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; 
v_unused_1073_ = lean_ctor_get(v_r_1051_, 4);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_r_1051_, 3);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_r_1051_, 0);
lean_dec(v_unused_1075_);
v___x_1060_ = v_r_1051_;
v_isShared_1061_ = v_isSharedCheck_1072_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_v_1058_);
lean_inc(v_k_1057_);
lean_dec(v_r_1051_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1072_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_unsigned_to_nat(3u);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 4, v_l_1034_);
lean_ctor_set(v___x_1060_, 3, v_l_1034_);
lean_ctor_set(v___x_1060_, 2, v_v_1053_);
lean_ctor_set(v___x_1060_, 1, v_k_1052_);
lean_ctor_set(v___x_1060_, 0, v___x_948_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_k_1052_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_v_1053_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_l_1034_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_l_1034_);
v___x_1064_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v_l_1034_);
lean_ctor_set(v___x_1055_, 2, v_v_940_);
lean_ctor_set(v___x_1055_, 1, v_k_939_);
lean_ctor_set(v___x_1055_, 0, v___x_948_);
v___x_1066_ = v___x_1055_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_l_1034_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_l_1034_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v___x_1066_);
lean_ctor_set(v___x_944_, 3, v___x_1064_);
lean_ctor_set(v___x_944_, 2, v_v_1058_);
lean_ctor_set(v___x_944_, 1, v_k_1057_);
lean_ctor_set(v___x_944_, 0, v___x_1062_);
v___x_1068_ = v___x_944_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_k_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_v_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(2u);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_r_1051_);
lean_ctor_set(v___x_944_, 3, v_impl_947_);
lean_ctor_set(v___x_944_, 0, v___x_1080_);
v___x_1082_ = v___x_944_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_impl_947_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_r_1051_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1085_; 
lean_dec(v_v_940_);
lean_dec(v_k_939_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v_v_936_);
lean_ctor_set(v___x_944_, 1, v_k_935_);
v___x_1085_ = v___x_944_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_size_938_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_935_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_936_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_l_941_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_r_942_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
default: 
{
lean_object* v_impl_1087_; lean_object* v___x_1088_; 
lean_dec(v_size_938_);
v_impl_1087_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_935_, v_v_936_, v_r_942_);
v___x_1088_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_941_) == 0)
{
lean_object* v_size_1089_; lean_object* v_size_1090_; lean_object* v_k_1091_; lean_object* v_v_1092_; lean_object* v_l_1093_; lean_object* v_r_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_size_1089_ = lean_ctor_get(v_l_941_, 0);
v_size_1090_ = lean_ctor_get(v_impl_1087_, 0);
lean_inc(v_size_1090_);
v_k_1091_ = lean_ctor_get(v_impl_1087_, 1);
lean_inc(v_k_1091_);
v_v_1092_ = lean_ctor_get(v_impl_1087_, 2);
lean_inc(v_v_1092_);
v_l_1093_ = lean_ctor_get(v_impl_1087_, 3);
lean_inc(v_l_1093_);
v_r_1094_ = lean_ctor_get(v_impl_1087_, 4);
lean_inc(v_r_1094_);
v___x_1095_ = lean_unsigned_to_nat(3u);
v___x_1096_ = lean_nat_mul(v___x_1095_, v_size_1089_);
v___x_1097_ = lean_nat_dec_lt(v___x_1096_, v_size_1090_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_dec(v_r_1094_);
lean_dec(v_l_1093_);
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
v___x_1098_ = lean_nat_add(v___x_1088_, v_size_1089_);
v___x_1099_ = lean_nat_add(v___x_1098_, v_size_1090_);
lean_dec(v_size_1090_);
lean_dec(v___x_1098_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_impl_1087_);
lean_ctor_set(v___x_944_, 0, v___x_1099_);
v___x_1101_ = v___x_944_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_l_941_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_impl_1087_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v_impl_1087_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1167_ = lean_ctor_get(v_impl_1087_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_impl_1087_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_impl_1087_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_impl_1087_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_impl_1087_, 0);
lean_dec(v_unused_1171_);
v___x_1104_ = v_impl_1087_;
v_isShared_1105_ = v_isSharedCheck_1166_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_impl_1087_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1166_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_size_1106_; lean_object* v_k_1107_; lean_object* v_v_1108_; lean_object* v_l_1109_; lean_object* v_r_1110_; lean_object* v_size_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_size_1106_ = lean_ctor_get(v_l_1093_, 0);
v_k_1107_ = lean_ctor_get(v_l_1093_, 1);
v_v_1108_ = lean_ctor_get(v_l_1093_, 2);
v_l_1109_ = lean_ctor_get(v_l_1093_, 3);
v_r_1110_ = lean_ctor_get(v_l_1093_, 4);
v_size_1111_ = lean_ctor_get(v_r_1094_, 0);
v___x_1112_ = lean_unsigned_to_nat(2u);
v___x_1113_ = lean_nat_mul(v___x_1112_, v_size_1111_);
v___x_1114_ = lean_nat_dec_lt(v_size_1106_, v___x_1113_);
lean_dec(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1142_; 
lean_inc(v_r_1110_);
lean_inc(v_l_1109_);
lean_inc(v_v_1108_);
lean_inc(v_k_1107_);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_l_1093_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1143_ = lean_ctor_get(v_l_1093_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_1093_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_l_1093_, 2);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_l_1093_, 1);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_l_1093_, 0);
lean_dec(v_unused_1147_);
v___x_1116_ = v_l_1093_;
v_isShared_1117_ = v_isSharedCheck_1142_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_l_1093_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1142_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1132_; 
v___x_1118_ = lean_nat_add(v___x_1088_, v_size_1089_);
v___x_1119_ = lean_nat_add(v___x_1118_, v_size_1090_);
lean_dec(v_size_1090_);
if (lean_obj_tag(v_l_1109_) == 0)
{
lean_object* v_size_1140_; 
v_size_1140_ = lean_ctor_get(v_l_1109_, 0);
lean_inc(v_size_1140_);
v___y_1132_ = v_size_1140_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___y_1132_ = v___x_1141_;
goto v___jp_1131_;
}
v___jp_1120_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_nat_add(v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v_r_1094_);
lean_ctor_set(v___x_1116_, 3, v_r_1110_);
lean_ctor_set(v___x_1116_, 2, v_v_1092_);
lean_ctor_set(v___x_1116_, 1, v_k_1091_);
lean_ctor_set(v___x_1116_, 0, v___x_1124_);
v___x_1126_ = v___x_1116_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_r_1110_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_r_1094_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 4, v___x_1126_);
lean_ctor_set(v___x_1104_, 3, v___y_1121_);
lean_ctor_set(v___x_1104_, 2, v_v_1108_);
lean_ctor_set(v___x_1104_, 1, v_k_1107_);
lean_ctor_set(v___x_1104_, 0, v___x_1119_);
v___x_1128_ = v___x_1104_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_k_1107_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_v_1108_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v___y_1121_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_nat_add(v___x_1118_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec(v___x_1118_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_l_1109_);
lean_ctor_set(v___x_944_, 0, v___x_1133_);
v___x_1135_ = v___x_944_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_l_941_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_l_1109_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_nat_add(v___x_1088_, v_size_1111_);
if (lean_obj_tag(v_r_1110_) == 0)
{
lean_object* v_size_1137_; 
v_size_1137_ = lean_ctor_get(v_r_1110_, 0);
lean_inc(v_size_1137_);
v___y_1121_ = v___x_1135_;
v___y_1122_ = v___x_1136_;
v___y_1123_ = v_size_1137_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___y_1121_ = v___x_1135_;
v___y_1122_ = v___x_1136_;
v___y_1123_ = v___x_1138_;
goto v___jp_1120_;
}
}
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_del_object(v___x_944_);
v___x_1148_ = lean_nat_add(v___x_1088_, v_size_1089_);
v___x_1149_ = lean_nat_add(v___x_1148_, v_size_1090_);
lean_dec(v_size_1090_);
v___x_1150_ = lean_nat_add(v___x_1148_, v_size_1106_);
lean_dec(v___x_1148_);
lean_inc_ref(v_l_941_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 4, v_l_1093_);
lean_ctor_set(v___x_1104_, 3, v_l_941_);
lean_ctor_set(v___x_1104_, 2, v_v_940_);
lean_ctor_set(v___x_1104_, 1, v_k_939_);
lean_ctor_set(v___x_1104_, 0, v___x_1150_);
v___x_1152_ = v___x_1104_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_l_941_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_l_1093_);
v___x_1152_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v_l_941_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1160_ = lean_ctor_get(v_l_941_, 4);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_l_941_, 3);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_l_941_, 2);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_l_941_, 1);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_l_941_, 0);
lean_dec(v_unused_1164_);
v___x_1154_ = v_l_941_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v_l_941_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 4, v_r_1094_);
lean_ctor_set(v___x_1154_, 3, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v_v_1092_);
lean_ctor_set(v___x_1154_, 1, v_k_1091_);
lean_ctor_set(v___x_1154_, 0, v___x_1149_);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_r_1094_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1172_; 
v_l_1172_ = lean_ctor_get(v_impl_1087_, 3);
lean_inc(v_l_1172_);
if (lean_obj_tag(v_l_1172_) == 0)
{
lean_object* v_r_1173_; lean_object* v_k_1174_; lean_object* v_v_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1198_; 
v_r_1173_ = lean_ctor_get(v_impl_1087_, 4);
v_k_1174_ = lean_ctor_get(v_impl_1087_, 1);
v_v_1175_ = lean_ctor_get(v_impl_1087_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_impl_1087_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_impl_1087_, 3);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_impl_1087_, 0);
lean_dec(v_unused_1200_);
v___x_1177_ = v_impl_1087_;
v_isShared_1178_ = v_isSharedCheck_1198_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_r_1173_);
lean_inc(v_v_1175_);
lean_inc(v_k_1174_);
lean_dec(v_impl_1087_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1198_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_k_1179_; lean_object* v_v_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1194_; 
v_k_1179_ = lean_ctor_get(v_l_1172_, 1);
v_v_1180_ = lean_ctor_get(v_l_1172_, 2);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_l_1172_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; lean_object* v_unused_1196_; lean_object* v_unused_1197_; 
v_unused_1195_ = lean_ctor_get(v_l_1172_, 4);
lean_dec(v_unused_1195_);
v_unused_1196_ = lean_ctor_get(v_l_1172_, 3);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_l_1172_, 0);
lean_dec(v_unused_1197_);
v___x_1182_ = v_l_1172_;
v_isShared_1183_ = v_isSharedCheck_1194_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_v_1180_);
lean_inc(v_k_1179_);
lean_dec(v_l_1172_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1194_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1173_, 2);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 4, v_r_1173_);
lean_ctor_set(v___x_1182_, 3, v_r_1173_);
lean_ctor_set(v___x_1182_, 2, v_v_940_);
lean_ctor_set(v___x_1182_, 1, v_k_939_);
lean_ctor_set(v___x_1182_, 0, v___x_1088_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_r_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_r_1173_);
v___x_1186_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1188_; 
lean_inc(v_r_1173_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 3, v_r_1173_);
lean_ctor_set(v___x_1177_, 0, v___x_1088_);
v___x_1188_ = v___x_1177_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1174_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1175_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_r_1173_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_r_1173_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v___x_1188_);
lean_ctor_set(v___x_944_, 3, v___x_1186_);
lean_ctor_set(v___x_944_, 2, v_v_1180_);
lean_ctor_set(v___x_944_, 1, v_k_1179_);
lean_ctor_set(v___x_944_, 0, v___x_1184_);
v___x_1190_ = v___x_944_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1180_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
else
{
lean_object* v_r_1201_; 
v_r_1201_ = lean_ctor_get(v_impl_1087_, 4);
lean_inc(v_r_1201_);
if (lean_obj_tag(v_r_1201_) == 0)
{
lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1214_; 
v_k_1202_ = lean_ctor_get(v_impl_1087_, 1);
v_v_1203_ = lean_ctor_get(v_impl_1087_, 2);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_impl_1087_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; lean_object* v_unused_1216_; lean_object* v_unused_1217_; 
v_unused_1215_ = lean_ctor_get(v_impl_1087_, 4);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_impl_1087_, 3);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_impl_1087_, 0);
lean_dec(v_unused_1217_);
v___x_1205_ = v_impl_1087_;
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_dec(v_impl_1087_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1214_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(3u);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v_l_1172_);
lean_ctor_set(v___x_1205_, 2, v_v_940_);
lean_ctor_set(v___x_1205_, 1, v_k_939_);
lean_ctor_set(v___x_1205_, 0, v___x_1088_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_l_1172_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_l_1172_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_r_1201_);
lean_ctor_set(v___x_944_, 3, v___x_1209_);
lean_ctor_set(v___x_944_, 2, v_v_1203_);
lean_ctor_set(v___x_944_, 1, v_k_1202_);
lean_ctor_set(v___x_944_, 0, v___x_1207_);
v___x_1211_ = v___x_944_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_r_1201_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(2u);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_impl_1087_);
lean_ctor_set(v___x_944_, 3, v_r_1201_);
lean_ctor_set(v___x_944_, 0, v___x_1218_);
v___x_1220_ = v___x_944_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_r_1201_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_impl_1087_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
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
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_k_935_);
lean_ctor_set(v___x_1224_, 2, v_v_936_);
lean_ctor_set(v___x_1224_, 3, v_t_937_);
lean_ctor_set(v___x_1224_, 4, v_t_937_);
return v___x_1224_;
}
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__0(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1225_ = lean_box(1);
v___x_1226_ = ((lean_object*)(l_Lake_StrPat_verLike));
v___x_1227_ = ((lean_object*)(l_Lake_StrPat_verLike___closed__2));
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1227_, v___x_1226_, v___x_1225_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_obj_once(&l_Lake_versionTagPresets___closed__0, &l_Lake_versionTagPresets___closed__0_once, _init_l_Lake_versionTagPresets___closed__0);
v___x_1230_ = ((lean_object*)(l_Lake_defaultVersionTags));
v___x_1231_ = ((lean_object*)(l_Lake_defaultVersionTags___closed__1));
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v___x_1231_, v___x_1230_, v___x_1229_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lake_versionTagPresets(void){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_obj_once(&l_Lake_versionTagPresets___closed__1, &l_Lake_versionTagPresets___closed__1_once, _init_l_Lake_versionTagPresets___closed__1);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object* v_00_u03b2_1234_, lean_object* v_k_1235_, lean_object* v_v_1236_, lean_object* v_t_1237_, lean_object* v_hl_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_1235_, v_v_1236_, v_t_1237_);
return v___x_1239_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
