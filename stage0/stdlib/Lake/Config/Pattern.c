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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___redArg(lean_object* v_x_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_tag_nat(v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___redArg___boxed(lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_PatternDescr_ctorIdx___impl___redArg(v_x_126_);
lean_dec_ref(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_x_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_tag_nat(v_x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorIdx___impl___boxed(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_PatternDescr_ctorIdx___impl(v_00_u03b1_132_, v_00_u03b2_133_, v_x_134_);
lean_dec_ref(v_x_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___redArg(lean_object* v_t_136_, lean_object* v_k_137_){
_start:
{
if (lean_obj_tag(v_t_136_) == 3)
{
lean_object* v_p_138_; lean_object* v___x_139_; 
v_p_138_ = lean_ctor_get(v_t_136_, 0);
lean_inc(v_p_138_);
lean_dec_ref_known(v_t_136_, 1);
v___x_139_ = lean_apply_1(v_k_137_, v_p_138_);
return v___x_139_;
}
else
{
lean_object* v_p_140_; lean_object* v___x_141_; 
v_p_140_ = lean_ctor_get(v_t_136_, 0);
lean_inc_ref(v_p_140_);
lean_dec_ref(v_t_136_);
v___x_141_ = lean_apply_1(v_k_137_, v_p_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_motive__2_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_146_, v_k_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_ctorElim___boxed(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_motive__2_152_, lean_object* v_ctorIdx_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_k_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lake_PatternDescr_ctorElim(v_00_u03b1_150_, v_00_u03b2_151_, v_motive__2_152_, v_ctorIdx_153_, v_t_154_, v_h_155_, v_k_156_);
lean_dec(v_ctorIdx_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim___redArg(lean_object* v_t_158_, lean_object* v_not_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_158_, v_not_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_not_elim(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_motive__2_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_not_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_164_, v_not_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim___redArg(lean_object* v_t_168_, lean_object* v_all_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_168_, v_all_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_all_elim(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_motive__2_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_all_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_174_, v_all_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim___redArg(lean_object* v_t_178_, lean_object* v_any_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_178_, v_any_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_any_elim(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_motive__2_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_any_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_184_, v_any_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim___redArg(lean_object* v_t_188_, lean_object* v_coe_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_188_, v_coe_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_coe_elim(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_motive__2_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_coe_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lake_PatternDescr_ctorElim___redArg(v_t_194_, v_coe_196_);
return v___x_197_;
}
}
uint8_t l_Lake_instInhabitedPattern_default__1___redArg___lam__0(lean_object* v_x_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPattern_default__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_198_ = stack[0].m_obj;
uint8_t v_res_200_;
v_res_200_ = l_Lake_instInhabitedPattern_default__1___redArg___lam__0(v_x_198_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___lam__0___boxed(lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lake_instInhabitedPattern_default__1___redArg___lam__0(v_x_201_);
lean_dec(v_x_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
lean_object* l_Lake_instInhabitedPattern_default__1___redArg(){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__1));
return v___x_210_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPattern_default__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_211_;
v_res_211_ = l_Lake_instInhabitedPattern_default__1___redArg();
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___boxed(lean_object* v___dummy_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v_res_213_;
}
}
static lean_object* _init_l_Lake_instInhabitedPattern_default__1___closed__0(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_217_;
}
}
lean_object* l_Lake_instInhabitedPattern___redArg(){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPattern___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_220_;
v_res_220_ = l_Lake_instInhabitedPattern___redArg();
stack->m_obj
 = v_res_220_;
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
lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg(){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0);
return v___x_229_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPatternDescr_default__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_230_;
v_res_230_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg___boxed(lean_object* v___dummy_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v_res_232_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_236_;
}
}
lean_object* l_Lake_instInhabitedPatternDescr___redArg(){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lake_instInhabitedPatternDescr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_239_;
v_res_239_ = l_Lake_instInhabitedPatternDescr___redArg();
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg___boxed(lean_object* v___dummy_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_instInhabitedPatternDescr___redArg();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___lam__0(lean_object* v_p_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_246_, 0, v_p_245_);
return v___x_246_;
}
}
lean_object* l_Lake_instCoePatternDescr___redArg(){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_249_;
}
}
LEAN_EXPORT void l_Lake_instCoePatternDescr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_250_;
v_res_250_ = l_Lake_instCoePatternDescr___redArg();
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___boxed(lean_object* v___dummy_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_instCoePatternDescr___redArg();
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object* v_00_u03b2_253_, lean_object* v_00_u03b1_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_255_;
}
}
uint8_t l_Lake_Pattern_matches___redArg(lean_object* v_a_256_, lean_object* v_self_257_){
_start:
{
lean_object* v_filter_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_filter_258_ = lean_ctor_get(v_self_257_, 0);
lean_inc_ref(v_filter_258_);
lean_dec_ref(v_self_257_);
v___x_259_ = lean_apply_1(v_filter_258_, v_a_256_);
v___x_260_ = lean_unbox(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT void l_Lake_Pattern_matches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_256_ = stack[0].m_obj;
lean_object* v_self_257_ = stack[1].m_obj;
uint8_t v_res_261_;
v_res_261_ = l_Lake_Pattern_matches___redArg(v_a_256_, v_self_257_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object* v_a_262_, lean_object* v_self_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lake_Pattern_matches___redArg(v_a_262_, v_self_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
uint8_t l_Lake_Pattern_matches(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_a_268_, lean_object* v_self_269_){
_start:
{
lean_object* v_filter_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_filter_270_ = lean_ctor_get(v_self_269_, 0);
lean_inc_ref(v_filter_270_);
lean_dec_ref(v_self_269_);
v___x_271_ = lean_apply_1(v_filter_270_, v_a_268_);
v___x_272_ = lean_unbox(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT void l_Lake_Pattern_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_268_ = stack[2].m_obj;
lean_object* v_self_269_ = stack[3].m_obj;
uint8_t v_res_273_;
v_res_273_ = l_Lake_Pattern_matches(lean_box(0), lean_box(0), v_a_268_, v_self_269_);
stack->m_num = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_a_276_, lean_object* v_self_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Lake_Pattern_matches(v_00_u03b1_274_, v_00_u03b2_275_, v_a_276_, v_self_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
uint8_t l_Lake_instIsPatternPattern___redArg___lam__0(lean_object* v_self_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_filter_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_filter_282_ = lean_ctor_get(v_self_280_, 0);
lean_inc_ref(v_filter_282_);
lean_dec_ref(v_self_280_);
v___x_283_ = lean_apply_1(v_filter_282_, v___y_281_);
v___x_284_ = lean_unbox(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT void l_Lake_instIsPatternPattern___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_280_ = stack[0].m_obj;
lean_object* v___y_281_ = stack[1].m_obj;
uint8_t v_res_285_;
v_res_285_ = l_Lake_instIsPatternPattern___redArg___lam__0(v_self_280_, v___y_281_);
stack->m_num = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___lam__0___boxed(lean_object* v_self_286_, lean_object* v___y_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lake_instIsPatternPattern___redArg___lam__0(v_self_286_, v___y_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
lean_object* l_Lake_instIsPatternPattern___redArg(){
_start:
{
lean_object* v___f_292_; 
v___f_292_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_292_;
}
}
LEAN_EXPORT void l_Lake_instIsPatternPattern___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_293_;
v_res_293_ = l_Lake_instIsPatternPattern___redArg();
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___boxed(lean_object* v___dummy_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_instIsPatternPattern___redArg();
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_){
_start:
{
lean_object* v___f_298_; 
v___f_298_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_298_;
}
}
uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object* v_val_299_, uint8_t v___x_300_, lean_object* v_v_301_){
_start:
{
lean_object* v_filter_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_filter_302_ = lean_ctor_get(v_v_301_, 0);
lean_inc_ref(v_filter_302_);
lean_dec_ref(v_v_301_);
v___x_303_ = lean_apply_1(v_filter_302_, v_val_299_);
v___x_304_ = lean_unbox(v___x_303_);
if (v___x_304_ == 0)
{
return v___x_300_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
}
}
LEAN_EXPORT void l_Lake_PatternDescr_matches___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_299_ = stack[0].m_obj;
uint8_t v___x_300_ = stack[1].m_num;
lean_object* v_v_301_ = stack[2].m_obj;
uint8_t v_res_306_;
v_res_306_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_299_, v___x_300_, v_v_301_);
stack->m_num = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object* v_val_307_, lean_object* v___x_308_, lean_object* v_v_309_){
_start:
{
uint8_t v___x_202__boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v___x_202__boxed_310_ = lean_unbox(v___x_308_);
v_res_311_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_307_, v___x_202__boxed_310_, v_v_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object* v_val_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_filter_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_filter_315_ = lean_ctor_get(v_x_314_, 0);
lean_inc_ref(v_filter_315_);
lean_dec_ref(v_x_314_);
v___x_316_ = lean_apply_1(v_filter_315_, v_val_313_);
v___x_317_ = lean_unbox(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Lake_PatternDescr_matches___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_313_ = stack[0].m_obj;
lean_object* v_x_314_ = stack[1].m_obj;
uint8_t v_res_318_;
v_res_318_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_313_, v_x_314_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object* v_val_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_319_, v_x_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
uint8_t l_Lake_PatternDescr_matches___redArg(lean_object* v_inst_342_, lean_object* v_val_343_, lean_object* v_self_344_){
_start:
{
switch(lean_obj_tag(v_self_344_))
{
case 0:
{
lean_object* v_p_345_; lean_object* v_filter_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
lean_dec_ref(v_inst_342_);
v_p_345_ = lean_ctor_get(v_self_344_, 0);
lean_inc_ref(v_p_345_);
lean_dec_ref_known(v_self_344_, 1);
v_filter_346_ = lean_ctor_get(v_p_345_, 0);
lean_inc_ref(v_filter_346_);
lean_dec_ref(v_p_345_);
v___x_347_ = lean_apply_1(v_filter_346_, v_val_343_);
v___x_348_ = lean_unbox(v___x_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; 
v___x_349_ = 1;
return v___x_349_;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
case 1:
{
lean_object* v_ps_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
lean_dec_ref(v_inst_342_);
v_ps_351_ = lean_ctor_get(v_self_344_, 0);
lean_inc_ref(v_ps_351_);
lean_dec_ref_known(v_self_344_, 1);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_array_get_size(v_ps_351_);
v___x_354_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_355_ = lean_nat_dec_lt(v___x_352_, v___x_353_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
lean_dec_ref(v_ps_351_);
lean_dec(v_val_343_);
v___x_356_ = 1;
return v___x_356_;
}
else
{
if (v___x_355_ == 0)
{
lean_dec_ref(v_ps_351_);
lean_dec(v_val_343_);
return v___x_355_;
}
else
{
lean_object* v___x_357_; lean_object* v___f_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_357_ = lean_box(v___x_355_);
v___f_358_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_358_, 0, v_val_343_);
lean_closure_set(v___f_358_, 1, v___x_357_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_353_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_354_, v___f_358_, v_ps_351_, v___x_359_, v___x_360_);
v___x_362_ = lean_unbox(v___x_361_);
lean_dec(v___x_361_);
if (v___x_362_ == 0)
{
return v___x_355_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
}
case 2:
{
lean_object* v_ps_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
lean_dec_ref(v_inst_342_);
v_ps_364_ = lean_ctor_get(v_self_344_, 0);
lean_inc_ref(v_ps_364_);
lean_dec_ref_known(v_self_344_, 1);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_array_get_size(v_ps_364_);
v___x_367_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_368_ = lean_nat_dec_lt(v___x_365_, v___x_366_);
if (v___x_368_ == 0)
{
lean_dec_ref(v_ps_364_);
lean_dec(v_val_343_);
return v___x_368_;
}
else
{
if (v___x_368_ == 0)
{
lean_dec_ref(v_ps_364_);
lean_dec(v_val_343_);
return v___x_368_;
}
else
{
lean_object* v___f_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___f_369_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_369_, 0, v_val_343_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_366_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_367_, v___f_369_, v_ps_364_, v___x_370_, v___x_371_);
v___x_373_ = lean_unbox(v___x_372_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
}
default: 
{
lean_object* v_p_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_p_374_ = lean_ctor_get(v_self_344_, 0);
lean_inc(v_p_374_);
lean_dec_ref_known(v_self_344_, 1);
v___x_375_ = lean_apply_2(v_inst_342_, v_p_374_, v_val_343_);
v___x_376_ = lean_unbox(v___x_375_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT void l_Lake_PatternDescr_matches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_342_ = stack[0].m_obj;
lean_object* v_val_343_ = stack[1].m_obj;
lean_object* v_self_344_ = stack[2].m_obj;
uint8_t v_res_377_;
v_res_377_ = l_Lake_PatternDescr_matches___redArg(v_inst_342_, v_val_343_, v_self_344_);
stack->m_num = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object* v_inst_378_, lean_object* v_val_379_, lean_object* v_self_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Lake_PatternDescr_matches___redArg(v_inst_378_, v_val_379_, v_self_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
uint8_t l_Lake_PatternDescr_matches(lean_object* v_00_u03b2_383_, lean_object* v_00_u03b1_384_, lean_object* v_inst_385_, lean_object* v_val_386_, lean_object* v_self_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l_Lake_PatternDescr_matches___redArg(v_inst_385_, v_val_386_, v_self_387_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Lake_PatternDescr_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_385_ = stack[2].m_obj;
lean_object* v_val_386_ = stack[3].m_obj;
lean_object* v_self_387_ = stack[4].m_obj;
uint8_t v_res_389_;
v_res_389_ = l_Lake_PatternDescr_matches(lean_box(0), lean_box(0), v_inst_385_, v_val_386_, v_self_387_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object* v_00_u03b2_390_, lean_object* v_00_u03b1_391_, lean_object* v_inst_392_, lean_object* v_val_393_, lean_object* v_self_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lake_PatternDescr_matches(v_00_u03b2_390_, v_00_u03b1_391_, v_inst_392_, v_val_393_, v_self_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object* v_inst_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___boxed), 5, 3);
lean_closure_set(v___x_398_, 0, lean_box(0));
lean_closure_set(v___x_398_, 1, lean_box(0));
lean_closure_set(v___x_398_, 2, v_inst_397_);
v___x_399_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_399_, 0, lean_box(0));
lean_closure_set(v___x_399_, 1, lean_box(0));
lean_closure_set(v___x_399_, 2, lean_box(0));
lean_closure_set(v___x_399_, 3, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object* v_00_u03b2_400_, lean_object* v_00_u03b1_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object* v_f_404_, lean_object* v_name_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v_f_404_);
lean_ctor_set(v___x_407_, 1, v_name_405_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_f_410_, lean_object* v_name_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_413_, 0, v_f_410_);
lean_ctor_set(v___x_413_, 1, v_name_411_);
lean_ctor_set(v___x_413_, 2, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___lam__0(lean_object* v_f_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_417_, 0, v_f_414_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
return v___x_417_;
}
}
lean_object* l_Lake_instCoeForallBoolPattern___redArg(){
_start:
{
lean_object* v___f_420_; 
v___f_420_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_420_;
}
}
LEAN_EXPORT void l_Lake_instCoeForallBoolPattern___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_421_;
v_res_421_ = l_Lake_instCoeForallBoolPattern___redArg();
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___boxed(lean_object* v___dummy_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lake_instCoeForallBoolPattern___redArg();
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_){
_start:
{
lean_object* v___f_426_; 
v___f_426_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_426_;
}
}
uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object* v_inst_427_, lean_object* v_descr_428_, lean_object* v_x_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = l_Lake_PatternDescr_matches___redArg(v_inst_427_, v_x_429_, v_descr_428_);
return v___x_430_;
}
}
LEAN_EXPORT void l_Lake_Pattern_ofDescr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_427_ = stack[0].m_obj;
lean_object* v_descr_428_ = stack[1].m_obj;
lean_object* v_x_429_ = stack[2].m_obj;
uint8_t v_res_431_;
v_res_431_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_427_, v_descr_428_, v_x_429_);
stack->m_num = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object* v_inst_432_, lean_object* v_descr_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_432_, v_descr_433_, v_x_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object* v_inst_437_, lean_object* v_descr_438_, lean_object* v_name_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc_ref(v_descr_438_);
v___f_440_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_440_, 0, v_inst_437_);
lean_closure_set(v___f_440_, 1, v_descr_438_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_descr_438_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v___f_440_);
lean_ctor_set(v___x_442_, 1, v_name_439_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object* v_00_u03b2_443_, lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_descr_446_, lean_object* v_name_447_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref(v_descr_446_);
v___f_448_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_448_, 0, v_inst_445_);
lean_closure_set(v___f_448_, 1, v_descr_446_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_descr_446_);
v___x_450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_450_, 0, v___f_448_);
lean_ctor_set(v___x_450_, 1, v_name_447_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
return v___x_450_;
}
}
uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object* v_inst_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lake_PatternDescr_matches___redArg(v_inst_451_, v_x_453_, v_x_452_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_451_ = stack[0].m_obj;
lean_object* v_x_452_ = stack[1].m_obj;
lean_object* v_x_453_ = stack[2].m_obj;
uint8_t v_res_455_;
v_res_455_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_451_, v_x_452_, v_x_453_);
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object* v_inst_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_456_, v_x_457_, v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object* v_inst_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc_ref(v_x_462_);
v___f_463_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_463_, 0, v_inst_461_);
lean_closure_set(v___f_463_, 1, v_x_462_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_x_462_);
v___x_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_466_, 0, v___f_463_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object* v_inst_467_){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_468_, 0, v_inst_467_);
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object* v_00_u03b2_469_, lean_object* v_00_u03b1_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v___f_472_; 
v___f_472_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_472_, 0, v_inst_471_);
return v___f_472_;
}
}
uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object* v_inst_473_, lean_object* v___x_474_, lean_object* v_x_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = l_Lake_PatternDescr_matches___redArg(v_inst_473_, v_x_475_, v___x_474_);
return v___x_476_;
}
}
LEAN_EXPORT void l_Lake_Pattern_not___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_473_ = stack[0].m_obj;
lean_object* v___x_474_ = stack[1].m_obj;
lean_object* v_x_475_ = stack[2].m_obj;
uint8_t v_res_477_;
v_res_477_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_473_, v___x_474_, v_x_475_);
stack->m_num = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object* v_inst_478_, lean_object* v___x_479_, lean_object* v_x_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_478_, v___x_479_, v_x_480_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object* v_inst_483_, lean_object* v_p_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_p_484_);
lean_inc_ref(v___x_485_);
v___f_486_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_486_, 0, v_inst_483_);
lean_closure_set(v___f_486_, 1, v___x_485_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_485_);
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v___f_486_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object* v_00_u03b2_490_, lean_object* v_00_u03b1_491_, lean_object* v_inst_492_, lean_object* v_p_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_p_493_);
lean_inc_ref(v___x_494_);
v___f_495_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_495_, 0, v_inst_492_);
lean_closure_set(v___f_495_, 1, v___x_494_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
v___x_498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_498_, 0, v___f_495_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
lean_ctor_set(v___x_498_, 2, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object* v_inst_499_, lean_object* v_ps_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_ps_500_);
lean_inc_ref(v___x_501_);
v___f_502_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_502_, 0, v_inst_499_);
lean_closure_set(v___f_502_, 1, v___x_501_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
v___x_505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_505_, 0, v___f_502_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object* v_00_u03b2_506_, lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_ps_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_ps_509_);
lean_inc_ref(v___x_510_);
v___f_511_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_511_, 0, v_inst_508_);
lean_closure_set(v___f_511_, 1, v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___f_511_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object* v_inst_515_, lean_object* v_ps_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_517_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_517_, 0, v_ps_516_);
lean_inc_ref(v___x_517_);
v___f_518_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_518_, 0, v_inst_515_);
lean_closure_set(v___f_518_, 1, v___x_517_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
v___x_521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_521_, 0, v___f_518_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object* v_00_u03b2_522_, lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_ps_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_526_, 0, v_ps_525_);
lean_inc_ref(v___x_526_);
v___f_527_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_527_, 0, v_inst_524_);
lean_closure_set(v___f_527_, 1, v___x_526_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_526_);
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v___f_527_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
return v___x_530_;
}
}
lean_object* l_Lake_PatternDescr_empty___redArg(){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_Lake_PatternDescr_empty___redArg___closed__1));
return v___x_536_;
}
}
LEAN_EXPORT void l_Lake_PatternDescr_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_537_;
v_res_537_ = l_Lake_PatternDescr_empty___redArg();
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg___boxed(lean_object* v___dummy_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_PatternDescr_empty___redArg();
return v_res_539_;
}
}
static lean_object* _init_l_Lake_PatternDescr_empty___closed__0(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lake_PatternDescr_empty___redArg();
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_543_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
v___x_549_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__2, &l_Lake_Pattern_empty___redArg___closed__2_once, _init_l_Lake_Pattern_empty___redArg___closed__2);
v___x_550_ = ((lean_object*)(l_Lake_Pattern_empty___redArg___closed__1));
v___f_551_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__0));
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___f_551_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_549_);
return v___x_552_;
}
}
lean_object* l_Lake_Pattern_empty___redArg(){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__3, &l_Lake_Pattern_empty___redArg___closed__3_once, _init_l_Lake_Pattern_empty___redArg___closed__3);
return v___x_554_;
}
}
LEAN_EXPORT void l_Lake_Pattern_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_555_;
v_res_555_ = l_Lake_Pattern_empty___redArg();
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg___boxed(lean_object* v___dummy_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_Pattern_empty___redArg();
return v_res_557_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__0(void){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lake_Pattern_empty___redArg();
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_561_;
}
}
lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg(){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_563_;
}
}
LEAN_EXPORT void l_Lake_instEmptyCollectionPatternDescr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_564_;
v_res_564_ = l_Lake_instEmptyCollectionPatternDescr___redArg();
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg___boxed(lean_object* v___dummy_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lake_instEmptyCollectionPatternDescr___redArg();
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_569_;
}
}
lean_object* l_Lake_instEmptyCollectionPattern___redArg(){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_571_;
}
}
LEAN_EXPORT void l_Lake_instEmptyCollectionPattern___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_572_;
v_res_572_ = l_Lake_instEmptyCollectionPattern___redArg();
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg___boxed(lean_object* v___dummy_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lake_instEmptyCollectionPattern___redArg();
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_577_;
}
}
lean_object* l_Lake_PatternDescr_star___redArg(){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Lake_PatternDescr_star___redArg___closed__0));
return v___x_581_;
}
}
LEAN_EXPORT void l_Lake_PatternDescr_star___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_582_;
v_res_582_ = l_Lake_PatternDescr_star___redArg();
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg___boxed(lean_object* v___dummy_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lake_PatternDescr_star___redArg();
return v_res_584_;
}
}
static lean_object* _init_l_Lake_PatternDescr_star___closed__0(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lake_PatternDescr_star___redArg();
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
return v___x_588_;
}
}
uint8_t l_Lake_Pattern_star___redArg___lam__0(lean_object* v_x_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = 1;
return v___x_590_;
}
}
LEAN_EXPORT void l_Lake_Pattern_star___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_589_ = stack[0].m_obj;
uint8_t v_res_591_;
v_res_591_ = l_Lake_Pattern_star___redArg___lam__0(v_x_589_);
stack->m_num = v_res_591_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___lam__0___boxed(lean_object* v_x_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Lake_Pattern_star___redArg___lam__0(v_x_592_);
lean_dec(v_x_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__4(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__3, &l_Lake_Pattern_star___redArg___closed__3_once, _init_l_Lake_Pattern_star___redArg___closed__3);
v___x_602_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__2));
v___f_603_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__0));
v___x_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_604_, 0, v___f_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
return v___x_604_;
}
}
lean_object* l_Lake_Pattern_star___redArg(){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__4, &l_Lake_Pattern_star___redArg___closed__4_once, _init_l_Lake_Pattern_star___redArg___closed__4);
return v___x_606_;
}
}
LEAN_EXPORT void l_Lake_Pattern_star___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_607_;
v_res_607_ = l_Lake_Pattern_star___redArg();
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___boxed(lean_object* v___dummy_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lake_Pattern_star___redArg();
return v_res_609_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__0(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lake_Pattern_star___redArg();
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lake_Pattern_star___closed__0, &l_Lake_Pattern_star___closed__0_once, _init_l_Lake_Pattern_star___closed__0);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl(lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_tag_nat(v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl___boxed(lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lake_StrPatDescr_ctorIdx___impl(v_x_616_);
lean_dec_ref(v_x_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object* v_t_618_, lean_object* v_k_619_){
_start:
{
lean_object* v_xs_620_; lean_object* v___x_621_; 
v_xs_620_ = lean_ctor_get(v_t_618_, 0);
lean_inc_ref(v_xs_620_);
lean_dec_ref(v_t_618_);
v___x_621_ = lean_apply_1(v_k_619_, v_xs_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object* v_motive_622_, lean_object* v_ctorIdx_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_k_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_624_, v_k_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object* v_motive_628_, lean_object* v_ctorIdx_629_, lean_object* v_t_630_, lean_object* v_h_631_, lean_object* v_k_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lake_StrPatDescr_ctorElim(v_motive_628_, v_ctorIdx_629_, v_t_630_, v_h_631_, v_k_632_);
lean_dec(v_ctorIdx_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object* v_t_634_, lean_object* v_mem_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_634_, v_mem_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object* v_motive_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_mem_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_638_, v_mem_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object* v_t_642_, lean_object* v_startsWith_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_642_, v_startsWith_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object* v_motive_645_, lean_object* v_t_646_, lean_object* v_h_647_, lean_object* v_startsWith_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_646_, v_startsWith_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object* v_t_650_, lean_object* v_endsWith_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_650_, v_endsWith_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object* v_motive_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_endsWith_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_654_, v_endsWith_656_);
return v___x_657_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object* v_a_664_, lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
v___x_670_ = lean_string_dec_eq(v_a_664_, v___x_669_);
if (v___x_670_ == 0)
{
size_t v___x_671_; size_t v___x_672_; 
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_add(v_i_666_, v___x_671_);
v_i_666_ = v___x_672_;
goto _start;
}
else
{
return v___x_670_;
}
}
else
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_664_ = stack[0].m_obj;
lean_object* v_as_665_ = stack[1].m_obj;
size_t v_i_666_ = stack[2].m_num;
size_t v_stop_667_ = stack[3].m_num;
uint8_t v_res_675_;
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_664_, v_as_665_, v_i_666_, v_stop_667_);
stack->m_num = v_res_675_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object* v_a_676_, lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_){
_start:
{
size_t v_i_boxed_680_; size_t v_stop_boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v_i_boxed_680_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_681_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_676_, v_as_677_, v_i_boxed_680_, v_stop_boxed_681_);
lean_dec_ref(v_as_677_);
lean_dec_ref(v_a_676_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object* v_as_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_as_684_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
return v___x_688_;
}
else
{
if (v___x_688_ == 0)
{
return v___x_688_;
}
else
{
size_t v___x_689_; size_t v___x_690_; uint8_t v___x_691_; 
v___x_689_ = ((size_t)0ULL);
v___x_690_ = lean_usize_of_nat(v___x_687_);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_685_, v_as_684_, v___x_689_, v___x_690_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_684_ = stack[0].m_obj;
lean_object* v_a_685_ = stack[1].m_obj;
uint8_t v_res_692_;
v_res_692_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_684_, v_a_685_);
stack->m_num = v_res_692_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object* v_as_693_, lean_object* v_a_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_693_, v_a_694_);
lean_dec_ref(v_a_694_);
lean_dec_ref(v_as_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
uint8_t l_Lake_StrPatDescr_matches(lean_object* v_s_697_, lean_object* v_self_698_){
_start:
{
switch(lean_obj_tag(v_self_698_))
{
case 0:
{
lean_object* v_xs_699_; uint8_t v___x_700_; 
v_xs_699_ = lean_ctor_get(v_self_698_, 0);
v___x_700_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_699_, v_s_697_);
return v___x_700_;
}
case 1:
{
lean_object* v_affix_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_affix_701_ = lean_ctor_get(v_self_698_, 0);
v___x_702_ = lean_string_utf8_byte_size(v_s_697_);
v___x_703_ = lean_string_utf8_byte_size(v_affix_701_);
v___x_704_ = lean_nat_dec_le(v___x_703_, v___x_702_);
if (v___x_704_ == 0)
{
return v___x_704_;
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_string_memcmp(v_s_697_, v_affix_701_, v___x_705_, v___x_705_, v___x_703_);
return v___x_706_;
}
}
default: 
{
lean_object* v_affix_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_affix_707_ = lean_ctor_get(v_self_698_, 0);
v___x_708_ = lean_string_utf8_byte_size(v_s_697_);
v___x_709_ = lean_string_utf8_byte_size(v_affix_707_);
v___x_710_ = lean_nat_dec_le(v___x_709_, v___x_708_);
if (v___x_710_ == 0)
{
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_sub(v___x_708_, v___x_709_);
v___x_713_ = lean_string_memcmp(v_s_697_, v_affix_707_, v___x_712_, v___x_711_, v___x_709_);
lean_dec(v___x_712_);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_StrPatDescr_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_697_ = stack[0].m_obj;
lean_object* v_self_698_ = stack[1].m_obj;
uint8_t v_res_714_;
v_res_714_ = l_Lake_StrPatDescr_matches(v_s_697_, v_self_698_);
stack->m_num = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object* v_s_715_, lean_object* v_self_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lake_StrPatDescr_matches(v_s_715_, v_self_716_);
lean_dec_ref(v_self_716_);
lean_dec_ref(v_s_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
uint8_t l_Lake_StrPat_mem___lam__0(lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v_x_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = l_Lake_PatternDescr_matches___redArg(v___x_723_, v_x_725_, v___x_724_);
return v___x_726_;
}
}
LEAN_EXPORT void l_Lake_StrPat_mem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_723_ = stack[0].m_obj;
lean_object* v___x_724_ = stack[1].m_obj;
lean_object* v_x_725_ = stack[2].m_obj;
uint8_t v_res_727_;
v_res_727_ = l_Lake_StrPat_mem___lam__0(v___x_723_, v___x_724_, v_x_725_);
stack->m_num = v_res_727_;
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Lake_StrPat_mem___lam__0(v___x_728_, v___x_729_, v_x_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object* v_xs_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_734_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_xs_733_);
v___x_736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_inc_ref(v___x_736_);
v___f_737_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_737_, 0, v___x_734_);
lean_closure_set(v___f_737_, 1, v___x_736_);
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
v___x_740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_740_, 0, v___f_737_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object* v_xs_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_xs_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object* v_affix_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_748_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_affix_747_);
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_inc_ref(v___x_750_);
v___f_751_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_751_, 0, v___x_748_);
lean_closure_set(v___f_751_, 1, v___x_750_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
v___x_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_754_, 0, v___f_751_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object* v_affix_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_756_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_757_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_757_, 0, v_affix_755_);
v___x_758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_inc_ref(v___x_758_);
v___f_759_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_759_, 0, v___x_756_);
lean_closure_set(v___f_759_, 1, v___x_758_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v___f_759_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object* v_s_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_mk_empty_array_with_capacity(v___x_764_);
v___x_766_ = lean_array_push(v___x_765_, v_s_763_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
uint8_t l_Lake_StrPat_beq___lam__0(lean_object* v_s_768_, lean_object* v_x_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_string_dec_eq(v_x_769_, v_s_768_);
return v___x_770_;
}
}
LEAN_EXPORT void l_Lake_StrPat_beq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_768_ = stack[0].m_obj;
lean_object* v_x_769_ = stack[1].m_obj;
uint8_t v_res_771_;
v_res_771_ = l_Lake_StrPat_beq___lam__0(v_s_768_, v_x_769_);
stack->m_num = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object* v_s_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Lake_StrPat_beq___lam__0(v_s_772_, v_x_773_);
lean_dec_ref(v_x_773_);
lean_dec_ref(v_s_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object* v_s_779_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v_s_779_);
v___f_780_ = lean_alloc_closure((void*)(l_Lake_StrPat_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_780_, 0, v_s_779_);
v___x_781_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_782_ = l_Lake_StrPatDescr_beq(v_s_779_);
v___x_783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___f_780_);
lean_ctor_set(v___x_785_, 1, v___x_781_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl(lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_tag_nat(v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl___boxed(lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lake_PathPatDescr_ctorIdx___impl(v_x_792_);
lean_dec_ref(v_x_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object* v_t_794_, lean_object* v_k_795_){
_start:
{
lean_object* v_p_796_; lean_object* v___x_797_; 
v_p_796_ = lean_ctor_get(v_t_794_, 0);
lean_inc_ref(v_p_796_);
lean_dec_ref(v_t_794_);
v___x_797_ = lean_apply_1(v_k_795_, v_p_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object* v_motive_798_, lean_object* v_ctorIdx_799_, lean_object* v_t_800_, lean_object* v_h_801_, lean_object* v_k_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_800_, v_k_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object* v_motive_804_, lean_object* v_ctorIdx_805_, lean_object* v_t_806_, lean_object* v_h_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lake_PathPatDescr_ctorElim(v_motive_804_, v_ctorIdx_805_, v_t_806_, v_h_807_, v_k_808_);
lean_dec(v_ctorIdx_805_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object* v_t_810_, lean_object* v_path_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_810_, v_path_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object* v_motive_813_, lean_object* v_t_814_, lean_object* v_h_815_, lean_object* v_path_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_814_, v_path_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object* v_t_818_, lean_object* v_extension_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_818_, v_extension_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object* v_motive_821_, lean_object* v_t_822_, lean_object* v_h_823_, lean_object* v_extension_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_822_, v_extension_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object* v_t_826_, lean_object* v_fileName_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_826_, v_fileName_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object* v_motive_829_, lean_object* v_t_830_, lean_object* v_h_831_, lean_object* v_fileName_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_830_, v_fileName_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__0(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__0, &l_Lake_instInhabitedPathPatDescr_default___closed__0_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__0);
return v___x_836_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr(void){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lake_instInhabitedPathPatDescr_default;
return v___x_837_;
}
}
uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object* v_p_838_, lean_object* v_x_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_string_dec_eq(v_x_839_, v_p_838_);
return v___x_840_;
}
}
LEAN_EXPORT void l_Lake_PathPatDescr_eq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_838_ = stack[0].m_obj;
lean_object* v_x_839_ = stack[1].m_obj;
uint8_t v_res_841_;
v_res_841_ = l_Lake_PathPatDescr_eq___lam__0(v_p_838_, v_x_839_);
stack->m_num = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object* v_p_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Lake_PathPatDescr_eq___lam__0(v_p_842_, v_x_843_);
lean_dec_ref(v_x_843_);
lean_dec_ref(v_p_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object* v_p_846_){
_start:
{
lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_inc_ref(v_p_846_);
v___f_847_ = lean_alloc_closure((void*)(l_Lake_PathPatDescr_eq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_847_, 0, v_p_846_);
v___x_848_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_849_ = l_Lake_StrPatDescr_beq(v_p_846_);
v___x_850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_852_, 0, v___f_847_);
lean_ctor_set(v___x_852_, 1, v___x_848_);
lean_ctor_set(v___x_852_, 2, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
uint8_t l_Lake_PathPatDescr_matches(lean_object* v_path_854_, lean_object* v_self_855_){
_start:
{
switch(lean_obj_tag(v_self_855_))
{
case 0:
{
lean_object* v_p_856_; lean_object* v_filter_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_p_856_ = lean_ctor_get(v_self_855_, 0);
lean_inc_ref(v_p_856_);
lean_dec_ref_known(v_self_855_, 1);
v_filter_857_ = lean_ctor_get(v_p_856_, 0);
lean_inc_ref(v_filter_857_);
lean_dec_ref(v_p_856_);
v___x_858_ = l_System_FilePath_normalize(v_path_854_);
v___x_859_ = lean_apply_1(v_filter_857_, v___x_858_);
v___x_860_ = lean_unbox(v___x_859_);
return v___x_860_;
}
case 1:
{
lean_object* v_p_861_; lean_object* v___x_862_; 
v_p_861_ = lean_ctor_get(v_self_855_, 0);
lean_inc_ref(v_p_861_);
lean_dec_ref_known(v_self_855_, 1);
v___x_862_ = l_System_FilePath_extension(v_path_854_);
if (lean_obj_tag(v___x_862_) == 0)
{
uint8_t v___x_863_; 
lean_dec_ref(v_p_861_);
v___x_863_ = 0;
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v_filter_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_val_864_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_862_, 1);
v_filter_865_ = lean_ctor_get(v_p_861_, 0);
lean_inc_ref(v_filter_865_);
lean_dec_ref(v_p_861_);
v___x_866_ = lean_apply_1(v_filter_865_, v_val_864_);
v___x_867_ = lean_unbox(v___x_866_);
return v___x_867_;
}
}
default: 
{
lean_object* v_p_868_; lean_object* v___x_869_; 
v_p_868_ = lean_ctor_get(v_self_855_, 0);
lean_inc_ref(v_p_868_);
lean_dec_ref_known(v_self_855_, 1);
v___x_869_ = l_System_FilePath_fileName(v_path_854_);
if (lean_obj_tag(v___x_869_) == 0)
{
uint8_t v___x_870_; 
lean_dec_ref(v_p_868_);
v___x_870_ = 0;
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v_filter_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_val_871_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_869_, 1);
v_filter_872_ = lean_ctor_get(v_p_868_, 0);
lean_inc_ref(v_filter_872_);
lean_dec_ref(v_p_868_);
v___x_873_ = lean_apply_1(v_filter_872_, v_val_871_);
v___x_874_ = lean_unbox(v___x_873_);
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_PathPatDescr_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_854_ = stack[0].m_obj;
lean_object* v_self_855_ = stack[1].m_obj;
uint8_t v_res_875_;
v_res_875_ = l_Lake_PathPatDescr_matches(v_path_854_, v_self_855_);
stack->m_num = v_res_875_;
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object* v_path_876_, lean_object* v_self_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lake_PathPatDescr_matches(v_path_876_, v_self_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
uint8_t l_Lake_PathPat_path___lam__0(lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_x_886_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = l_Lake_PatternDescr_matches___redArg(v___x_884_, v_x_886_, v___x_885_);
return v___x_887_;
}
}
LEAN_EXPORT void l_Lake_PathPat_path___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_884_ = stack[0].m_obj;
lean_object* v___x_885_ = stack[1].m_obj;
lean_object* v_x_886_ = stack[2].m_obj;
uint8_t v_res_888_;
v_res_888_ = l_Lake_PathPat_path___lam__0(v___x_884_, v___x_885_, v_x_886_);
stack->m_num = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_Lake_PathPat_path___lam__0(v___x_889_, v___x_890_, v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object* v_p_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_895_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_p_894_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_inc_ref(v___x_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v___x_895_);
lean_closure_set(v___f_898_, 1, v___x_897_);
v___x_899_ = lean_box(0);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
v___x_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_901_, 0, v___f_898_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object* v_p_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_903_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_p_902_);
v___x_905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_inc_ref(v___x_905_);
v___f_906_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_906_, 0, v___x_903_);
lean_closure_set(v___f_906_, 1, v___x_905_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
v___x_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_909_, 0, v___f_906_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object* v_p_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_911_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_912_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_912_, 0, v_p_910_);
v___x_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_inc_ref(v___x_913_);
v___f_914_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_914_, 0, v___x_911_);
lean_closure_set(v___f_914_, 1, v___x_913_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_913_);
v___x_917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_917_, 0, v___f_914_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
return v___x_917_;
}
}
uint8_t l_Lake_isVerLike(lean_object* v_s_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(2u);
v___x_920_ = lean_string_utf8_byte_size(v_s_918_);
v___x_921_ = lean_nat_dec_le(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
return v___x_921_;
}
else
{
lean_object* v___x_922_; uint32_t v___x_923_; uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_string_utf8_get_fast(v_s_918_, v___x_922_);
v___x_924_ = 118;
v___x_925_ = lean_uint32_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
return v___x_925_;
}
else
{
lean_object* v___x_926_; uint32_t v___x_927_; uint32_t v___x_928_; uint8_t v___x_929_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_string_utf8_get_fast(v_s_918_, v___x_926_);
v___x_928_ = 48;
v___x_929_ = lean_uint32_dec_le(v___x_928_, v___x_927_);
if (v___x_929_ == 0)
{
return v___x_929_;
}
else
{
uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_930_ = 57;
v___x_931_ = lean_uint32_dec_le(v___x_927_, v___x_930_);
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_isVerLike_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_918_ = stack[0].m_obj;
uint8_t v_res_932_;
v_res_932_ = l_Lake_isVerLike(v_s_918_);
stack->m_num = v_res_932_;
}
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object* v_s_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Lake_isVerLike(v_s_933_);
lean_dec_ref(v_s_933_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object* v_k_953_, lean_object* v_v_954_, lean_object* v_t_955_){
_start:
{
if (lean_obj_tag(v_t_955_) == 0)
{
lean_object* v_size_956_; lean_object* v_k_957_; lean_object* v_v_958_; lean_object* v_l_959_; lean_object* v_r_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1240_; 
v_size_956_ = lean_ctor_get(v_t_955_, 0);
v_k_957_ = lean_ctor_get(v_t_955_, 1);
v_v_958_ = lean_ctor_get(v_t_955_, 2);
v_l_959_ = lean_ctor_get(v_t_955_, 3);
v_r_960_ = lean_ctor_get(v_t_955_, 4);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_t_955_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_962_ = v_t_955_;
v_isShared_963_ = v_isSharedCheck_1240_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_r_960_);
lean_inc(v_l_959_);
lean_inc(v_v_958_);
lean_inc(v_k_957_);
lean_inc(v_size_956_);
lean_dec(v_t_955_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1240_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
v___x_964_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_953_, v_k_957_);
switch(v___x_964_)
{
case 0:
{
lean_object* v_impl_965_; lean_object* v___x_966_; 
lean_dec(v_size_956_);
v_impl_965_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_953_, v_v_954_, v_l_959_);
v___x_966_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_960_) == 0)
{
lean_object* v_size_967_; lean_object* v_size_968_; lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v_l_971_; lean_object* v_r_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_size_967_ = lean_ctor_get(v_r_960_, 0);
v_size_968_ = lean_ctor_get(v_impl_965_, 0);
v_k_969_ = lean_ctor_get(v_impl_965_, 1);
v_v_970_ = lean_ctor_get(v_impl_965_, 2);
v_l_971_ = lean_ctor_get(v_impl_965_, 3);
v_r_972_ = lean_ctor_get(v_impl_965_, 4);
lean_inc(v_r_972_);
v___x_973_ = lean_unsigned_to_nat(3u);
v___x_974_ = lean_nat_mul(v___x_973_, v_size_967_);
v___x_975_ = lean_nat_dec_lt(v___x_974_, v_size_968_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
lean_dec(v_r_972_);
v___x_976_ = lean_nat_add(v___x_966_, v_size_968_);
v___x_977_ = lean_nat_add(v___x_976_, v_size_967_);
lean_dec(v___x_976_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 3, v_impl_965_);
lean_ctor_set(v___x_962_, 0, v___x_977_);
v___x_979_ = v___x_962_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_impl_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_r_960_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1046_; 
lean_inc(v_l_971_);
lean_inc(v_v_970_);
lean_inc(v_k_969_);
lean_inc(v_size_968_);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_impl_965_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; 
v_unused_1047_ = lean_ctor_get(v_impl_965_, 4);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_impl_965_, 3);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_impl_965_, 2);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_impl_965_, 1);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_impl_965_, 0);
lean_dec(v_unused_1051_);
v___x_982_ = v_impl_965_;
v_isShared_983_ = v_isSharedCheck_1046_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_impl_965_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1046_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_size_984_; lean_object* v_size_985_; lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v_l_988_; lean_object* v_r_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_size_984_ = lean_ctor_get(v_l_971_, 0);
v_size_985_ = lean_ctor_get(v_r_972_, 0);
v_k_986_ = lean_ctor_get(v_r_972_, 1);
v_v_987_ = lean_ctor_get(v_r_972_, 2);
v_l_988_ = lean_ctor_get(v_r_972_, 3);
v_r_989_ = lean_ctor_get(v_r_972_, 4);
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = lean_nat_mul(v___x_990_, v_size_984_);
v___x_992_ = lean_nat_dec_lt(v_size_985_, v___x_991_);
lean_dec(v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1021_; 
lean_inc(v_r_989_);
lean_inc(v_l_988_);
lean_inc(v_v_987_);
lean_inc(v_k_986_);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_r_972_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1022_ = lean_ctor_get(v_r_972_, 4);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_972_, 3);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_r_972_, 2);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_r_972_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_r_972_, 0);
lean_dec(v_unused_1026_);
v___x_994_ = v_r_972_;
v_isShared_995_ = v_isSharedCheck_1021_;
goto v_resetjp_993_;
}
else
{
lean_dec(v_r_972_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1021_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___x_1009_; lean_object* v___y_1011_; 
v___x_996_ = lean_nat_add(v___x_966_, v_size_968_);
lean_dec(v_size_968_);
v___x_997_ = lean_nat_add(v___x_996_, v_size_967_);
lean_dec(v___x_996_);
v___x_1009_ = lean_nat_add(v___x_966_, v_size_984_);
if (lean_obj_tag(v_l_988_) == 0)
{
lean_object* v_size_1019_; 
v_size_1019_ = lean_ctor_get(v_l_988_, 0);
lean_inc(v_size_1019_);
v___y_1011_ = v_size_1019_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___y_1011_ = v___x_1020_;
goto v___jp_1010_;
}
v___jp_998_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_nat_add(v___y_999_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec(v___y_999_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 4, v_r_960_);
lean_ctor_set(v___x_994_, 3, v_r_989_);
lean_ctor_set(v___x_994_, 2, v_v_958_);
lean_ctor_set(v___x_994_, 1, v_k_957_);
lean_ctor_set(v___x_994_, 0, v___x_1002_);
v___x_1004_ = v___x_994_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_r_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_r_960_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v___x_1004_);
lean_ctor_set(v___x_982_, 3, v___y_1000_);
lean_ctor_set(v___x_982_, 2, v_v_987_);
lean_ctor_set(v___x_982_, 1, v_k_986_);
lean_ctor_set(v___x_982_, 0, v___x_997_);
v___x_1006_ = v___x_982_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_986_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___y_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
v___jp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_nat_add(v___x_1009_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec(v___x_1009_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_l_988_);
lean_ctor_set(v___x_962_, 3, v_l_971_);
lean_ctor_set(v___x_962_, 2, v_v_970_);
lean_ctor_set(v___x_962_, 1, v_k_969_);
lean_ctor_set(v___x_962_, 0, v___x_1012_);
v___x_1014_ = v___x_962_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_l_971_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_l_988_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_nat_add(v___x_966_, v_size_967_);
if (lean_obj_tag(v_r_989_) == 0)
{
lean_object* v_size_1016_; 
v_size_1016_ = lean_ctor_get(v_r_989_, 0);
lean_inc(v_size_1016_);
v___y_999_ = v___x_1015_;
v___y_1000_ = v___x_1014_;
v___y_1001_ = v_size_1016_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___y_999_ = v___x_1015_;
v___y_1000_ = v___x_1014_;
v___y_1001_ = v___x_1017_;
goto v___jp_998_;
}
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_del_object(v___x_962_);
v___x_1027_ = lean_nat_add(v___x_966_, v_size_968_);
lean_dec(v_size_968_);
v___x_1028_ = lean_nat_add(v___x_1027_, v_size_967_);
lean_dec(v___x_1027_);
v___x_1029_ = lean_nat_add(v___x_966_, v_size_967_);
v___x_1030_ = lean_nat_add(v___x_1029_, v_size_985_);
lean_dec(v___x_1029_);
lean_inc_ref(v_r_960_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v_r_960_);
lean_ctor_set(v___x_982_, 3, v_r_972_);
lean_ctor_set(v___x_982_, 2, v_v_958_);
lean_ctor_set(v___x_982_, 1, v_k_957_);
lean_ctor_set(v___x_982_, 0, v___x_1030_);
v___x_1032_ = v___x_982_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_r_972_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_r_960_);
v___x_1032_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v_r_960_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; lean_object* v_unused_1044_; 
v_unused_1040_ = lean_ctor_get(v_r_960_, 4);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_r_960_, 3);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_r_960_, 2);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_r_960_, 1);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_r_960_, 0);
lean_dec(v_unused_1044_);
v___x_1034_ = v_r_960_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_r_960_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v_l_971_);
lean_ctor_set(v___x_1034_, 2, v_v_970_);
lean_ctor_set(v___x_1034_, 1, v_k_969_);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_l_971_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1052_; 
v_l_1052_ = lean_ctor_get(v_impl_965_, 3);
if (lean_obj_tag(v_l_1052_) == 0)
{
lean_object* v_r_1053_; lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1066_; 
lean_inc_ref(v_l_1052_);
v_r_1053_ = lean_ctor_get(v_impl_965_, 4);
v_k_1054_ = lean_ctor_get(v_impl_965_, 1);
v_v_1055_ = lean_ctor_get(v_impl_965_, 2);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_impl_965_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; 
v_unused_1067_ = lean_ctor_get(v_impl_965_, 3);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_impl_965_, 0);
lean_dec(v_unused_1068_);
v___x_1057_ = v_impl_965_;
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_r_1053_);
lean_inc(v_v_1055_);
lean_inc(v_k_1054_);
lean_dec(v_impl_965_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1053_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 3, v_r_1053_);
lean_ctor_set(v___x_1057_, 2, v_v_958_);
lean_ctor_set(v___x_1057_, 1, v_k_957_);
lean_ctor_set(v___x_1057_, 0, v___x_966_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_r_1053_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_r_1053_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v___x_1061_);
lean_ctor_set(v___x_962_, 3, v_l_1052_);
lean_ctor_set(v___x_962_, 2, v_v_1055_);
lean_ctor_set(v___x_962_, 1, v_k_1054_);
lean_ctor_set(v___x_962_, 0, v___x_1059_);
v___x_1063_ = v___x_962_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_l_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_r_1069_; 
v_r_1069_ = lean_ctor_get(v_impl_965_, 4);
lean_inc(v_r_1069_);
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_k_1070_; lean_object* v_v_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_l_1052_);
v_k_1070_ = lean_ctor_get(v_impl_965_, 1);
v_v_1071_ = lean_ctor_get(v_impl_965_, 2);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_impl_965_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1095_ = lean_ctor_get(v_impl_965_, 4);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_impl_965_, 3);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_impl_965_, 0);
lean_dec(v_unused_1097_);
v___x_1073_ = v_impl_965_;
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_v_1071_);
lean_inc(v_k_1070_);
lean_dec(v_impl_965_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_k_1075_; lean_object* v_v_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1090_; 
v_k_1075_ = lean_ctor_get(v_r_1069_, 1);
v_v_1076_ = lean_ctor_get(v_r_1069_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1091_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1093_);
v___x_1078_ = v_r_1069_;
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_v_1076_);
lean_inc(v_k_1075_);
lean_dec(v_r_1069_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_unsigned_to_nat(3u);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_1052_);
lean_ctor_set(v___x_1078_, 3, v_l_1052_);
lean_ctor_set(v___x_1078_, 2, v_v_1071_);
lean_ctor_set(v___x_1078_, 1, v_k_1070_);
lean_ctor_set(v___x_1078_, 0, v___x_966_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1070_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1071_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_1052_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_l_1052_);
v___x_1082_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v_l_1052_);
lean_ctor_set(v___x_1073_, 2, v_v_958_);
lean_ctor_set(v___x_1073_, 1, v_k_957_);
lean_ctor_set(v___x_1073_, 0, v___x_966_);
v___x_1084_ = v___x_1073_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_l_1052_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_l_1052_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v___x_1084_);
lean_ctor_set(v___x_962_, 3, v___x_1082_);
lean_ctor_set(v___x_962_, 2, v_v_1076_);
lean_ctor_set(v___x_962_, 1, v_k_1075_);
lean_ctor_set(v___x_962_, 0, v___x_1080_);
v___x_1086_ = v___x_962_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_1076_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_unsigned_to_nat(2u);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_r_1069_);
lean_ctor_set(v___x_962_, 3, v_impl_965_);
lean_ctor_set(v___x_962_, 0, v___x_1098_);
v___x_1100_ = v___x_962_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_impl_965_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_r_1069_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1103_; 
lean_dec(v_v_958_);
lean_dec(v_k_957_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v_v_954_);
lean_ctor_set(v___x_962_, 1, v_k_953_);
v___x_1103_ = v___x_962_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_size_956_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_k_953_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_v_954_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_l_959_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_r_960_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
default: 
{
lean_object* v_impl_1105_; lean_object* v___x_1106_; 
lean_dec(v_size_956_);
v_impl_1105_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_953_, v_v_954_, v_r_960_);
v___x_1106_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_959_) == 0)
{
lean_object* v_size_1107_; lean_object* v_size_1108_; lean_object* v_k_1109_; lean_object* v_v_1110_; lean_object* v_l_1111_; lean_object* v_r_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_size_1107_ = lean_ctor_get(v_l_959_, 0);
v_size_1108_ = lean_ctor_get(v_impl_1105_, 0);
v_k_1109_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1110_ = lean_ctor_get(v_impl_1105_, 2);
v_l_1111_ = lean_ctor_get(v_impl_1105_, 3);
lean_inc(v_l_1111_);
v_r_1112_ = lean_ctor_get(v_impl_1105_, 4);
v___x_1113_ = lean_unsigned_to_nat(3u);
v___x_1114_ = lean_nat_mul(v___x_1113_, v_size_1107_);
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v_size_1108_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_dec(v_l_1111_);
v___x_1116_ = lean_nat_add(v___x_1106_, v_size_1107_);
v___x_1117_ = lean_nat_add(v___x_1116_, v_size_1108_);
lean_dec(v___x_1116_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_impl_1105_);
lean_ctor_set(v___x_962_, 0, v___x_1117_);
v___x_1119_ = v___x_962_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_l_959_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_impl_1105_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1184_; 
lean_inc(v_r_1112_);
lean_inc(v_v_1110_);
lean_inc(v_k_1109_);
lean_inc(v_size_1108_);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; 
v_unused_1185_ = lean_ctor_get(v_impl_1105_, 4);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_impl_1105_, 2);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_impl_1105_, 1);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1189_);
v___x_1122_ = v_impl_1105_;
v_isShared_1123_ = v_isSharedCheck_1184_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_impl_1105_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1184_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_size_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v_l_1127_; lean_object* v_r_1128_; lean_object* v_size_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_size_1124_ = lean_ctor_get(v_l_1111_, 0);
v_k_1125_ = lean_ctor_get(v_l_1111_, 1);
v_v_1126_ = lean_ctor_get(v_l_1111_, 2);
v_l_1127_ = lean_ctor_get(v_l_1111_, 3);
v_r_1128_ = lean_ctor_get(v_l_1111_, 4);
v_size_1129_ = lean_ctor_get(v_r_1112_, 0);
v___x_1130_ = lean_unsigned_to_nat(2u);
v___x_1131_ = lean_nat_mul(v___x_1130_, v_size_1129_);
v___x_1132_ = lean_nat_dec_lt(v_size_1124_, v___x_1131_);
lean_dec(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1160_; 
lean_inc(v_r_1128_);
lean_inc(v_l_1127_);
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1161_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1165_);
v___x_1134_ = v_l_1111_;
v_isShared_1135_ = v_isSharedCheck_1160_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v_l_1111_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1160_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1150_; 
v___x_1136_ = lean_nat_add(v___x_1106_, v_size_1107_);
v___x_1137_ = lean_nat_add(v___x_1136_, v_size_1108_);
lean_dec(v_size_1108_);
if (lean_obj_tag(v_l_1127_) == 0)
{
lean_object* v_size_1158_; 
v_size_1158_ = lean_ctor_get(v_l_1127_, 0);
lean_inc(v_size_1158_);
v___y_1150_ = v_size_1158_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___y_1150_ = v___x_1159_;
goto v___jp_1149_;
}
v___jp_1138_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_nat_add(v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec(v___y_1140_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v_r_1112_);
lean_ctor_set(v___x_1134_, 3, v_r_1128_);
lean_ctor_set(v___x_1134_, 2, v_v_1110_);
lean_ctor_set(v___x_1134_, 1, v_k_1109_);
lean_ctor_set(v___x_1134_, 0, v___x_1142_);
v___x_1144_ = v___x_1134_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_r_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_r_1112_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v___x_1144_);
lean_ctor_set(v___x_1122_, 3, v___y_1139_);
lean_ctor_set(v___x_1122_, 2, v_v_1126_);
lean_ctor_set(v___x_1122_, 1, v_k_1125_);
lean_ctor_set(v___x_1122_, 0, v___x_1137_);
v___x_1146_ = v___x_1122_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v___y_1139_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_nat_add(v___x_1136_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec(v___x_1136_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_l_1127_);
lean_ctor_set(v___x_962_, 0, v___x_1151_);
v___x_1153_ = v___x_962_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_l_959_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_l_1127_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_nat_add(v___x_1106_, v_size_1129_);
if (lean_obj_tag(v_r_1128_) == 0)
{
lean_object* v_size_1155_; 
v_size_1155_ = lean_ctor_get(v_r_1128_, 0);
lean_inc(v_size_1155_);
v___y_1139_ = v___x_1153_;
v___y_1140_ = v___x_1154_;
v___y_1141_ = v_size_1155_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___y_1139_ = v___x_1153_;
v___y_1140_ = v___x_1154_;
v___y_1141_ = v___x_1156_;
goto v___jp_1138_;
}
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_del_object(v___x_962_);
v___x_1166_ = lean_nat_add(v___x_1106_, v_size_1107_);
v___x_1167_ = lean_nat_add(v___x_1166_, v_size_1108_);
lean_dec(v_size_1108_);
v___x_1168_ = lean_nat_add(v___x_1166_, v_size_1124_);
lean_dec(v___x_1166_);
lean_inc_ref(v_l_959_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v_l_1111_);
lean_ctor_set(v___x_1122_, 3, v_l_959_);
lean_ctor_set(v___x_1122_, 2, v_v_958_);
lean_ctor_set(v___x_1122_, 1, v_k_957_);
lean_ctor_set(v___x_1122_, 0, v___x_1168_);
v___x_1170_ = v___x_1122_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_l_959_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_l_1111_);
v___x_1170_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_isSharedCheck_1177_ = !lean_is_exclusive(v_l_959_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; 
v_unused_1178_ = lean_ctor_get(v_l_959_, 4);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_l_959_, 3);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_l_959_, 2);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_l_959_, 1);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_l_959_, 0);
lean_dec(v_unused_1182_);
v___x_1172_ = v_l_959_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_dec(v_l_959_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 4, v_r_1112_);
lean_ctor_set(v___x_1172_, 3, v___x_1170_);
lean_ctor_set(v___x_1172_, 2, v_v_1110_);
lean_ctor_set(v___x_1172_, 1, v_k_1109_);
lean_ctor_set(v___x_1172_, 0, v___x_1167_);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_r_1112_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1190_; 
v_l_1190_ = lean_ctor_get(v_impl_1105_, 3);
lean_inc(v_l_1190_);
if (lean_obj_tag(v_l_1190_) == 0)
{
lean_object* v_r_1191_; lean_object* v_k_1192_; lean_object* v_v_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1216_; 
v_r_1191_ = lean_ctor_get(v_impl_1105_, 4);
v_k_1192_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1193_ = lean_ctor_get(v_impl_1105_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1217_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1218_);
v___x_1195_ = v_impl_1105_;
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_r_1191_);
lean_inc(v_v_1193_);
lean_inc(v_k_1192_);
lean_dec(v_impl_1105_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1212_; 
v_k_1197_ = lean_ctor_get(v_l_1190_, 1);
v_v_1198_ = lean_ctor_get(v_l_1190_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_l_1190_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; lean_object* v_unused_1214_; lean_object* v_unused_1215_; 
v_unused_1213_ = lean_ctor_get(v_l_1190_, 4);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_l_1190_, 3);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_l_1190_, 0);
lean_dec(v_unused_1215_);
v___x_1200_ = v_l_1190_;
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_v_1198_);
lean_inc(v_k_1197_);
lean_dec(v_l_1190_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1191_, 2);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_r_1191_);
lean_ctor_set(v___x_1200_, 3, v_r_1191_);
lean_ctor_set(v___x_1200_, 2, v_v_958_);
lean_ctor_set(v___x_1200_, 1, v_k_957_);
lean_ctor_set(v___x_1200_, 0, v___x_1106_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_r_1191_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_r_1191_);
v___x_1204_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
lean_inc(v_r_1191_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 3, v_r_1191_);
lean_ctor_set(v___x_1195_, 0, v___x_1106_);
v___x_1206_ = v___x_1195_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_k_1192_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_v_1193_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_r_1191_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_r_1191_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v___x_1206_);
lean_ctor_set(v___x_962_, 3, v___x_1204_);
lean_ctor_set(v___x_962_, 2, v_v_1198_);
lean_ctor_set(v___x_962_, 1, v_k_1197_);
lean_ctor_set(v___x_962_, 0, v___x_1202_);
v___x_1208_ = v___x_962_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1197_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1198_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
else
{
lean_object* v_r_1219_; 
v_r_1219_ = lean_ctor_get(v_impl_1105_, 4);
lean_inc(v_r_1219_);
if (lean_obj_tag(v_r_1219_) == 0)
{
lean_object* v_k_1220_; lean_object* v_v_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1232_; 
v_k_1220_ = lean_ctor_get(v_impl_1105_, 1);
v_v_1221_ = lean_ctor_get(v_impl_1105_, 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_impl_1105_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1233_ = lean_ctor_get(v_impl_1105_, 4);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_impl_1105_, 3);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_impl_1105_, 0);
lean_dec(v_unused_1235_);
v___x_1223_ = v_impl_1105_;
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_v_1221_);
lean_inc(v_k_1220_);
lean_dec(v_impl_1105_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(3u);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_l_1190_);
lean_ctor_set(v___x_1223_, 2, v_v_958_);
lean_ctor_set(v___x_1223_, 1, v_k_957_);
lean_ctor_set(v___x_1223_, 0, v___x_1106_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_l_1190_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_l_1190_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_r_1219_);
lean_ctor_set(v___x_962_, 3, v___x_1227_);
lean_ctor_set(v___x_962_, 2, v_v_1221_);
lean_ctor_set(v___x_962_, 1, v_k_1220_);
lean_ctor_set(v___x_962_, 0, v___x_1225_);
v___x_1229_ = v___x_962_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_r_1219_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_unsigned_to_nat(2u);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v_impl_1105_);
lean_ctor_set(v___x_962_, 3, v_r_1219_);
lean_ctor_set(v___x_962_, 0, v___x_1236_);
v___x_1238_ = v___x_962_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_impl_1105_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
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
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_k_953_);
lean_ctor_set(v___x_1242_, 2, v_v_954_);
lean_ctor_set(v___x_1242_, 3, v_t_955_);
lean_ctor_set(v___x_1242_, 4, v_t_955_);
return v___x_1242_;
}
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__0(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_box(1);
v___x_1244_ = ((lean_object*)(l_Lake_StrPat_verLike));
v___x_1245_ = ((lean_object*)(l_Lake_StrPat_verLike___closed__2));
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1245_, v___x_1244_, v___x_1243_);
return v___x_1246_;
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__1(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1247_ = lean_obj_once(&l_Lake_versionTagPresets___closed__0, &l_Lake_versionTagPresets___closed__0_once, _init_l_Lake_versionTagPresets___closed__0);
v___x_1248_ = ((lean_object*)(l_Lake_defaultVersionTags));
v___x_1249_ = ((lean_object*)(l_Lake_defaultVersionTags___closed__1));
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v___x_1249_, v___x_1248_, v___x_1247_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lake_versionTagPresets(void){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_obj_once(&l_Lake_versionTagPresets___closed__1, &l_Lake_versionTagPresets___closed__1_once, _init_l_Lake_versionTagPresets___closed__1);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_k_1253_, lean_object* v_v_1254_, lean_object* v_t_1255_, lean_object* v_hl_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_1253_, v_v_1254_, v_t_1255_);
return v___x_1257_;
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
