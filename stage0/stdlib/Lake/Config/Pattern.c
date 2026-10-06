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
LEAN_EXPORT uint8_t l_Lake_instInhabitedPattern_default__1___redArg___lam__0(lean_object* v_x_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___lam__0___boxed(lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lake_instInhabitedPattern_default__1___redArg___lam__0(v_x_200_);
lean_dec(v_x_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__1));
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1___redArg___boxed(lean_object* v___dummy_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v_res_211_;
}
}
static lean_object* _init_l_Lake_instInhabitedPattern_default__1___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lake_instInhabitedPattern_default__1___redArg();
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern_default__1(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg(){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern___redArg___boxed(lean_object* v___dummy_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_instInhabitedPattern___redArg();
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPattern(lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
return v___x_222_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg(){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___redArg___closed__0);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1___redArg___boxed(lean_object* v___dummy_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v_res_228_;
}
}
static lean_object* _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lake_instInhabitedPatternDescr_default__1___redArg();
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr_default__1(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg(){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr___redArg___boxed(lean_object* v___dummy_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lake_instInhabitedPatternDescr___redArg();
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPatternDescr(lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lake_instInhabitedPatternDescr_default__1___closed__0, &l_Lake_instInhabitedPatternDescr_default__1___closed__0_once, _init_l_Lake_instInhabitedPatternDescr_default__1___closed__0);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___lam__0(lean_object* v_p_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_241_, 0, v_p_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg(){
_start:
{
lean_object* v___f_244_; 
v___f_244_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr___redArg___boxed(lean_object* v___dummy_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_instCoePatternDescr___redArg();
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescr(lean_object* v_00_u03b2_247_, lean_object* v_00_u03b1_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = ((lean_object*)(l_Lake_instCoePatternDescr___redArg___closed__0));
return v___f_249_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches___redArg(lean_object* v_a_250_, lean_object* v_self_251_){
_start:
{
lean_object* v_filter_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_filter_252_ = lean_ctor_get(v_self_251_, 0);
lean_inc_ref(v_filter_252_);
lean_dec_ref(v_self_251_);
v___x_253_ = lean_apply_1(v_filter_252_, v_a_250_);
v___x_254_ = lean_unbox(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___redArg___boxed(lean_object* v_a_255_, lean_object* v_self_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lake_Pattern_matches___redArg(v_a_255_, v_self_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_matches(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_a_261_, lean_object* v_self_262_){
_start:
{
lean_object* v_filter_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_filter_263_ = lean_ctor_get(v_self_262_, 0);
lean_inc_ref(v_filter_263_);
lean_dec_ref(v_self_262_);
v___x_264_ = lean_apply_1(v_filter_263_, v_a_261_);
v___x_265_ = lean_unbox(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_matches___boxed(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_a_268_, lean_object* v_self_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lake_Pattern_matches(v_00_u03b1_266_, v_00_u03b2_267_, v_a_268_, v_self_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Lake_instIsPatternPattern___redArg___lam__0(lean_object* v_self_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_filter_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_filter_274_ = lean_ctor_get(v_self_272_, 0);
lean_inc_ref(v_filter_274_);
lean_dec_ref(v_self_272_);
v___x_275_ = lean_apply_1(v_filter_274_, v___y_273_);
v___x_276_ = lean_unbox(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___lam__0___boxed(lean_object* v_self_277_, lean_object* v___y_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lake_instIsPatternPattern___redArg___lam__0(v_self_277_, v___y_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg(){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern___redArg___boxed(lean_object* v___dummy_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_instIsPatternPattern___redArg();
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPattern(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_){
_start:
{
lean_object* v___f_288_; 
v___f_288_ = ((lean_object*)(l_Lake_instIsPatternPattern___redArg___closed__0));
return v___f_288_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__0(lean_object* v_val_289_, uint8_t v___x_290_, lean_object* v_v_291_){
_start:
{
lean_object* v_filter_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_filter_292_ = lean_ctor_get(v_v_291_, 0);
lean_inc_ref(v_filter_292_);
lean_dec_ref(v_v_291_);
v___x_293_ = lean_apply_1(v_filter_292_, v_val_289_);
v___x_294_ = lean_unbox(v___x_293_);
if (v___x_294_ == 0)
{
return v___x_290_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__0___boxed(lean_object* v_val_296_, lean_object* v___x_297_, lean_object* v_v_298_){
_start:
{
uint8_t v___x_202__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v___x_202__boxed_299_ = lean_unbox(v___x_297_);
v_res_300_ = l_Lake_PatternDescr_matches___redArg___lam__0(v_val_296_, v___x_202__boxed_299_, v_v_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg___lam__1(lean_object* v_val_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_filter_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_filter_304_ = lean_ctor_get(v_x_303_, 0);
lean_inc_ref(v_filter_304_);
lean_dec_ref(v_x_303_);
v___x_305_ = lean_apply_1(v_filter_304_, v_val_302_);
v___x_306_ = lean_unbox(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___lam__1___boxed(lean_object* v_val_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Lake_PatternDescr_matches___redArg___lam__1(v_val_307_, v_x_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches___redArg(lean_object* v_inst_330_, lean_object* v_val_331_, lean_object* v_self_332_){
_start:
{
switch(lean_obj_tag(v_self_332_))
{
case 0:
{
lean_object* v_p_333_; lean_object* v_filter_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
lean_dec_ref(v_inst_330_);
v_p_333_ = lean_ctor_get(v_self_332_, 0);
lean_inc_ref(v_p_333_);
lean_dec_ref_known(v_self_332_, 1);
v_filter_334_ = lean_ctor_get(v_p_333_, 0);
lean_inc_ref(v_filter_334_);
lean_dec_ref(v_p_333_);
v___x_335_ = lean_apply_1(v_filter_334_, v_val_331_);
v___x_336_ = lean_unbox(v___x_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
v___x_337_ = 1;
return v___x_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
case 1:
{
lean_object* v_ps_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
lean_dec_ref(v_inst_330_);
v_ps_339_ = lean_ctor_get(v_self_332_, 0);
lean_inc_ref(v_ps_339_);
lean_dec_ref_known(v_self_332_, 1);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_array_get_size(v_ps_339_);
v___x_342_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_343_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
lean_dec_ref(v_ps_339_);
lean_dec(v_val_331_);
v___x_344_ = 1;
return v___x_344_;
}
else
{
if (v___x_343_ == 0)
{
lean_dec_ref(v_ps_339_);
lean_dec(v_val_331_);
return v___x_343_;
}
else
{
lean_object* v___x_345_; lean_object* v___f_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_345_ = lean_box(v___x_343_);
v___f_346_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_346_, 0, v_val_331_);
lean_closure_set(v___f_346_, 1, v___x_345_);
v___x_347_ = ((size_t)0ULL);
v___x_348_ = lean_usize_of_nat(v___x_341_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_342_, v___f_346_, v_ps_339_, v___x_347_, v___x_348_);
v___x_350_ = lean_unbox(v___x_349_);
lean_dec(v___x_349_);
if (v___x_350_ == 0)
{
return v___x_343_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
}
}
}
case 2:
{
lean_object* v_ps_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
lean_dec_ref(v_inst_330_);
v_ps_352_ = lean_ctor_get(v_self_332_, 0);
lean_inc_ref(v_ps_352_);
lean_dec_ref_known(v_self_332_, 1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get_size(v_ps_352_);
v___x_355_ = ((lean_object*)(l_Lake_PatternDescr_matches___redArg___closed__9));
v___x_356_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_356_ == 0)
{
lean_dec_ref(v_ps_352_);
lean_dec(v_val_331_);
return v___x_356_;
}
else
{
if (v___x_356_ == 0)
{
lean_dec_ref(v_ps_352_);
lean_dec(v_val_331_);
return v___x_356_;
}
else
{
lean_object* v___f_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___f_357_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_357_, 0, v_val_331_);
v___x_358_ = ((size_t)0ULL);
v___x_359_ = lean_usize_of_nat(v___x_354_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_355_, v___f_357_, v_ps_352_, v___x_358_, v___x_359_);
v___x_361_ = lean_unbox(v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
}
default: 
{
lean_object* v_p_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_p_362_ = lean_ctor_get(v_self_332_, 0);
lean_inc(v_p_362_);
lean_dec_ref_known(v_self_332_, 1);
v___x_363_ = lean_apply_2(v_inst_330_, v_p_362_, v_val_331_);
v___x_364_ = lean_unbox(v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___redArg___boxed(lean_object* v_inst_365_, lean_object* v_val_366_, lean_object* v_self_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lake_PatternDescr_matches___redArg(v_inst_365_, v_val_366_, v_self_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Lake_PatternDescr_matches(lean_object* v_00_u03b2_370_, lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_val_373_, lean_object* v_self_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Lake_PatternDescr_matches___redArg(v_inst_372_, v_val_373_, v_self_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_matches___boxed(lean_object* v_00_u03b2_376_, lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_val_379_, lean_object* v_self_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Lake_PatternDescr_matches(v_00_u03b2_376_, v_00_u03b1_377_, v_inst_378_, v_val_379_, v_self_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr___redArg(lean_object* v_inst_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_alloc_closure((void*)(l_Lake_PatternDescr_matches___boxed), 5, 3);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, lean_box(0));
lean_closure_set(v___x_384_, 2, v_inst_383_);
v___x_385_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_385_, 0, lean_box(0));
lean_closure_set(v___x_385_, 1, lean_box(0));
lean_closure_set(v___x_385_, 2, lean_box(0));
lean_closure_set(v___x_385_, 3, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_instIsPatternPatternDescr(lean_object* v_00_u03b2_386_, lean_object* v_00_u03b1_387_, lean_object* v_inst_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lake_instIsPatternPatternDescr___redArg(v_inst_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn___redArg(lean_object* v_f_390_, lean_object* v_name_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_f_390_);
lean_ctor_set(v___x_393_, 1, v_name_391_);
lean_ctor_set(v___x_393_, 2, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofFn(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_f_396_, lean_object* v_name_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_399_, 0, v_f_396_);
lean_ctor_set(v___x_399_, 1, v_name_397_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___lam__0(lean_object* v_f_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v_f_400_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg(){
_start:
{
lean_object* v___f_406_; 
v___f_406_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern___redArg___boxed(lean_object* v___dummy_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lake_instCoeForallBoolPattern___redArg();
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeForallBoolPattern(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_){
_start:
{
lean_object* v___f_411_; 
v___f_411_ = ((lean_object*)(l_Lake_instCoeForallBoolPattern___redArg___closed__0));
return v___f_411_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_ofDescr___redArg___lam__0(lean_object* v_inst_412_, lean_object* v_descr_413_, lean_object* v_x_414_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = l_Lake_PatternDescr_matches___redArg(v_inst_412_, v_x_414_, v_descr_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg___lam__0___boxed(lean_object* v_inst_416_, lean_object* v_descr_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lake_Pattern_ofDescr___redArg___lam__0(v_inst_416_, v_descr_417_, v_x_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr___redArg(lean_object* v_inst_421_, lean_object* v_descr_422_, lean_object* v_name_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc_ref(v_descr_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_424_, 0, v_inst_421_);
lean_closure_set(v___f_424_, 1, v_descr_422_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_descr_422_);
v___x_426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_426_, 0, v___f_424_);
lean_ctor_set(v___x_426_, 1, v_name_423_);
lean_ctor_set(v___x_426_, 2, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_ofDescr(lean_object* v_00_u03b2_427_, lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_descr_430_, lean_object* v_name_431_){
_start:
{
lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_inc_ref(v_descr_430_);
v___f_432_ = lean_alloc_closure((void*)(l_Lake_Pattern_ofDescr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_432_, 0, v_inst_429_);
lean_closure_set(v___f_432_, 1, v_descr_430_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v_descr_430_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v___f_432_);
lean_ctor_set(v___x_434_, 1, v_name_431_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT uint8_t l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(lean_object* v_inst_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_Lake_PatternDescr_matches___redArg(v_inst_435_, v_x_437_, v_x_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed(lean_object* v_inst_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0(v_inst_439_, v_x_440_, v_x_441_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1(lean_object* v_inst_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc_ref(v_x_445_);
v___f_446_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_446_, 0, v_inst_444_);
lean_closure_set(v___f_446_, 1, v_x_445_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_x_445_);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v___f_446_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern___redArg(lean_object* v_inst_450_){
_start:
{
lean_object* v___f_451_; 
v___f_451_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_451_, 0, v_inst_450_);
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePatternDescrPatternOfIsPattern(lean_object* v_00_u03b2_452_, lean_object* v_00_u03b1_453_, lean_object* v_inst_454_){
_start:
{
lean_object* v___f_455_; 
v___f_455_ = lean_alloc_closure((void*)(l_Lake_instCoePatternDescrPatternOfIsPattern___redArg___lam__1), 2, 1);
lean_closure_set(v___f_455_, 0, v_inst_454_);
return v___f_455_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_not___redArg___lam__0(lean_object* v_inst_456_, lean_object* v___x_457_, lean_object* v_x_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = l_Lake_PatternDescr_matches___redArg(v_inst_456_, v_x_458_, v___x_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg___lam__0___boxed(lean_object* v_inst_460_, lean_object* v___x_461_, lean_object* v_x_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lake_Pattern_not___redArg___lam__0(v_inst_460_, v___x_461_, v_x_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_not___redArg(lean_object* v_inst_465_, lean_object* v_p_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_p_466_);
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
LEAN_EXPORT lean_object* l_Lake_Pattern_not(lean_object* v_00_u03b2_472_, lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_p_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_p_475_);
lean_inc_ref(v___x_476_);
v___f_477_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_477_, 0, v_inst_474_);
lean_closure_set(v___f_477_, 1, v___x_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_476_);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v___f_477_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_all___redArg(lean_object* v_inst_481_, lean_object* v_ps_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lake_Pattern_all(lean_object* v_00_u03b2_488_, lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_ps_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_ps_491_);
lean_inc_ref(v___x_492_);
v___f_493_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_493_, 0, v_inst_490_);
lean_closure_set(v___f_493_, 1, v___x_492_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_492_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v___f_493_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any___redArg(lean_object* v_inst_497_, lean_object* v_ps_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_499_, 0, v_ps_498_);
lean_inc_ref(v___x_499_);
v___f_500_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_500_, 0, v_inst_497_);
lean_closure_set(v___f_500_, 1, v___x_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_499_);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v___f_500_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_any(lean_object* v_00_u03b2_504_, lean_object* v_00_u03b1_505_, lean_object* v_inst_506_, lean_object* v_ps_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_508_, 0, v_ps_507_);
lean_inc_ref(v___x_508_);
v___f_509_ = lean_alloc_closure((void*)(l_Lake_Pattern_not___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_509_, 0, v_inst_506_);
lean_closure_set(v___f_509_, 1, v___x_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_508_);
v___x_512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_512_, 0, v___f_509_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg(){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Lake_PatternDescr_empty___redArg___closed__1));
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty___redArg___boxed(lean_object* v___dummy_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lake_PatternDescr_empty___redArg();
return v_res_520_;
}
}
static lean_object* _init_l_Lake_PatternDescr_empty___closed__0(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lake_PatternDescr_empty___redArg();
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_empty(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_524_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___redArg___closed__3(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
v___x_530_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__2, &l_Lake_Pattern_empty___redArg___closed__2_once, _init_l_Lake_Pattern_empty___redArg___closed__2);
v___x_531_ = ((lean_object*)(l_Lake_Pattern_empty___redArg___closed__1));
v___f_532_ = ((lean_object*)(l_Lake_instInhabitedPattern_default__1___redArg___closed__0));
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v___f_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg(){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lake_Pattern_empty___redArg___closed__3, &l_Lake_Pattern_empty___redArg___closed__3_once, _init_l_Lake_Pattern_empty___redArg___closed__3);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty___redArg___boxed(lean_object* v___dummy_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lake_Pattern_empty___redArg();
return v_res_537_;
}
}
static lean_object* _init_l_Lake_Pattern_empty___closed__0(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lake_Pattern_empty___redArg();
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_empty(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg(){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr___redArg___boxed(lean_object* v___dummy_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_instEmptyCollectionPatternDescr___redArg();
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPatternDescr(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lake_PatternDescr_empty___closed__0, &l_Lake_PatternDescr_empty___closed__0_once, _init_l_Lake_PatternDescr_empty___closed__0);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg(){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern___redArg___boxed(lean_object* v___dummy_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lake_instEmptyCollectionPattern___redArg();
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionPattern(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lake_Pattern_empty___closed__0, &l_Lake_Pattern_empty___closed__0_once, _init_l_Lake_Pattern_empty___closed__0);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg(){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lake_PatternDescr_star___redArg___closed__0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star___redArg___boxed(lean_object* v___dummy_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_PatternDescr_star___redArg();
return v_res_561_;
}
}
static lean_object* _init_l_Lake_PatternDescr_star___closed__0(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lake_PatternDescr_star___redArg();
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_PatternDescr_star(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
return v___x_565_;
}
}
LEAN_EXPORT uint8_t l_Lake_Pattern_star___redArg___lam__0(lean_object* v_x_566_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = 1;
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___lam__0___boxed(lean_object* v_x_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Lake_Pattern_star___redArg___lam__0(v_x_568_);
lean_dec(v_x_568_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lake_PatternDescr_star___closed__0, &l_Lake_PatternDescr_star___closed__0_once, _init_l_Lake_PatternDescr_star___closed__0);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lake_Pattern_star___redArg___closed__4(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__3, &l_Lake_Pattern_star___redArg___closed__3_once, _init_l_Lake_Pattern_star___redArg___closed__3);
v___x_578_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__2));
v___f_579_ = ((lean_object*)(l_Lake_Pattern_star___redArg___closed__0));
v___x_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_580_, 0, v___f_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg(){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lake_Pattern_star___redArg___closed__4, &l_Lake_Pattern_star___redArg___closed__4_once, _init_l_Lake_Pattern_star___redArg___closed__4);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star___redArg___boxed(lean_object* v___dummy_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lake_Pattern_star___redArg();
return v_res_584_;
}
}
static lean_object* _init_l_Lake_Pattern_star___closed__0(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lake_Pattern_star___redArg();
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Pattern_star(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lake_Pattern_star___closed__0, &l_Lake_Pattern_star___closed__0_once, _init_l_Lake_Pattern_star___closed__0);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl(lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_tag_nat(v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorIdx___impl___boxed(lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lake_StrPatDescr_ctorIdx___impl(v_x_591_);
lean_dec_ref(v_x_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___redArg(lean_object* v_t_593_, lean_object* v_k_594_){
_start:
{
lean_object* v_xs_595_; lean_object* v___x_596_; 
v_xs_595_ = lean_ctor_get(v_t_593_, 0);
lean_inc_ref(v_xs_595_);
lean_dec_ref(v_t_593_);
v___x_596_ = lean_apply_1(v_k_594_, v_xs_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim(lean_object* v_motive_597_, lean_object* v_ctorIdx_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_k_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_599_, v_k_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_ctorElim___boxed(lean_object* v_motive_603_, lean_object* v_ctorIdx_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_k_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lake_StrPatDescr_ctorElim(v_motive_603_, v_ctorIdx_604_, v_t_605_, v_h_606_, v_k_607_);
lean_dec(v_ctorIdx_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim___redArg(lean_object* v_t_609_, lean_object* v_mem_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_609_, v_mem_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_mem_elim(lean_object* v_motive_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_mem_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_613_, v_mem_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim___redArg(lean_object* v_t_617_, lean_object* v_startsWith_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_617_, v_startsWith_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_startsWith_elim(lean_object* v_motive_620_, lean_object* v_t_621_, lean_object* v_h_622_, lean_object* v_startsWith_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_621_, v_startsWith_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim___redArg(lean_object* v_t_625_, lean_object* v_endsWith_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_625_, v_endsWith_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_endsWith_elim(lean_object* v_motive_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_endsWith_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lake_StrPatDescr_ctorElim___redArg(v_t_629_, v_endsWith_631_);
return v___x_632_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(lean_object* v_a_639_, lean_object* v_as_640_, size_t v_i_641_, size_t v_stop_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_eq(v_i_641_, v_stop_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_array_uget_borrowed(v_as_640_, v_i_641_);
v___x_645_ = lean_string_dec_eq(v_a_639_, v___x_644_);
if (v___x_645_ == 0)
{
size_t v___x_646_; size_t v___x_647_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_641_, v___x_646_);
v_i_641_ = v___x_647_;
goto _start;
}
else
{
return v___x_645_;
}
}
else
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0___boxed(lean_object* v_a_650_, lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_stop_653_){
_start:
{
size_t v_i_boxed_654_; size_t v_stop_boxed_655_; uint8_t v_res_656_; lean_object* v_r_657_; 
v_i_boxed_654_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v_stop_boxed_655_ = lean_unbox_usize(v_stop_653_);
lean_dec(v_stop_653_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_650_, v_as_651_, v_i_boxed_654_, v_stop_boxed_655_);
lean_dec_ref(v_as_651_);
lean_dec_ref(v_a_650_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(lean_object* v_as_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_as_658_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
return v___x_662_;
}
else
{
if (v___x_662_ == 0)
{
return v___x_662_;
}
else
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_661_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_StrPatDescr_matches_spec__0_spec__0(v_a_659_, v_as_658_, v___x_663_, v___x_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0___boxed(lean_object* v_as_666_, lean_object* v_a_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_as_666_, v_a_667_);
lean_dec_ref(v_a_667_);
lean_dec_ref(v_as_666_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPatDescr_matches(lean_object* v_s_670_, lean_object* v_self_671_){
_start:
{
switch(lean_obj_tag(v_self_671_))
{
case 0:
{
lean_object* v_xs_672_; uint8_t v___x_673_; 
v_xs_672_ = lean_ctor_get(v_self_671_, 0);
v___x_673_ = l_Array_contains___at___00Lake_StrPatDescr_matches_spec__0(v_xs_672_, v_s_670_);
return v___x_673_;
}
case 1:
{
lean_object* v_affix_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_affix_674_ = lean_ctor_get(v_self_671_, 0);
v___x_675_ = lean_string_utf8_byte_size(v_s_670_);
v___x_676_ = lean_string_utf8_byte_size(v_affix_674_);
v___x_677_ = lean_nat_dec_le(v___x_676_, v___x_675_);
if (v___x_677_ == 0)
{
return v___x_677_;
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_string_memcmp(v_s_670_, v_affix_674_, v___x_678_, v___x_678_, v___x_676_);
return v___x_679_;
}
}
default: 
{
lean_object* v_affix_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_affix_680_ = lean_ctor_get(v_self_671_, 0);
v___x_681_ = lean_string_utf8_byte_size(v_s_670_);
v___x_682_ = lean_string_utf8_byte_size(v_affix_680_);
v___x_683_ = lean_nat_dec_le(v___x_682_, v___x_681_);
if (v___x_683_ == 0)
{
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_sub(v___x_681_, v___x_682_);
v___x_686_ = lean_string_memcmp(v_s_670_, v_affix_680_, v___x_685_, v___x_684_, v___x_682_);
lean_dec(v___x_685_);
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_matches___boxed(lean_object* v_s_687_, lean_object* v_self_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lake_StrPatDescr_matches(v_s_687_, v_self_688_);
lean_dec_ref(v_self_688_);
lean_dec_ref(v_s_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_mem___lam__0(lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_x_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lake_PatternDescr_matches___redArg(v___x_695_, v_x_697_, v___x_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem___lam__0___boxed(lean_object* v___x_699_, lean_object* v___x_700_, lean_object* v_x_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lake_StrPat_mem___lam__0(v___x_699_, v___x_700_, v_x_701_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_mem(lean_object* v_xs_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_705_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_xs_704_);
v___x_707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_inc_ref(v___x_707_);
v___f_708_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_708_, 0, v___x_705_);
lean_closure_set(v___f_708_, 1, v___x_707_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_707_);
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v___f_708_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeArrayStringStrPatDescr___lam__0(lean_object* v_xs_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_xs_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_startsWith(lean_object* v_affix_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_719_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_affix_718_);
v___x_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_inc_ref(v___x_721_);
v___f_722_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_722_, 0, v___x_719_);
lean_closure_set(v___f_722_, 1, v___x_721_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___f_722_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_endsWith(lean_object* v_affix_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_727_ = ((lean_object*)(l_Lake_instIsPatternStrPatDescrString));
v___x_728_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_728_, 0, v_affix_726_);
v___x_729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_inc_ref(v___x_729_);
v___f_730_ = lean_alloc_closure((void*)(l_Lake_StrPat_mem___lam__0___boxed), 3, 2);
lean_closure_set(v___f_730_, 0, v___x_727_);
lean_closure_set(v___f_730_, 1, v___x_729_);
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
v___x_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_733_, 0, v___f_730_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPatDescr_beq(lean_object* v_s_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
v___x_737_ = lean_array_push(v___x_736_, v_s_734_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_beq___lam__0(lean_object* v_s_739_, lean_object* v_x_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = lean_string_dec_eq(v_x_740_, v_s_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq___lam__0___boxed(lean_object* v_s_742_, lean_object* v_x_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Lake_StrPat_beq___lam__0(v_s_742_, v_x_743_);
lean_dec_ref(v_x_743_);
lean_dec_ref(v_s_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_beq(lean_object* v_s_749_){
_start:
{
lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc_ref(v_s_749_);
v___f_750_ = lean_alloc_closure((void*)(l_Lake_StrPat_beq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_750_, 0, v_s_749_);
v___x_751_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_752_ = l_Lake_StrPatDescr_beq(v_s_749_);
v___x_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v___f_750_);
lean_ctor_set(v___x_755_, 1, v___x_751_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl(lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_tag_nat(v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorIdx___impl___boxed(lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_PathPatDescr_ctorIdx___impl(v_x_762_);
lean_dec_ref(v_x_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___redArg(lean_object* v_t_764_, lean_object* v_k_765_){
_start:
{
lean_object* v_p_766_; lean_object* v___x_767_; 
v_p_766_ = lean_ctor_get(v_t_764_, 0);
lean_inc_ref(v_p_766_);
lean_dec_ref(v_t_764_);
v___x_767_ = lean_apply_1(v_k_765_, v_p_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim(lean_object* v_motive_768_, lean_object* v_ctorIdx_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_770_, v_k_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_ctorElim___boxed(lean_object* v_motive_774_, lean_object* v_ctorIdx_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_PathPatDescr_ctorElim(v_motive_774_, v_ctorIdx_775_, v_t_776_, v_h_777_, v_k_778_);
lean_dec(v_ctorIdx_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim___redArg(lean_object* v_t_780_, lean_object* v_path_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_780_, v_path_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_path_elim(lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_path_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_784_, v_path_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim___redArg(lean_object* v_t_788_, lean_object* v_extension_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_788_, v_extension_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_extension_elim(lean_object* v_motive_791_, lean_object* v_t_792_, lean_object* v_h_793_, lean_object* v_extension_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_792_, v_extension_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim___redArg(lean_object* v_t_796_, lean_object* v_fileName_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_796_, v_fileName_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_fileName_elim(lean_object* v_motive_799_, lean_object* v_t_800_, lean_object* v_h_801_, lean_object* v_fileName_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lake_PathPatDescr_ctorElim___redArg(v_t_800_, v_fileName_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default___closed__0(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_obj_once(&l_Lake_instInhabitedPattern_default__1___closed__0, &l_Lake_instInhabitedPattern_default__1___closed__0_once, _init_l_Lake_instInhabitedPattern_default__1___closed__0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr_default(void){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = lean_obj_once(&l_Lake_instInhabitedPathPatDescr_default___closed__0, &l_Lake_instInhabitedPathPatDescr_default___closed__0_once, _init_l_Lake_instInhabitedPathPatDescr_default___closed__0);
return v___x_806_;
}
}
static lean_object* _init_l_Lake_instInhabitedPathPatDescr(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lake_instInhabitedPathPatDescr_default;
return v___x_807_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_eq___lam__0(lean_object* v_p_808_, lean_object* v_x_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = lean_string_dec_eq(v_x_809_, v_p_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq___lam__0___boxed(lean_object* v_p_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lake_PathPatDescr_eq___lam__0(v_p_811_, v_x_812_);
lean_dec_ref(v_x_812_);
lean_dec_ref(v_p_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_eq(lean_object* v_p_815_){
_start:
{
lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_inc_ref(v_p_815_);
v___f_816_ = lean_alloc_closure((void*)(l_Lake_PathPatDescr_eq___lam__0___boxed), 2, 1);
lean_closure_set(v___f_816_, 0, v_p_815_);
v___x_817_ = ((lean_object*)(l_Lake_StrPat_beq___closed__1));
v___x_818_ = l_Lake_StrPatDescr_beq(v_p_815_);
v___x_819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_821_, 0, v___f_816_);
lean_ctor_set(v___x_821_, 1, v___x_817_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPatDescr_matches(lean_object* v_path_823_, lean_object* v_self_824_){
_start:
{
switch(lean_obj_tag(v_self_824_))
{
case 0:
{
lean_object* v_p_825_; lean_object* v_filter_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_p_825_ = lean_ctor_get(v_self_824_, 0);
lean_inc_ref(v_p_825_);
lean_dec_ref_known(v_self_824_, 1);
v_filter_826_ = lean_ctor_get(v_p_825_, 0);
lean_inc_ref(v_filter_826_);
lean_dec_ref(v_p_825_);
v___x_827_ = l_System_FilePath_normalize(v_path_823_);
v___x_828_ = lean_apply_1(v_filter_826_, v___x_827_);
v___x_829_ = lean_unbox(v___x_828_);
return v___x_829_;
}
case 1:
{
lean_object* v_p_830_; lean_object* v___x_831_; 
v_p_830_ = lean_ctor_get(v_self_824_, 0);
lean_inc_ref(v_p_830_);
lean_dec_ref_known(v_self_824_, 1);
v___x_831_ = l_System_FilePath_extension(v_path_823_);
if (lean_obj_tag(v___x_831_) == 0)
{
uint8_t v___x_832_; 
lean_dec_ref(v_p_830_);
v___x_832_ = 0;
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v_filter_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_831_, 1);
v_filter_834_ = lean_ctor_get(v_p_830_, 0);
lean_inc_ref(v_filter_834_);
lean_dec_ref(v_p_830_);
v___x_835_ = lean_apply_1(v_filter_834_, v_val_833_);
v___x_836_ = lean_unbox(v___x_835_);
return v___x_836_;
}
}
default: 
{
lean_object* v_p_837_; lean_object* v___x_838_; 
v_p_837_ = lean_ctor_get(v_self_824_, 0);
lean_inc_ref(v_p_837_);
lean_dec_ref_known(v_self_824_, 1);
v___x_838_ = l_System_FilePath_fileName(v_path_823_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lake_PathPatDescr_matches___boxed(lean_object* v_path_844_, lean_object* v_self_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lake_PathPatDescr_matches(v_path_844_, v_self_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lake_PathPat_path___lam__0(lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Lake_PatternDescr_matches___redArg(v___x_852_, v_x_854_, v___x_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path___lam__0___boxed(lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Lake_PathPat_path___lam__0(v___x_856_, v___x_857_, v_x_858_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_path(lean_object* v_p_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_862_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_p_861_);
v___x_864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_inc_ref(v___x_864_);
v___f_865_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_865_, 0, v___x_862_);
lean_closure_set(v___f_865_, 1, v___x_864_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_864_);
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v___f_865_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_extension(lean_object* v_p_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_870_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_p_869_);
v___x_872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_inc_ref(v___x_872_);
v___f_873_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_873_, 0, v___x_870_);
lean_closure_set(v___f_873_, 1, v___x_872_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_872_);
v___x_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_876_, 0, v___f_873_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_PathPat_fileName(lean_object* v_p_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_878_ = ((lean_object*)(l_Lake_instIsPatternPathPatDescrFilePath));
v___x_879_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_879_, 0, v_p_877_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_inc_ref(v___x_880_);
v___f_881_ = lean_alloc_closure((void*)(l_Lake_PathPat_path___lam__0___boxed), 3, 2);
lean_closure_set(v___f_881_, 0, v___x_878_);
lean_closure_set(v___f_881_, 1, v___x_880_);
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_880_);
v___x_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_884_, 0, v___f_881_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_h__1_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_2(v_h__1_887_, v_x_885_, v_x_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Pattern_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_h__1_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_2(v_h__1_892_, v_x_890_, v_x_891_);
return v___x_893_;
}
}
LEAN_EXPORT uint8_t l_Lake_isVerLike(lean_object* v_s_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(2u);
v___x_896_ = lean_string_utf8_byte_size(v_s_894_);
v___x_897_ = lean_nat_dec_le(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
return v___x_897_;
}
else
{
lean_object* v___x_898_; uint32_t v___x_899_; uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_string_utf8_get_fast(v_s_894_, v___x_898_);
v___x_900_ = 118;
v___x_901_ = lean_uint32_dec_eq(v___x_899_, v___x_900_);
if (v___x_901_ == 0)
{
return v___x_901_;
}
else
{
lean_object* v___x_902_; uint32_t v___x_903_; uint32_t v___x_904_; uint8_t v___x_905_; 
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_string_utf8_get_fast(v_s_894_, v___x_902_);
v___x_904_ = 48;
v___x_905_ = lean_uint32_dec_le(v___x_904_, v___x_903_);
if (v___x_905_ == 0)
{
return v___x_905_;
}
else
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 57;
v___x_907_ = lean_uint32_dec_le(v___x_903_, v___x_906_);
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_isVerLike___boxed(lean_object* v_s_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lake_isVerLike(v_s_908_);
lean_dec_ref(v_s_908_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(lean_object* v_k_928_, lean_object* v_v_929_, lean_object* v_t_930_){
_start:
{
if (lean_obj_tag(v_t_930_) == 0)
{
lean_object* v_size_931_; lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v_l_934_; lean_object* v_r_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_1215_; 
v_size_931_ = lean_ctor_get(v_t_930_, 0);
v_k_932_ = lean_ctor_get(v_t_930_, 1);
v_v_933_ = lean_ctor_get(v_t_930_, 2);
v_l_934_ = lean_ctor_get(v_t_930_, 3);
v_r_935_ = lean_ctor_get(v_t_930_, 4);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_t_930_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_937_ = v_t_930_;
v_isShared_938_ = v_isSharedCheck_1215_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_r_935_);
lean_inc(v_l_934_);
lean_inc(v_v_933_);
lean_inc(v_k_932_);
lean_inc(v_size_931_);
lean_dec(v_t_930_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_1215_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
uint8_t v___x_939_; 
v___x_939_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_928_, v_k_932_);
switch(v___x_939_)
{
case 0:
{
lean_object* v_impl_940_; lean_object* v___x_941_; 
lean_dec(v_size_931_);
v_impl_940_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_928_, v_v_929_, v_l_934_);
v___x_941_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_935_) == 0)
{
lean_object* v_size_942_; lean_object* v_size_943_; lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v_l_946_; lean_object* v_r_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_size_942_ = lean_ctor_get(v_r_935_, 0);
v_size_943_ = lean_ctor_get(v_impl_940_, 0);
v_k_944_ = lean_ctor_get(v_impl_940_, 1);
v_v_945_ = lean_ctor_get(v_impl_940_, 2);
v_l_946_ = lean_ctor_get(v_impl_940_, 3);
v_r_947_ = lean_ctor_get(v_impl_940_, 4);
lean_inc(v_r_947_);
v___x_948_ = lean_unsigned_to_nat(3u);
v___x_949_ = lean_nat_mul(v___x_948_, v_size_942_);
v___x_950_ = lean_nat_dec_lt(v___x_949_, v_size_943_);
lean_dec(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec(v_r_947_);
v___x_951_ = lean_nat_add(v___x_941_, v_size_943_);
v___x_952_ = lean_nat_add(v___x_951_, v_size_942_);
lean_dec(v___x_951_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 3, v_impl_940_);
lean_ctor_set(v___x_937_, 0, v___x_952_);
v___x_954_ = v___x_937_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_impl_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_r_935_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1021_; 
lean_inc(v_l_946_);
lean_inc(v_v_945_);
lean_inc(v_k_944_);
lean_inc(v_size_943_);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_impl_940_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1022_ = lean_ctor_get(v_impl_940_, 4);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_impl_940_, 3);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_impl_940_, 2);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_impl_940_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_940_, 0);
lean_dec(v_unused_1026_);
v___x_957_ = v_impl_940_;
v_isShared_958_ = v_isSharedCheck_1021_;
goto v_resetjp_956_;
}
else
{
lean_dec(v_impl_940_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1021_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_size_959_; lean_object* v_size_960_; lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_l_963_; lean_object* v_r_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_959_ = lean_ctor_get(v_l_946_, 0);
v_size_960_ = lean_ctor_get(v_r_947_, 0);
v_k_961_ = lean_ctor_get(v_r_947_, 1);
v_v_962_ = lean_ctor_get(v_r_947_, 2);
v_l_963_ = lean_ctor_get(v_r_947_, 3);
v_r_964_ = lean_ctor_get(v_r_947_, 4);
v___x_965_ = lean_unsigned_to_nat(2u);
v___x_966_ = lean_nat_mul(v___x_965_, v_size_959_);
v___x_967_ = lean_nat_dec_lt(v_size_960_, v___x_966_);
lean_dec(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_996_; 
lean_inc(v_r_964_);
lean_inc(v_l_963_);
lean_inc(v_v_962_);
lean_inc(v_k_961_);
v_isSharedCheck_996_ = !lean_is_exclusive(v_r_947_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; 
v_unused_997_ = lean_ctor_get(v_r_947_, 4);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_947_, 3);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_947_, 2);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_947_, 1);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_r_947_, 0);
lean_dec(v_unused_1001_);
v___x_969_ = v_r_947_;
v_isShared_970_ = v_isSharedCheck_996_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_r_947_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_996_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___x_984_; lean_object* v___y_986_; 
v___x_971_ = lean_nat_add(v___x_941_, v_size_943_);
lean_dec(v_size_943_);
v___x_972_ = lean_nat_add(v___x_971_, v_size_942_);
lean_dec(v___x_971_);
v___x_984_ = lean_nat_add(v___x_941_, v_size_959_);
if (lean_obj_tag(v_l_963_) == 0)
{
lean_object* v_size_994_; 
v_size_994_ = lean_ctor_get(v_l_963_, 0);
lean_inc(v_size_994_);
v___y_986_ = v_size_994_;
goto v___jp_985_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___y_986_ = v___x_995_;
goto v___jp_985_;
}
v___jp_973_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_nat_add(v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_r_935_);
lean_ctor_set(v___x_969_, 3, v_r_964_);
lean_ctor_set(v___x_969_, 2, v_v_933_);
lean_ctor_set(v___x_969_, 1, v_k_932_);
lean_ctor_set(v___x_969_, 0, v___x_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_r_964_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_r_935_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 4, v___x_979_);
lean_ctor_set(v___x_957_, 3, v___y_974_);
lean_ctor_set(v___x_957_, 2, v_v_962_);
lean_ctor_set(v___x_957_, 1, v_k_961_);
lean_ctor_set(v___x_957_, 0, v___x_972_);
v___x_981_ = v___x_957_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v___y_974_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
v___jp_985_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_nat_add(v___x_984_, v___y_986_);
lean_dec(v___y_986_);
lean_dec(v___x_984_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_l_963_);
lean_ctor_set(v___x_937_, 3, v_l_946_);
lean_ctor_set(v___x_937_, 2, v_v_945_);
lean_ctor_set(v___x_937_, 1, v_k_944_);
lean_ctor_set(v___x_937_, 0, v___x_987_);
v___x_989_ = v___x_937_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_946_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_l_963_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = lean_nat_add(v___x_941_, v_size_942_);
if (lean_obj_tag(v_r_964_) == 0)
{
lean_object* v_size_991_; 
v_size_991_ = lean_ctor_get(v_r_964_, 0);
lean_inc(v_size_991_);
v___y_974_ = v___x_989_;
v___y_975_ = v___x_990_;
v___y_976_ = v_size_991_;
goto v___jp_973_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v___y_974_ = v___x_989_;
v___y_975_ = v___x_990_;
v___y_976_ = v___x_992_;
goto v___jp_973_;
}
}
}
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_del_object(v___x_937_);
v___x_1002_ = lean_nat_add(v___x_941_, v_size_943_);
lean_dec(v_size_943_);
v___x_1003_ = lean_nat_add(v___x_1002_, v_size_942_);
lean_dec(v___x_1002_);
v___x_1004_ = lean_nat_add(v___x_941_, v_size_942_);
v___x_1005_ = lean_nat_add(v___x_1004_, v_size_960_);
lean_dec(v___x_1004_);
lean_inc_ref(v_r_935_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 4, v_r_935_);
lean_ctor_set(v___x_957_, 3, v_r_947_);
lean_ctor_set(v___x_957_, 2, v_v_933_);
lean_ctor_set(v___x_957_, 1, v_k_932_);
lean_ctor_set(v___x_957_, 0, v___x_1005_);
v___x_1007_ = v___x_957_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_r_947_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_r_935_);
v___x_1007_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v_r_935_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1015_ = lean_ctor_get(v_r_935_, 4);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_r_935_, 3);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_935_, 2);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_935_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_r_935_, 0);
lean_dec(v_unused_1019_);
v___x_1009_ = v_r_935_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v_r_935_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___x_1007_);
lean_ctor_set(v___x_1009_, 3, v_l_946_);
lean_ctor_set(v___x_1009_, 2, v_v_945_);
lean_ctor_set(v___x_1009_, 1, v_k_944_);
lean_ctor_set(v___x_1009_, 0, v___x_1003_);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_l_946_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v___x_1007_);
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
}
else
{
lean_object* v_l_1027_; 
v_l_1027_ = lean_ctor_get(v_impl_940_, 3);
if (lean_obj_tag(v_l_1027_) == 0)
{
lean_object* v_r_1028_; lean_object* v_k_1029_; lean_object* v_v_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1041_; 
lean_inc_ref(v_l_1027_);
v_r_1028_ = lean_ctor_get(v_impl_940_, 4);
v_k_1029_ = lean_ctor_get(v_impl_940_, 1);
v_v_1030_ = lean_ctor_get(v_impl_940_, 2);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_impl_940_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1042_ = lean_ctor_get(v_impl_940_, 3);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_impl_940_, 0);
lean_dec(v_unused_1043_);
v___x_1032_ = v_impl_940_;
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_r_1028_);
lean_inc(v_v_1030_);
lean_inc(v_k_1029_);
lean_dec(v_impl_940_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 3, v_r_1028_);
lean_ctor_set(v___x_1032_, 2, v_v_933_);
lean_ctor_set(v___x_1032_, 1, v_k_932_);
lean_ctor_set(v___x_1032_, 0, v___x_941_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_1028_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_r_1028_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v___x_1036_);
lean_ctor_set(v___x_937_, 3, v_l_1027_);
lean_ctor_set(v___x_937_, 2, v_v_1030_);
lean_ctor_set(v___x_937_, 1, v_k_1029_);
lean_ctor_set(v___x_937_, 0, v___x_1034_);
v___x_1038_ = v___x_937_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_l_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_r_1044_; 
v_r_1044_ = lean_ctor_get(v_impl_940_, 4);
lean_inc(v_r_1044_);
if (lean_obj_tag(v_r_1044_) == 0)
{
lean_object* v_k_1045_; lean_object* v_v_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1069_; 
lean_inc(v_l_1027_);
v_k_1045_ = lean_ctor_get(v_impl_940_, 1);
v_v_1046_ = lean_ctor_get(v_impl_940_, 2);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_impl_940_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1070_ = lean_ctor_get(v_impl_940_, 4);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_impl_940_, 3);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_impl_940_, 0);
lean_dec(v_unused_1072_);
v___x_1048_ = v_impl_940_;
v_isShared_1049_ = v_isSharedCheck_1069_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_v_1046_);
lean_inc(v_k_1045_);
lean_dec(v_impl_940_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1069_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_k_1050_; lean_object* v_v_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1065_; 
v_k_1050_ = lean_ctor_get(v_r_1044_, 1);
v_v_1051_ = lean_ctor_get(v_r_1044_, 2);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_r_1044_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; 
v_unused_1066_ = lean_ctor_get(v_r_1044_, 4);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_r_1044_, 3);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_r_1044_, 0);
lean_dec(v_unused_1068_);
v___x_1053_ = v_r_1044_;
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_v_1051_);
lean_inc(v_k_1050_);
lean_dec(v_r_1044_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_unsigned_to_nat(3u);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v_l_1027_);
lean_ctor_set(v___x_1053_, 3, v_l_1027_);
lean_ctor_set(v___x_1053_, 2, v_v_1046_);
lean_ctor_set(v___x_1053_, 1, v_k_1045_);
lean_ctor_set(v___x_1053_, 0, v___x_941_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_l_1027_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_l_1027_);
v___x_1057_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 4, v_l_1027_);
lean_ctor_set(v___x_1048_, 2, v_v_933_);
lean_ctor_set(v___x_1048_, 1, v_k_932_);
lean_ctor_set(v___x_1048_, 0, v___x_941_);
v___x_1059_ = v___x_1048_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_l_1027_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_l_1027_);
v___x_1059_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v___x_1059_);
lean_ctor_set(v___x_937_, 3, v___x_1057_);
lean_ctor_set(v___x_937_, 2, v_v_1051_);
lean_ctor_set(v___x_937_, 1, v_k_1050_);
lean_ctor_set(v___x_937_, 0, v___x_1055_);
v___x_1061_ = v___x_937_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_k_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_v_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_unsigned_to_nat(2u);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_r_1044_);
lean_ctor_set(v___x_937_, 3, v_impl_940_);
lean_ctor_set(v___x_937_, 0, v___x_1073_);
v___x_1075_ = v___x_937_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_impl_940_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_r_1044_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1078_; 
lean_dec(v_v_933_);
lean_dec(v_k_932_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 2, v_v_929_);
lean_ctor_set(v___x_937_, 1, v_k_928_);
v___x_1078_ = v___x_937_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_size_931_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_928_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_929_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_l_934_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_r_935_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
default: 
{
lean_object* v_impl_1080_; lean_object* v___x_1081_; 
lean_dec(v_size_931_);
v_impl_1080_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_928_, v_v_929_, v_r_935_);
v___x_1081_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_934_) == 0)
{
lean_object* v_size_1082_; lean_object* v_size_1083_; lean_object* v_k_1084_; lean_object* v_v_1085_; lean_object* v_l_1086_; lean_object* v_r_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_size_1082_ = lean_ctor_get(v_l_934_, 0);
v_size_1083_ = lean_ctor_get(v_impl_1080_, 0);
v_k_1084_ = lean_ctor_get(v_impl_1080_, 1);
v_v_1085_ = lean_ctor_get(v_impl_1080_, 2);
v_l_1086_ = lean_ctor_get(v_impl_1080_, 3);
lean_inc(v_l_1086_);
v_r_1087_ = lean_ctor_get(v_impl_1080_, 4);
v___x_1088_ = lean_unsigned_to_nat(3u);
v___x_1089_ = lean_nat_mul(v___x_1088_, v_size_1082_);
v___x_1090_ = lean_nat_dec_lt(v___x_1089_, v_size_1083_);
lean_dec(v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_dec(v_l_1086_);
v___x_1091_ = lean_nat_add(v___x_1081_, v_size_1082_);
v___x_1092_ = lean_nat_add(v___x_1091_, v_size_1083_);
lean_dec(v___x_1091_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_impl_1080_);
lean_ctor_set(v___x_937_, 0, v___x_1092_);
v___x_1094_ = v___x_937_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_934_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_impl_1080_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1159_; 
lean_inc(v_r_1087_);
lean_inc(v_v_1085_);
lean_inc(v_k_1084_);
lean_inc(v_size_1083_);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_impl_1080_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1160_ = lean_ctor_get(v_impl_1080_, 4);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_impl_1080_, 3);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_impl_1080_, 2);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_impl_1080_, 1);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_impl_1080_, 0);
lean_dec(v_unused_1164_);
v___x_1097_ = v_impl_1080_;
v_isShared_1098_ = v_isSharedCheck_1159_;
goto v_resetjp_1096_;
}
else
{
lean_dec(v_impl_1080_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1159_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_size_1099_; lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v_l_1102_; lean_object* v_r_1103_; lean_object* v_size_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_size_1099_ = lean_ctor_get(v_l_1086_, 0);
v_k_1100_ = lean_ctor_get(v_l_1086_, 1);
v_v_1101_ = lean_ctor_get(v_l_1086_, 2);
v_l_1102_ = lean_ctor_get(v_l_1086_, 3);
v_r_1103_ = lean_ctor_get(v_l_1086_, 4);
v_size_1104_ = lean_ctor_get(v_r_1087_, 0);
v___x_1105_ = lean_unsigned_to_nat(2u);
v___x_1106_ = lean_nat_mul(v___x_1105_, v_size_1104_);
v___x_1107_ = lean_nat_dec_lt(v_size_1099_, v___x_1106_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1135_; 
lean_inc(v_r_1103_);
lean_inc(v_l_1102_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1136_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1140_);
v___x_1109_ = v_l_1086_;
v_isShared_1110_ = v_isSharedCheck_1135_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_l_1086_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1135_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1125_; 
v___x_1111_ = lean_nat_add(v___x_1081_, v_size_1082_);
v___x_1112_ = lean_nat_add(v___x_1111_, v_size_1083_);
lean_dec(v_size_1083_);
if (lean_obj_tag(v_l_1102_) == 0)
{
lean_object* v_size_1133_; 
v_size_1133_ = lean_ctor_get(v_l_1102_, 0);
lean_inc(v_size_1133_);
v___y_1125_ = v_size_1133_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___y_1125_ = v___x_1134_;
goto v___jp_1124_;
}
v___jp_1113_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_nat_add(v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v_r_1087_);
lean_ctor_set(v___x_1109_, 3, v_r_1103_);
lean_ctor_set(v___x_1109_, 2, v_v_1085_);
lean_ctor_set(v___x_1109_, 1, v_k_1084_);
lean_ctor_set(v___x_1109_, 0, v___x_1117_);
v___x_1119_ = v___x_1109_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_r_1103_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_r_1087_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 4, v___x_1119_);
lean_ctor_set(v___x_1097_, 3, v___y_1114_);
lean_ctor_set(v___x_1097_, 2, v_v_1101_);
lean_ctor_set(v___x_1097_, 1, v_k_1100_);
lean_ctor_set(v___x_1097_, 0, v___x_1112_);
v___x_1121_ = v___x_1097_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v___y_1114_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
v___jp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = lean_nat_add(v___x_1111_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec(v___x_1111_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_l_1102_);
lean_ctor_set(v___x_937_, 0, v___x_1126_);
v___x_1128_ = v___x_937_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_l_934_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_l_1102_);
v___x_1128_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_nat_add(v___x_1081_, v_size_1104_);
if (lean_obj_tag(v_r_1103_) == 0)
{
lean_object* v_size_1130_; 
v_size_1130_ = lean_ctor_get(v_r_1103_, 0);
lean_inc(v_size_1130_);
v___y_1114_ = v___x_1128_;
v___y_1115_ = v___x_1129_;
v___y_1116_ = v_size_1130_;
goto v___jp_1113_;
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___y_1114_ = v___x_1128_;
v___y_1115_ = v___x_1129_;
v___y_1116_ = v___x_1131_;
goto v___jp_1113_;
}
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_del_object(v___x_937_);
v___x_1141_ = lean_nat_add(v___x_1081_, v_size_1082_);
v___x_1142_ = lean_nat_add(v___x_1141_, v_size_1083_);
lean_dec(v_size_1083_);
v___x_1143_ = lean_nat_add(v___x_1141_, v_size_1099_);
lean_dec(v___x_1141_);
lean_inc_ref(v_l_934_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 4, v_l_1086_);
lean_ctor_set(v___x_1097_, 3, v_l_934_);
lean_ctor_set(v___x_1097_, 2, v_v_933_);
lean_ctor_set(v___x_1097_, 1, v_k_932_);
lean_ctor_set(v___x_1097_, 0, v___x_1143_);
v___x_1145_ = v___x_1097_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_l_934_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_l_1086_);
v___x_1145_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_isSharedCheck_1152_ = !lean_is_exclusive(v_l_934_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; 
v_unused_1153_ = lean_ctor_get(v_l_934_, 4);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_l_934_, 3);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_l_934_, 2);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_934_, 1);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_l_934_, 0);
lean_dec(v_unused_1157_);
v___x_1147_ = v_l_934_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v_l_934_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 4, v_r_1087_);
lean_ctor_set(v___x_1147_, 3, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v_v_1085_);
lean_ctor_set(v___x_1147_, 1, v_k_1084_);
lean_ctor_set(v___x_1147_, 0, v___x_1142_);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1087_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1165_; 
v_l_1165_ = lean_ctor_get(v_impl_1080_, 3);
lean_inc(v_l_1165_);
if (lean_obj_tag(v_l_1165_) == 0)
{
lean_object* v_r_1166_; lean_object* v_k_1167_; lean_object* v_v_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1191_; 
v_r_1166_ = lean_ctor_get(v_impl_1080_, 4);
v_k_1167_ = lean_ctor_get(v_impl_1080_, 1);
v_v_1168_ = lean_ctor_get(v_impl_1080_, 2);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_impl_1080_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; lean_object* v_unused_1193_; 
v_unused_1192_ = lean_ctor_get(v_impl_1080_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1080_, 0);
lean_dec(v_unused_1193_);
v___x_1170_ = v_impl_1080_;
v_isShared_1171_ = v_isSharedCheck_1191_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_r_1166_);
lean_inc(v_v_1168_);
lean_inc(v_k_1167_);
lean_dec(v_impl_1080_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1191_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_k_1172_; lean_object* v_v_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1187_; 
v_k_1172_ = lean_ctor_get(v_l_1165_, 1);
v_v_1173_ = lean_ctor_get(v_l_1165_, 2);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_l_1165_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1188_ = lean_ctor_get(v_l_1165_, 4);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_l_1165_, 3);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_l_1165_, 0);
lean_dec(v_unused_1190_);
v___x_1175_ = v_l_1165_;
v_isShared_1176_ = v_isSharedCheck_1187_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_v_1173_);
lean_inc(v_k_1172_);
lean_dec(v_l_1165_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1187_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1166_, 2);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 4, v_r_1166_);
lean_ctor_set(v___x_1175_, 3, v_r_1166_);
lean_ctor_set(v___x_1175_, 2, v_v_933_);
lean_ctor_set(v___x_1175_, 1, v_k_932_);
lean_ctor_set(v___x_1175_, 0, v___x_1081_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_1166_);
v___x_1179_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
lean_inc(v_r_1166_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 3, v_r_1166_);
lean_ctor_set(v___x_1170_, 0, v___x_1081_);
v___x_1181_ = v___x_1170_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_1167_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_1168_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_r_1166_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_r_1166_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v___x_1181_);
lean_ctor_set(v___x_937_, 3, v___x_1179_);
lean_ctor_set(v___x_937_, 2, v_v_1173_);
lean_ctor_set(v___x_937_, 1, v_k_1172_);
lean_ctor_set(v___x_937_, 0, v___x_1177_);
v___x_1183_ = v___x_937_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_k_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_v_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
else
{
lean_object* v_r_1194_; 
v_r_1194_ = lean_ctor_get(v_impl_1080_, 4);
lean_inc(v_r_1194_);
if (lean_obj_tag(v_r_1194_) == 0)
{
lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1207_; 
v_k_1195_ = lean_ctor_get(v_impl_1080_, 1);
v_v_1196_ = lean_ctor_get(v_impl_1080_, 2);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_impl_1080_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; 
v_unused_1208_ = lean_ctor_get(v_impl_1080_, 4);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_impl_1080_, 3);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_impl_1080_, 0);
lean_dec(v_unused_1210_);
v___x_1198_ = v_impl_1080_;
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
lean_dec(v_impl_1080_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_unsigned_to_nat(3u);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v_l_1165_);
lean_ctor_set(v___x_1198_, 2, v_v_933_);
lean_ctor_set(v___x_1198_, 1, v_k_932_);
lean_ctor_set(v___x_1198_, 0, v___x_1081_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_l_1165_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_l_1165_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_r_1194_);
lean_ctor_set(v___x_937_, 3, v___x_1202_);
lean_ctor_set(v___x_937_, 2, v_v_1196_);
lean_ctor_set(v___x_937_, 1, v_k_1195_);
lean_ctor_set(v___x_937_, 0, v___x_1200_);
v___x_1204_ = v___x_937_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_r_1194_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_unsigned_to_nat(2u);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v_impl_1080_);
lean_ctor_set(v___x_937_, 3, v_r_1194_);
lean_ctor_set(v___x_937_, 0, v___x_1211_);
v___x_1213_ = v___x_937_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_r_1194_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_impl_1080_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
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
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_k_928_);
lean_ctor_set(v___x_1217_, 2, v_v_929_);
lean_ctor_set(v___x_1217_, 3, v_t_930_);
lean_ctor_set(v___x_1217_, 4, v_t_930_);
return v___x_1217_;
}
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__0(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = ((lean_object*)(l_Lake_StrPat_verLike));
v___x_1220_ = ((lean_object*)(l_Lake_StrPat_verLike___closed__2));
v___x_1221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1220_, v___x_1219_, v___x_1218_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lake_versionTagPresets___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_obj_once(&l_Lake_versionTagPresets___closed__0, &l_Lake_versionTagPresets___closed__0_once, _init_l_Lake_versionTagPresets___closed__0);
v___x_1223_ = ((lean_object*)(l_Lake_defaultVersionTags));
v___x_1224_ = ((lean_object*)(l_Lake_defaultVersionTags___closed__1));
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lake_versionTagPresets(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_obj_once(&l_Lake_versionTagPresets___closed__1, &l_Lake_versionTagPresets___closed__1_once, _init_l_Lake_versionTagPresets___closed__1);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0(lean_object* v_00_u03b2_1227_, lean_object* v_k_1228_, lean_object* v_v_1229_, lean_object* v_t_1230_, lean_object* v_hl_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_versionTagPresets_spec__0___redArg(v_k_1228_, v_v_1229_, v_t_1230_);
return v___x_1232_;
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
