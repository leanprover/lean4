// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Attr
// Imports: public import Lean.Meta.Sym.Simp.Theorems
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSimpTheoremNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpExt(lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4_value;
static const lean_array_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Erasing `Sym.simp` attributes is not supported yet."};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5;
static const lean_array_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sym_simp"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 252, 23, 23, 113, 211, 65, 14)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Sym.simp theorem"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "symSimpExtension"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 157, 124, 152, 13, 216, 140, 99)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_symSimpExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1);
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_6_);
lean_ctor_set(v___x_7_, 5, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(lean_object* v_ext_8_, lean_object* v_b_9_, uint8_t v_kind_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_toCold_15_; lean_object* v_currNamespace_16_; lean_object* v___x_17_; lean_object* v_env_18_; lean_object* v_nextMacroScope_19_; lean_object* v_ngen_20_; lean_object* v_auxDeclNGen_21_; lean_object* v_traceState_22_; lean_object* v_messages_23_; lean_object* v_infoState_24_; lean_object* v_snapshotTasks_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_52_; 
v_toCold_15_ = lean_ctor_get(v___y_12_, 0);
v_currNamespace_16_ = lean_ctor_get(v_toCold_15_, 4);
v___x_17_ = lean_st_ref_take(v___y_13_);
v_env_18_ = lean_ctor_get(v___x_17_, 0);
v_nextMacroScope_19_ = lean_ctor_get(v___x_17_, 1);
v_ngen_20_ = lean_ctor_get(v___x_17_, 2);
v_auxDeclNGen_21_ = lean_ctor_get(v___x_17_, 3);
v_traceState_22_ = lean_ctor_get(v___x_17_, 4);
v_messages_23_ = lean_ctor_get(v___x_17_, 6);
v_infoState_24_ = lean_ctor_get(v___x_17_, 7);
v_snapshotTasks_25_ = lean_ctor_get(v___x_17_, 8);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v___x_17_, 5);
lean_dec(v_unused_53_);
v___x_27_ = v___x_17_;
v_isShared_28_ = v_isSharedCheck_52_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_snapshotTasks_25_);
lean_inc(v_infoState_24_);
lean_inc(v_messages_23_);
lean_inc(v_traceState_22_);
lean_inc(v_auxDeclNGen_21_);
lean_inc(v_ngen_20_);
lean_inc(v_nextMacroScope_19_);
lean_inc(v_env_18_);
lean_dec(v___x_17_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_52_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
lean_inc(v_currNamespace_16_);
v___x_29_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_18_, v_ext_8_, v_b_9_, v_kind_10_, v_currNamespace_16_);
v___x_30_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 5, v___x_30_);
lean_ctor_set(v___x_27_, 0, v___x_29_);
v___x_32_ = v___x_27_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_nextMacroScope_19_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_ngen_20_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_auxDeclNGen_21_);
lean_ctor_set(v_reuseFailAlloc_51_, 4, v_traceState_22_);
lean_ctor_set(v_reuseFailAlloc_51_, 5, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_51_, 6, v_messages_23_);
lean_ctor_set(v_reuseFailAlloc_51_, 7, v_infoState_24_);
lean_ctor_set(v_reuseFailAlloc_51_, 8, v_snapshotTasks_25_);
v___x_32_ = v_reuseFailAlloc_51_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_mctx_35_; lean_object* v_zetaDeltaFVarIds_36_; lean_object* v_postponed_37_; lean_object* v_diag_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_49_; 
v___x_33_ = lean_st_ref_put(v___y_13_, v___x_32_);
v___x_34_ = lean_st_ref_take(v___y_11_);
v_mctx_35_ = lean_ctor_get(v___x_34_, 0);
v_zetaDeltaFVarIds_36_ = lean_ctor_get(v___x_34_, 2);
v_postponed_37_ = lean_ctor_get(v___x_34_, 3);
v_diag_38_ = lean_ctor_get(v___x_34_, 4);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v___x_34_, 1);
lean_dec(v_unused_50_);
v___x_40_ = v___x_34_;
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_diag_38_);
lean_inc(v_postponed_37_);
lean_inc(v_zetaDeltaFVarIds_36_);
lean_inc(v_mctx_35_);
lean_dec(v___x_34_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v___x_42_);
v___x_44_ = v___x_40_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_mctx_35_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v_zetaDeltaFVarIds_36_);
lean_ctor_set(v_reuseFailAlloc_48_, 3, v_postponed_37_);
lean_ctor_set(v_reuseFailAlloc_48_, 4, v_diag_38_);
v___x_44_ = v_reuseFailAlloc_48_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_st_ref_put(v___y_11_, v___x_44_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(lean_object* v_ext_54_, lean_object* v_b_55_, lean_object* v_kind_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
uint8_t v_kind_boxed_61_; lean_object* v_res_62_; 
v_kind_boxed_61_ = lean_unbox(v_kind_56_);
v_res_62_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_54_, v_b_55_, v_kind_boxed_61_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_00_u03c3_65_, lean_object* v_ext_66_, lean_object* v_b_67_, uint8_t v_kind_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_66_, v_b_67_, v_kind_68_, v___y_70_, v___y_71_, v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_00_u03c3_77_, lean_object* v_ext_78_, lean_object* v_b_79_, lean_object* v_kind_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v_kind_boxed_86_; lean_object* v_res_87_; 
v_kind_boxed_86_ = lean_unbox(v_kind_80_);
v_res_87_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(v_00_u03b1_75_, v_00_u03b2_76_, v_00_u03c3_77_, v_ext_78_, v_b_79_, v_kind_boxed_86_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object* v_ext_88_, lean_object* v_declName_89_, uint8_t v_attrKind_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_89_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_88_, v_a_97_, v_attrKind_90_, v_a_92_, v_a_93_, v_a_94_);
return v___x_98_;
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v_ext_88_);
v_a_99_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_96_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object* v_ext_107_, lean_object* v_declName_108_, lean_object* v_attrKind_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
uint8_t v_attrKind_boxed_115_; lean_object* v_res_116_; 
v_attrKind_boxed_115_ = lean_unbox(v_attrKind_109_);
v_res_116_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_107_, v_declName_108_, v_attrKind_boxed_115_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(lean_object* v_validate_117_, lean_object* v_ext_118_, uint8_t v_attrKind_119_, lean_object* v_as_120_, size_t v_sz_121_, size_t v_i_122_, lean_object* v_b_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_122_, v_sz_121_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v_ext_118_);
lean_dec_ref(v_validate_117_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v_b_123_);
return v___x_130_;
}
else
{
lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_131_ = lean_array_uget_borrowed(v_as_120_, v_i_122_);
lean_inc_ref(v_validate_117_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
lean_inc(v_a_131_);
v___x_132_ = lean_apply_6(v_validate_117_, v_a_131_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; 
lean_dec_ref_known(v___x_132_, 1);
lean_inc(v_a_131_);
lean_inc_ref(v_ext_118_);
v___x_133_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_118_, v_a_131_, v_attrKind_119_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; size_t v___x_135_; size_t v___x_136_; 
lean_dec_ref_known(v___x_133_, 1);
v___x_134_ = lean_box(0);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_add(v_i_122_, v___x_135_);
v_i_122_ = v___x_136_;
v_b_123_ = v___x_134_;
goto _start;
}
else
{
lean_dec_ref(v_ext_118_);
lean_dec_ref(v_validate_117_);
return v___x_133_;
}
}
else
{
lean_dec_ref(v_ext_118_);
lean_dec_ref(v_validate_117_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0___boxed(lean_object* v_validate_138_, lean_object* v_ext_139_, lean_object* v_attrKind_140_, lean_object* v_as_141_, lean_object* v_sz_142_, lean_object* v_i_143_, lean_object* v_b_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v_attrKind_boxed_150_; size_t v_sz_boxed_151_; size_t v_i_boxed_152_; lean_object* v_res_153_; 
v_attrKind_boxed_150_ = lean_unbox(v_attrKind_140_);
v_sz_boxed_151_ = lean_unbox_usize(v_sz_142_);
lean_dec(v_sz_142_);
v_i_boxed_152_ = lean_unbox_usize(v_i_143_);
lean_dec(v_i_143_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_138_, v_ext_139_, v_attrKind_boxed_150_, v_as_141_, v_sz_boxed_151_, v_i_boxed_152_, v_b_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec_ref(v_as_141_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object* v_ext_154_, lean_object* v_declName_155_, uint8_t v_attrKind_156_, lean_object* v_validate_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Sym_Simp_getSimpTheoremNames(v_declName_155_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = lean_box(0);
v_sz_166_ = lean_array_size(v_a_164_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_157_, v_ext_154_, v_attrKind_156_, v_a_164_, v_sz_166_, v___x_167_, v___x_165_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_164_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_176_);
v___x_170_ = v___x_168_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_dec(v___x_168_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_165_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_165_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
else
{
return v___x_168_;
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec_ref(v_validate_157_);
lean_dec_ref(v_ext_154_);
v_a_177_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_163_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_163_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl___boxed(lean_object* v_ext_185_, lean_object* v_declName_186_, lean_object* v_attrKind_187_, lean_object* v_validate_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_attrKind_boxed_194_; lean_object* v_res_195_; 
v_attrKind_boxed_194_ = lean_unbox(v_attrKind_187_);
v_res_195_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_185_, v_declName_186_, v_attrKind_boxed_194_, v_validate_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10));
v___x_223_ = l_Lean_mkAtom(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12);
v___x_225_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_226_ = lean_array_push(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17));
v___x_236_ = l_Lean_mkAtom(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18);
v___x_238_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19);
v___x_241_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16));
v___x_242_ = lean_box(2);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20);
v___x_245_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13);
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21);
v___x_248_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11));
v___x_249_ = lean_box(2);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_247_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22);
v___x_252_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23);
v___x_255_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9));
v___x_256_ = lean_box(2);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24);
v___x_259_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_260_ = lean_array_push(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25);
v___x_262_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7));
v___x_263_ = lean_box(2);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_261_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_267_ = lean_array_push(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27);
v___x_269_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4));
v___x_270_ = lean_box(2);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_273_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
lean_ctor_set(v___x_278_, 2, v___x_277_);
lean_ctor_set(v___x_278_, 3, v___x_277_);
lean_ctor_set(v___x_278_, 4, v___x_276_);
lean_ctor_set(v___x_278_, 5, v___x_276_);
lean_ctor_set(v___x_278_, 6, v___x_276_);
lean_ctor_set(v___x_278_, 7, v___x_276_);
lean_ctor_set(v___x_278_, 8, v___x_276_);
lean_ctor_set(v___x_278_, 9, v___x_276_);
lean_ctor_set(v___x_278_, 10, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_unsigned_to_nat(32u);
v___x_280_ = lean_mk_empty_array_with_capacity(v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = ((size_t)5ULL);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_unsigned_to_nat(32u);
v___x_285_ = lean_mk_empty_array_with_capacity(v___x_284_);
v___x_286_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_287_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
lean_ctor_set(v___x_287_, 2, v___x_283_);
lean_ctor_set(v___x_287_, 3, v___x_283_);
lean_ctor_set_usize(v___x_287_, 4, v___x_282_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_box(1);
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4);
v___x_290_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1);
v___x_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
lean_ctor_set(v___x_291_, 2, v___x_288_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object* v_msgData_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_toCold_297_; lean_object* v_env_298_; lean_object* v_options_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_296_ = lean_st_ref_get(v___y_294_);
v_toCold_297_ = lean_ctor_get(v___y_293_, 0);
v_env_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_296_);
v_options_299_ = lean_ctor_get(v_toCold_297_, 2);
v___x_300_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2);
v___x_301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_299_);
v___x_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_302_, 0, v_env_298_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
lean_ctor_set(v___x_302_, 3, v_options_299_);
v___x_303_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_msgData_292_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msgData_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_ref_314_; lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_ref_314_ = lean_ctor_get(v___y_311_, 2);
v___x_315_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msg_310_, v___y_311_, v___y_312_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_inc(v_ref_314_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_ref_314_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 1);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg___boxed(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object* v___declName_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1);
v___x_338_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v___x_337_, v___y_334_, v___y_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object* v___declName_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(v___declName_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___declName_339_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(v_x_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_x_352_);
return v_res_358_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_365_; uint64_t v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2(void){
_start:
{
uint64_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_uint64_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1);
v___x_368_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_369_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set_uint64(v___x_369_, sizeof(void*)*1, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_box(1);
v___x_374_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4);
v___x_375_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_ctor_set(v___x_381_, 3, v___x_380_);
lean_ctor_set(v___x_381_, 4, v___x_379_);
lean_ctor_set(v___x_381_, 5, v___x_379_);
lean_ctor_set(v___x_381_, 6, v___x_379_);
lean_ctor_set(v___x_381_, 7, v___x_379_);
lean_ctor_set(v___x_381_, 8, v___x_379_);
lean_ctor_set(v___x_381_, 9, v___x_379_);
lean_ctor_set(v___x_381_, 10, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_383_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set(v___x_383_, 3, v___x_382_);
lean_ctor_set(v___x_383_, 4, v___x_382_);
lean_ctor_set(v___x_383_, 5, v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_ctor_set(v___x_385_, 3, v___x_384_);
lean_ctor_set(v___x_385_, 4, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(lean_object* v___x_386_, lean_object* v_ext_387_, lean_object* v___f_388_, lean_object* v_declName_389_, lean_object* v_x_390_, uint8_t v_attrKind_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_395_ = 0;
v___x_396_ = 1;
v___x_397_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4);
v___x_400_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5);
v___x_401_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6));
v___x_402_ = lean_box(0);
lean_inc(v___x_386_);
v___x_403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_403_, 0, v___x_397_);
lean_ctor_set(v___x_403_, 1, v___x_386_);
lean_ctor_set(v___x_403_, 2, v___x_400_);
lean_ctor_set(v___x_403_, 3, v___x_401_);
lean_ctor_set(v___x_403_, 4, v___x_402_);
lean_ctor_set(v___x_403_, 5, v___x_398_);
lean_ctor_set(v___x_403_, 6, v___x_402_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7, v___x_395_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 1, v___x_395_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 2, v___x_395_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 3, v___x_396_);
v___x_404_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7);
v___x_405_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8);
v___x_406_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__9);
v___x_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_407_, 0, v___x_404_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_386_);
lean_ctor_set(v___x_407_, 3, v___x_399_);
lean_ctor_set(v___x_407_, 4, v___x_406_);
v___x_408_ = lean_st_mk_ref(v___x_407_);
v___x_409_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_387_, v_declName_389_, v_attrKind_391_, v___f_388_, v___x_403_, v___x_408_, v___y_392_, v___y_393_);
lean_dec_ref_known(v___x_403_, 7);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_409_, 0);
lean_dec(v_unused_419_);
v___x_411_ = v___x_409_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_dec(v___x_409_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = lean_st_ref_get(v___x_408_);
lean_dec(v___x_408_);
lean_dec(v___x_413_);
v___x_414_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_dec(v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed(lean_object* v___x_420_, lean_object* v_ext_421_, lean_object* v___f_422_, lean_object* v_declName_423_, lean_object* v_x_424_, lean_object* v_attrKind_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v_attrKind_boxed_429_; lean_object* v_res_430_; 
v_attrKind_boxed_429_ = lean_unbox(v_attrKind_425_);
v_res_430_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(v___x_420_, v_ext_421_, v___f_422_, v_declName_423_, v_x_424_, v_attrKind_boxed_429_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_x_424_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object* v_attrName_433_, lean_object* v_attrDescr_434_, lean_object* v_ext_435_, lean_object* v_ref_436_){
_start:
{
lean_object* v___f_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___f_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___f_438_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0));
v___f_439_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1));
v___x_440_ = lean_box(1);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed), 9, 3);
lean_closure_set(v___f_441_, 0, v___x_440_);
lean_closure_set(v___f_441_, 1, v_ext_435_);
lean_closure_set(v___f_441_, 2, v___f_439_);
v___x_442_ = 1;
v___x_443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_443_, 0, v_ref_436_);
lean_ctor_set(v___x_443_, 1, v_attrName_433_);
lean_ctor_set(v___x_443_, 2, v_attrDescr_434_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___f_441_);
lean_ctor_set(v___x_444_, 2, v___f_438_);
v___x_445_ = l_Lean_registerBuiltinAttribute(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object* v_attrName_446_, lean_object* v_attrDescr_447_, lean_object* v_ext_448_, lean_object* v_ref_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_446_, v_attrDescr_447_, v_ext_448_, v_ref_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object* v_00_u03b1_452_, lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_453_, v___y_454_, v___y_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object* v_00_u03b1_458_, lean_object* v_msg_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(v_00_u03b1_458_, v_msg_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_464_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
else
{
lean_object* v_key_468_; lean_object* v_tail_469_; uint8_t v___x_470_; 
v_key_468_ = lean_ctor_get(v_x_466_, 0);
v_tail_469_ = lean_ctor_get(v_x_466_, 2);
v___x_470_ = lean_name_eq(v_key_468_, v_a_465_);
if (v___x_470_ == 0)
{
v_x_466_ = v_tail_469_;
goto _start;
}
else
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_472_, lean_object* v_x_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_472_, v_x_473_);
lean_dec(v_x_473_);
lean_dec(v_a_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_dec(v_b_477_);
lean_dec(v_a_476_);
return v_x_478_;
}
else
{
lean_object* v_key_479_; lean_object* v_value_480_; lean_object* v_tail_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v_key_479_ = lean_ctor_get(v_x_478_, 0);
v_value_480_ = lean_ctor_get(v_x_478_, 1);
v_tail_481_ = lean_ctor_get(v_x_478_, 2);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v_x_478_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_tail_481_);
lean_inc(v_value_480_);
lean_inc(v_key_479_);
lean_dec(v_x_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = lean_name_eq(v_key_479_, v_a_476_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_476_, v_b_477_, v_tail_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 2, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_key_479_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_value_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v_value_480_);
lean_dec(v_key_479_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_b_477_);
lean_ctor_set(v___x_483_, 0, v_a_476_);
v___x_491_ = v___x_483_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_b_477_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_tail_481_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
return v_x_494_;
}
else
{
lean_object* v_key_496_; lean_object* v_value_497_; lean_object* v_tail_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_524_; 
v_key_496_ = lean_ctor_get(v_x_495_, 0);
v_value_497_ = lean_ctor_get(v_x_495_, 1);
v_tail_498_ = lean_ctor_get(v_x_495_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_524_ == 0)
{
v___x_500_ = v_x_495_;
v_isShared_501_ = v_isSharedCheck_524_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_tail_498_);
lean_inc(v_value_497_);
lean_inc(v_key_496_);
lean_dec(v_x_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_524_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; uint64_t v___y_504_; 
v___x_502_ = lean_array_get_size(v_x_494_);
if (lean_obj_tag(v_key_496_) == 0)
{
uint64_t v___x_522_; 
v___x_522_ = 1723ULL;
v___y_504_ = v___x_522_;
goto v___jp_503_;
}
else
{
uint64_t v_hash_523_; 
v_hash_523_ = lean_ctor_get_uint64(v_key_496_, sizeof(void*)*2);
v___y_504_ = v_hash_523_;
goto v___jp_503_;
}
v___jp_503_:
{
uint64_t v___x_505_; uint64_t v___x_506_; uint64_t v_fold_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_505_ = 32ULL;
v___x_506_ = lean_uint64_shift_right(v___y_504_, v___x_505_);
v_fold_507_ = lean_uint64_xor(v___y_504_, v___x_506_);
v___x_508_ = 16ULL;
v___x_509_ = lean_uint64_shift_right(v_fold_507_, v___x_508_);
v___x_510_ = lean_uint64_xor(v_fold_507_, v___x_509_);
v___x_511_ = lean_uint64_to_usize(v___x_510_);
v___x_512_ = lean_usize_of_nat(v___x_502_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_sub(v___x_512_, v___x_513_);
v___x_515_ = lean_usize_land(v___x_511_, v___x_514_);
v___x_516_ = lean_array_uget_borrowed(v_x_494_, v___x_515_);
lean_inc(v___x_516_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 2, v___x_516_);
v___x_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_key_496_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_value_497_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v___x_516_);
v___x_518_ = v_reuseFailAlloc_521_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_array_uset(v_x_494_, v___x_515_, v___x_518_);
v_x_494_ = v___x_519_;
v_x_495_ = v_tail_498_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_525_, lean_object* v_source_526_, lean_object* v_target_527_){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_array_get_size(v_source_526_);
v___x_529_ = lean_nat_dec_lt(v_i_525_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec_ref(v_source_526_);
lean_dec(v_i_525_);
return v_target_527_;
}
else
{
lean_object* v_es_530_; lean_object* v___x_531_; lean_object* v_source_532_; lean_object* v_target_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_es_530_ = lean_array_fget(v_source_526_, v_i_525_);
v___x_531_ = lean_box(0);
v_source_532_ = lean_array_fset(v_source_526_, v_i_525_, v___x_531_);
v_target_533_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_527_, v_es_530_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_i_525_, v___x_534_);
lean_dec(v_i_525_);
v_i_525_ = v___x_535_;
v_source_526_ = v_source_532_;
v_target_527_ = v_target_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_nbuckets_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_538_ = lean_array_get_size(v_data_537_);
v___x_539_ = lean_unsigned_to_nat(2u);
v_nbuckets_540_ = lean_nat_mul(v___x_538_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_box(0);
v___x_543_ = lean_mk_array(v_nbuckets_540_, v___x_542_);
v___x_544_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_541_, v_data_537_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(lean_object* v_m_545_, lean_object* v_a_546_, lean_object* v_b_547_){
_start:
{
lean_object* v_size_548_; lean_object* v_buckets_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_595_; 
v_size_548_ = lean_ctor_get(v_m_545_, 0);
v_buckets_549_ = lean_ctor_get(v_m_545_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_m_545_);
if (v_isSharedCheck_595_ == 0)
{
v___x_551_ = v_m_545_;
v_isShared_552_ = v_isSharedCheck_595_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_buckets_549_);
lean_inc(v_size_548_);
lean_dec(v_m_545_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_595_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; uint64_t v___y_555_; 
v___x_553_ = lean_array_get_size(v_buckets_549_);
if (lean_obj_tag(v_a_546_) == 0)
{
uint64_t v___x_593_; 
v___x_593_ = 1723ULL;
v___y_555_ = v___x_593_;
goto v___jp_554_;
}
else
{
uint64_t v_hash_594_; 
v_hash_594_ = lean_ctor_get_uint64(v_a_546_, sizeof(void*)*2);
v___y_555_ = v_hash_594_;
goto v___jp_554_;
}
v___jp_554_:
{
uint64_t v___x_556_; uint64_t v___x_557_; uint64_t v_fold_558_; uint64_t v___x_559_; uint64_t v___x_560_; uint64_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v_bkt_567_; uint8_t v___x_568_; 
v___x_556_ = 32ULL;
v___x_557_ = lean_uint64_shift_right(v___y_555_, v___x_556_);
v_fold_558_ = lean_uint64_xor(v___y_555_, v___x_557_);
v___x_559_ = 16ULL;
v___x_560_ = lean_uint64_shift_right(v_fold_558_, v___x_559_);
v___x_561_ = lean_uint64_xor(v_fold_558_, v___x_560_);
v___x_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = lean_usize_of_nat(v___x_553_);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_sub(v___x_563_, v___x_564_);
v___x_566_ = lean_usize_land(v___x_562_, v___x_565_);
v_bkt_567_ = lean_array_uget_borrowed(v_buckets_549_, v___x_566_);
v___x_568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_546_, v_bkt_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v_size_x27_570_; lean_object* v___x_571_; lean_object* v_buckets_x27_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_569_ = lean_unsigned_to_nat(1u);
v_size_x27_570_ = lean_nat_add(v_size_548_, v___x_569_);
lean_dec(v_size_548_);
lean_inc(v_bkt_567_);
v___x_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_571_, 0, v_a_546_);
lean_ctor_set(v___x_571_, 1, v_b_547_);
lean_ctor_set(v___x_571_, 2, v_bkt_567_);
v_buckets_x27_572_ = lean_array_uset(v_buckets_549_, v___x_566_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(4u);
v___x_574_ = lean_nat_mul(v_size_x27_570_, v___x_573_);
v___x_575_ = lean_unsigned_to_nat(3u);
v___x_576_ = lean_nat_div(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_array_get_size(v_buckets_x27_572_);
v___x_578_ = lean_nat_dec_le(v___x_576_, v___x_577_);
lean_dec(v___x_576_);
if (v___x_578_ == 0)
{
lean_object* v_val_579_; lean_object* v___x_581_; 
v_val_579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_572_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_val_579_);
lean_ctor_set(v___x_551_, 0, v_size_x27_570_);
v___x_581_ = v___x_551_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_size_x27_570_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_val_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v___x_584_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_buckets_x27_572_);
lean_ctor_set(v___x_551_, 0, v_size_x27_570_);
v___x_584_ = v___x_551_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_size_x27_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_buckets_x27_572_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v___x_586_; lean_object* v_buckets_x27_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
lean_inc(v_bkt_567_);
v___x_586_ = lean_box(0);
v_buckets_x27_587_ = lean_array_uset(v_buckets_549_, v___x_566_, v___x_586_);
v___x_588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_546_, v_b_547_, v_bkt_567_);
v___x_589_ = lean_array_uset(v_buckets_x27_587_, v___x_566_, v___x_588_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_589_);
v___x_591_ = v___x_551_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_size_548_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object* v_attrName_596_, lean_object* v_attrDescr_597_, lean_object* v_ref_598_){
_start:
{
lean_object* v___x_600_; 
lean_inc(v_ref_598_);
v___x_600_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_ref_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_n(v_a_601_, 2);
lean_dec_ref_known(v___x_600_, 1);
lean_inc(v_attrName_596_);
v___x_602_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_596_, v_attrDescr_597_, v_a_601_, v_ref_598_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_602_, 0);
lean_dec(v_unused_614_);
v___x_604_ = v___x_602_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_602_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_606_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
v___x_607_ = lean_st_ref_take(v___x_606_);
lean_inc(v_a_601_);
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v___x_607_, v_attrName_596_, v_a_601_);
v___x_609_ = lean_st_ref_put(v___x_606_, v___x_608_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_601_);
v___x_611_ = v___x_604_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_601_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_a_601_);
lean_dec(v_attrName_596_);
v_a_615_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_602_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_602_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_dec(v_ref_598_);
lean_dec_ref(v_attrDescr_597_);
lean_dec(v_attrName_596_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(lean_object* v_attrName_623_, lean_object* v_attrDescr_624_, lean_object* v_ref_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v_attrName_623_, v_attrDescr_624_, v_ref_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v_m_629_, v_a_630_, v_b_631_);
return v___x_632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(v_00_u03b2_637_, v_a_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec(v_a_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_642_, lean_object* v_data_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_data_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_645_, lean_object* v_a_646_, lean_object* v_b_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_646_, v_b_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_650_, lean_object* v_i_651_, lean_object* v_source_652_, lean_object* v_target_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_651_, v_source_652_, v_target_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_676_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_677_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_674_, v___x_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = l_Lean_Meta_Sym_Simp_symSimpExtension;
v___x_683_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_682_, v_a_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_684_);
lean_dec(v_a_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems(lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems(v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_694_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_Simp_symSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_Simp_symSimpExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1 = _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1);
l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1 = _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
