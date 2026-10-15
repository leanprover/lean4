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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8;
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_toCold_15_; lean_object* v_currNamespace_16_; lean_object* v___x_17_; lean_object* v_env_18_; lean_object* v_nextMacroScope_19_; lean_object* v_ngen_20_; lean_object* v_auxDeclNGen_21_; lean_object* v_traceState_22_; lean_object* v_recordedDeps_23_; lean_object* v_messages_24_; lean_object* v_infoState_25_; lean_object* v_snapshotTasks_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_53_; 
v_toCold_15_ = lean_ctor_get(v___y_12_, 0);
v_currNamespace_16_ = lean_ctor_get(v_toCold_15_, 4);
v___x_17_ = lean_st_ref_take(v___y_13_);
v_env_18_ = lean_ctor_get(v___x_17_, 0);
v_nextMacroScope_19_ = lean_ctor_get(v___x_17_, 1);
v_ngen_20_ = lean_ctor_get(v___x_17_, 2);
v_auxDeclNGen_21_ = lean_ctor_get(v___x_17_, 3);
v_traceState_22_ = lean_ctor_get(v___x_17_, 4);
v_recordedDeps_23_ = lean_ctor_get(v___x_17_, 6);
v_messages_24_ = lean_ctor_get(v___x_17_, 7);
v_infoState_25_ = lean_ctor_get(v___x_17_, 8);
v_snapshotTasks_26_ = lean_ctor_get(v___x_17_, 9);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_17_, 5);
lean_dec(v_unused_54_);
v___x_28_ = v___x_17_;
v_isShared_29_ = v_isSharedCheck_53_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_snapshotTasks_26_);
lean_inc(v_infoState_25_);
lean_inc(v_messages_24_);
lean_inc(v_recordedDeps_23_);
lean_inc(v_traceState_22_);
lean_inc(v_auxDeclNGen_21_);
lean_inc(v_ngen_20_);
lean_inc(v_nextMacroScope_19_);
lean_inc(v_env_18_);
lean_dec(v___x_17_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_53_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
lean_inc(v_currNamespace_16_);
v___x_30_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_18_, v_ext_8_, v_b_9_, v_kind_10_, v_currNamespace_16_);
v___x_31_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 5, v___x_31_);
lean_ctor_set(v___x_28_, 0, v___x_30_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_nextMacroScope_19_);
lean_ctor_set(v_reuseFailAlloc_52_, 2, v_ngen_20_);
lean_ctor_set(v_reuseFailAlloc_52_, 3, v_auxDeclNGen_21_);
lean_ctor_set(v_reuseFailAlloc_52_, 4, v_traceState_22_);
lean_ctor_set(v_reuseFailAlloc_52_, 5, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_52_, 6, v_recordedDeps_23_);
lean_ctor_set(v_reuseFailAlloc_52_, 7, v_messages_24_);
lean_ctor_set(v_reuseFailAlloc_52_, 8, v_infoState_25_);
lean_ctor_set(v_reuseFailAlloc_52_, 9, v_snapshotTasks_26_);
v___x_33_ = v_reuseFailAlloc_52_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_mctx_36_; lean_object* v_zetaDeltaFVarIds_37_; lean_object* v_postponed_38_; lean_object* v_diag_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_50_; 
v___x_34_ = lean_st_ref_put(v___y_13_, v___x_33_);
v___x_35_ = lean_st_ref_take(v___y_11_);
v_mctx_36_ = lean_ctor_get(v___x_35_, 0);
v_zetaDeltaFVarIds_37_ = lean_ctor_get(v___x_35_, 2);
v_postponed_38_ = lean_ctor_get(v___x_35_, 3);
v_diag_39_ = lean_ctor_get(v___x_35_, 4);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v___x_35_, 1);
lean_dec(v_unused_51_);
v___x_41_ = v___x_35_;
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_diag_39_);
lean_inc(v_postponed_38_);
lean_inc(v_zetaDeltaFVarIds_37_);
lean_inc(v_mctx_36_);
lean_dec(v___x_35_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_44_);
v___x_46_ = v___x_41_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_mctx_36_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_zetaDeltaFVarIds_37_);
lean_ctor_set(v_reuseFailAlloc_49_, 3, v_postponed_38_);
lean_ctor_set(v_reuseFailAlloc_49_, 4, v_diag_39_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_st_ref_put(v___y_11_, v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_43_);
return v___x_48_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(lean_object* v_ext_55_, lean_object* v_b_56_, lean_object* v_kind_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
uint8_t v_kind_boxed_62_; lean_object* v_res_63_; 
v_kind_boxed_62_ = lean_unbox(v_kind_57_);
v_res_63_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_55_, v_b_56_, v_kind_boxed_62_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_00_u03c3_66_, lean_object* v_ext_67_, lean_object* v_b_68_, uint8_t v_kind_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_67_, v_b_68_, v_kind_69_, v___y_71_, v___y_72_, v___y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_00_u03c3_78_, lean_object* v_ext_79_, lean_object* v_b_80_, lean_object* v_kind_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_kind_boxed_87_; lean_object* v_res_88_; 
v_kind_boxed_87_ = lean_unbox(v_kind_81_);
v_res_88_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(v_00_u03b1_76_, v_00_u03b2_77_, v_00_u03c3_78_, v_ext_79_, v_b_80_, v_kind_boxed_87_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object* v_ext_89_, lean_object* v_declName_90_, uint8_t v_attrKind_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_90_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_89_, v_a_98_, v_attrKind_91_, v_a_93_, v_a_94_, v_a_95_);
return v___x_99_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_ext_89_);
v_a_100_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_97_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object* v_ext_108_, lean_object* v_declName_109_, lean_object* v_attrKind_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
uint8_t v_attrKind_boxed_116_; lean_object* v_res_117_; 
v_attrKind_boxed_116_ = lean_unbox(v_attrKind_110_);
v_res_117_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_108_, v_declName_109_, v_attrKind_boxed_116_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(lean_object* v_validate_118_, lean_object* v_ext_119_, uint8_t v_attrKind_120_, lean_object* v_as_121_, size_t v_sz_122_, size_t v_i_123_, lean_object* v_b_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = lean_usize_dec_lt(v_i_123_, v_sz_122_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v_ext_119_);
lean_dec_ref(v_validate_118_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_b_124_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v_a_133_; lean_object* v___x_134_; 
v___x_132_ = lean_box(0);
v_a_133_ = lean_array_uget_borrowed(v_as_121_, v_i_123_);
lean_inc_ref(v_validate_118_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
lean_inc(v_a_133_);
v___x_134_ = lean_apply_6(v_validate_118_, v_a_133_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v___x_135_; 
lean_dec_ref_known(v___x_134_, 1);
lean_inc(v_a_133_);
lean_inc_ref(v_ext_119_);
v___x_135_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_119_, v_a_133_, v_attrKind_120_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
if (lean_obj_tag(v___x_135_) == 0)
{
size_t v___x_136_; size_t v___x_137_; 
lean_dec_ref_known(v___x_135_, 1);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_add(v_i_123_, v___x_136_);
v_i_123_ = v___x_137_;
v_b_124_ = v___x_132_;
goto _start;
}
else
{
lean_dec_ref(v_ext_119_);
lean_dec_ref(v_validate_118_);
return v___x_135_;
}
}
else
{
lean_dec_ref(v_ext_119_);
lean_dec_ref(v_validate_118_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0___boxed(lean_object* v_validate_139_, lean_object* v_ext_140_, lean_object* v_attrKind_141_, lean_object* v_as_142_, lean_object* v_sz_143_, lean_object* v_i_144_, lean_object* v_b_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v_attrKind_boxed_151_; size_t v_sz_boxed_152_; size_t v_i_boxed_153_; lean_object* v_res_154_; 
v_attrKind_boxed_151_ = lean_unbox(v_attrKind_141_);
v_sz_boxed_152_ = lean_unbox_usize(v_sz_143_);
lean_dec(v_sz_143_);
v_i_boxed_153_ = lean_unbox_usize(v_i_144_);
lean_dec(v_i_144_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_139_, v_ext_140_, v_attrKind_boxed_151_, v_as_142_, v_sz_boxed_152_, v_i_boxed_153_, v_b_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec_ref(v_as_142_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object* v_ext_155_, lean_object* v_declName_156_, uint8_t v_attrKind_157_, lean_object* v_validate_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Sym_Simp_getSimpTheoremNames(v_declName_156_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v_thms_166_; lean_object* v_unfold_x3f_167_; lean_object* v___x_168_; size_t v_sz_169_; size_t v___x_170_; lean_object* v___x_171_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v_thms_166_ = lean_ctor_get(v_a_165_, 0);
lean_inc_ref(v_thms_166_);
v_unfold_x3f_167_ = lean_ctor_get(v_a_165_, 1);
lean_inc(v_unfold_x3f_167_);
lean_dec(v_a_165_);
v___x_168_ = lean_box(0);
v_sz_169_ = lean_array_size(v_thms_166_);
v___x_170_ = ((size_t)0ULL);
lean_inc_ref(v_ext_155_);
lean_inc_ref(v_validate_158_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_158_, v_ext_155_, v_attrKind_157_, v_thms_166_, v_sz_169_, v___x_170_, v___x_168_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec_ref(v_thms_166_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_204_; 
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v___x_171_, 0);
lean_dec(v_unused_205_);
v___x_173_ = v___x_171_;
v_isShared_174_ = v_isSharedCheck_204_;
goto v_resetjp_172_;
}
else
{
lean_dec(v___x_171_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_204_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
if (lean_obj_tag(v_unfold_x3f_167_) == 1)
{
lean_object* v_val_175_; lean_object* v___x_176_; 
lean_del_object(v___x_173_);
v_val_175_ = lean_ctor_get(v_unfold_x3f_167_, 0);
lean_inc_n(v_val_175_, 2);
lean_dec_ref_known(v_unfold_x3f_167_, 1);
lean_inc(v_a_162_);
lean_inc_ref(v_a_161_);
lean_inc(v_a_160_);
lean_inc_ref(v_a_159_);
v___x_176_ = lean_apply_6(v_validate_158_, v_val_175_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, lean_box(0));
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; 
lean_dec_ref_known(v___x_176_, 1);
v___x_177_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_val_175_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_expr_179_; lean_object* v_pattern_180_; lean_object* v_rhs_181_; uint8_t v_perm_182_; lean_object* v_rhsVarMask_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_192_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_expr_179_ = lean_ctor_get(v_a_178_, 0);
v_pattern_180_ = lean_ctor_get(v_a_178_, 1);
v_rhs_181_ = lean_ctor_get(v_a_178_, 2);
v_perm_182_ = lean_ctor_get_uint8(v_a_178_, sizeof(void*)*4);
v_rhsVarMask_183_ = lean_ctor_get(v_a_178_, 3);
v_isSharedCheck_192_ = !lean_is_exclusive(v_a_178_);
if (v_isSharedCheck_192_ == 0)
{
v___x_185_ = v_a_178_;
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_rhsVarMask_183_);
lean_inc(v_rhs_181_);
lean_inc(v_pattern_180_);
lean_inc(v_expr_179_);
lean_dec(v_a_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; lean_object* v___x_189_; 
v___x_187_ = 1;
if (v_isShared_186_ == 0)
{
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_expr_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_pattern_180_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_rhs_181_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_rhsVarMask_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_191_, sizeof(void*)*4, v_perm_182_);
v___x_189_ = v_reuseFailAlloc_191_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; 
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*4 + 1, v___x_187_);
v___x_190_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_155_, v___x_189_, v_attrKind_157_, v_a_160_, v_a_161_, v_a_162_);
return v___x_190_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_ext_155_);
v_a_193_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_177_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_177_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_dec(v_val_175_);
lean_dec_ref(v_ext_155_);
return v___x_176_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec(v_unfold_x3f_167_);
lean_dec_ref(v_validate_158_);
lean_dec_ref(v_ext_155_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_168_);
v___x_202_ = v___x_173_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_168_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_dec(v_unfold_x3f_167_);
lean_dec_ref(v_validate_158_);
lean_dec_ref(v_ext_155_);
return v___x_171_;
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v_validate_158_);
lean_dec_ref(v_ext_155_);
v_a_206_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_164_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_164_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl___boxed(lean_object* v_ext_214_, lean_object* v_declName_215_, lean_object* v_attrKind_216_, lean_object* v_validate_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_attrKind_boxed_223_; lean_object* v_res_224_; 
v_attrKind_boxed_223_ = lean_unbox(v_attrKind_216_);
v_res_224_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_214_, v_declName_215_, v_attrKind_boxed_223_, v_validate_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_224_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10));
v___x_252_ = l_Lean_mkAtom(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12);
v___x_254_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_255_ = lean_array_push(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17));
v___x_265_ = l_Lean_mkAtom(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_268_ = lean_array_push(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16));
v___x_271_ = lean_box(2);
v___x_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_269_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20);
v___x_274_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13);
v___x_275_ = lean_array_push(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21);
v___x_277_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11));
v___x_278_ = lean_box(2);
v___x_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
lean_ctor_set(v___x_279_, 2, v___x_276_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_282_ = lean_array_push(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23);
v___x_284_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9));
v___x_285_ = lean_box(2);
v___x_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
lean_ctor_set(v___x_286_, 2, v___x_283_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25);
v___x_291_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7));
v___x_292_ = lean_box(2);
v___x_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
lean_ctor_set(v___x_293_, 2, v___x_290_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26);
v___x_295_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_296_ = lean_array_push(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27);
v___x_298_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4));
v___x_299_ = lean_box(2);
v___x_300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_305_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_ctor_set(v___x_307_, 2, v___x_306_);
lean_ctor_set(v___x_307_, 3, v___x_306_);
lean_ctor_set(v___x_307_, 4, v___x_305_);
lean_ctor_set(v___x_307_, 5, v___x_305_);
lean_ctor_set(v___x_307_, 6, v___x_305_);
lean_ctor_set(v___x_307_, 7, v___x_305_);
lean_ctor_set(v___x_307_, 8, v___x_305_);
lean_ctor_set(v___x_307_, 9, v___x_305_);
lean_ctor_set(v___x_307_, 10, v___x_305_);
lean_ctor_set(v___x_307_, 11, v___x_304_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(32u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_311_ = ((size_t)5ULL);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_unsigned_to_nat(32u);
v___x_314_ = lean_mk_empty_array_with_capacity(v___x_313_);
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2);
v___x_316_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_312_);
lean_ctor_set(v___x_316_, 3, v___x_312_);
lean_ctor_set_usize(v___x_316_, 4, v___x_311_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_box(1);
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_319_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0);
v___x_320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_toCold_326_; lean_object* v_env_327_; lean_object* v_options_328_; uint8_t v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_toCold_326_ = lean_ctor_get(v___y_322_, 0);
v_env_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_325_);
v_options_328_ = lean_ctor_get(v_toCold_326_, 2);
v___x_329_ = 0;
v_env_330_ = l_Lean_Environment_setRecordingDeps(v_env_327_, v___x_329_);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1);
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_328_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_env_330_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
lean_ctor_set(v___x_333_, 3, v_options_328_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_msgData_321_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msgData_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_ref_345_; lean_object* v___x_346_; lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_ref_345_ = lean_ctor_get(v___y_342_, 2);
v___x_346_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msg_341_, v___y_342_, v___y_343_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_inc(v_ref_345_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_ref_345_);
lean_ctor_set(v___x_351_, 1, v_a_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 1);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg___boxed(lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_360_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object* v___declName_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1);
v___x_369_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v___x_368_, v___y_365_, v___y_366_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object* v___declName_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(v___declName_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___declName_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(v_x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v_x_383_);
return v_res_389_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_396_; uint64_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_397_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2(void){
_start:
{
uint64_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_uint64_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1);
v___x_399_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set_uint64(v___x_400_, sizeof(void*)*1, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_box(1);
v___x_404_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_405_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_403_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_410_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_411_);
lean_ctor_set(v___x_412_, 3, v___x_411_);
lean_ctor_set(v___x_412_, 4, v___x_410_);
lean_ctor_set(v___x_412_, 5, v___x_410_);
lean_ctor_set(v___x_412_, 6, v___x_410_);
lean_ctor_set(v___x_412_, 7, v___x_410_);
lean_ctor_set(v___x_412_, 8, v___x_410_);
lean_ctor_set(v___x_412_, 9, v___x_410_);
lean_ctor_set(v___x_412_, 10, v___x_410_);
lean_ctor_set(v___x_412_, 11, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_414_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
lean_ctor_set(v___x_414_, 3, v___x_413_);
lean_ctor_set(v___x_414_, 4, v___x_413_);
lean_ctor_set(v___x_414_, 5, v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
lean_ctor_set(v___x_416_, 2, v___x_415_);
lean_ctor_set(v___x_416_, 3, v___x_415_);
lean_ctor_set(v___x_416_, 4, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(lean_object* v___x_417_, lean_object* v_ext_418_, lean_object* v___f_419_, lean_object* v_declName_420_, lean_object* v_x_421_, uint8_t v_attrKind_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_426_ = 0;
v___x_427_ = 1;
v___x_428_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_431_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_432_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5));
v___x_433_ = lean_box(0);
lean_inc(v___x_417_);
v___x_434_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_417_);
lean_ctor_set(v___x_434_, 2, v___x_431_);
lean_ctor_set(v___x_434_, 3, v___x_432_);
lean_ctor_set(v___x_434_, 4, v___x_433_);
lean_ctor_set(v___x_434_, 5, v___x_429_);
lean_ctor_set(v___x_434_, 6, v___x_433_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*7, v___x_426_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*7 + 1, v___x_426_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*7 + 2, v___x_426_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*7 + 3, v___x_427_);
v___x_435_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6);
v___x_436_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7);
v___x_437_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8);
v___x_438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_438_, 0, v___x_435_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
lean_ctor_set(v___x_438_, 2, v___x_417_);
lean_ctor_set(v___x_438_, 3, v___x_430_);
lean_ctor_set(v___x_438_, 4, v___x_437_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_st_mk_ref(v___x_438_);
v___x_441_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_418_, v_declName_420_, v_attrKind_422_, v___f_419_, v___x_434_, v___x_440_, v___y_423_, v___y_424_);
lean_dec_ref_known(v___x_434_, 7);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_450_);
v___x_443_ = v___x_441_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_441_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_st_ref_get(v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___x_445_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_439_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_439_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_dec(v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed(lean_object* v___x_451_, lean_object* v_ext_452_, lean_object* v___f_453_, lean_object* v_declName_454_, lean_object* v_x_455_, lean_object* v_attrKind_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v_attrKind_boxed_460_; lean_object* v_res_461_; 
v_attrKind_boxed_460_ = lean_unbox(v_attrKind_456_);
v_res_461_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(v___x_451_, v_ext_452_, v___f_453_, v_declName_454_, v_x_455_, v_attrKind_boxed_460_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_x_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object* v_attrName_464_, lean_object* v_attrDescr_465_, lean_object* v_ext_466_, lean_object* v_ref_467_){
_start:
{
lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___f_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___f_469_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0));
v___f_470_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1));
v___x_471_ = lean_box(1);
v___f_472_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed), 9, 3);
lean_closure_set(v___f_472_, 0, v___x_471_);
lean_closure_set(v___f_472_, 1, v_ext_466_);
lean_closure_set(v___f_472_, 2, v___f_470_);
v___x_473_ = 1;
v___x_474_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_474_, 0, v_ref_467_);
lean_ctor_set(v___x_474_, 1, v_attrName_464_);
lean_ctor_set(v___x_474_, 2, v_attrDescr_465_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*3, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___f_472_);
lean_ctor_set(v___x_475_, 2, v___f_469_);
v___x_476_ = l_Lean_registerBuiltinAttribute(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object* v_attrName_477_, lean_object* v_attrDescr_478_, lean_object* v_ext_479_, lean_object* v_ref_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_477_, v_attrDescr_478_, v_ext_479_, v_ref_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object* v_00_u03b1_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_484_, v___y_485_, v___y_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object* v_00_u03b1_489_, lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(v_00_u03b1_489_, v_msg_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_494_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_495_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
uint8_t v___x_498_; 
v___x_498_ = 0;
return v___x_498_;
}
else
{
lean_object* v_key_499_; lean_object* v_tail_500_; uint8_t v___x_501_; 
v_key_499_ = lean_ctor_get(v_x_497_, 0);
v_tail_500_ = lean_ctor_get(v_x_497_, 2);
v___x_501_ = lean_name_eq(v_key_499_, v_a_496_);
if (v___x_501_ == 0)
{
v_x_497_ = v_tail_500_;
goto _start;
}
else
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec(v_a_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_dec(v_b_508_);
lean_dec(v_a_507_);
return v_x_509_;
}
else
{
lean_object* v_key_510_; lean_object* v_value_511_; lean_object* v_tail_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_key_510_ = lean_ctor_get(v_x_509_, 0);
v_value_511_ = lean_ctor_get(v_x_509_, 1);
v_tail_512_ = lean_ctor_get(v_x_509_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_524_ == 0)
{
v___x_514_ = v_x_509_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tail_512_);
lean_inc(v_value_511_);
lean_inc(v_key_510_);
lean_dec(v_x_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_name_eq(v_key_510_, v_a_507_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_507_, v_b_508_, v_tail_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 2, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_key_510_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_value_511_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v___x_522_; 
lean_dec(v_value_511_);
lean_dec(v_key_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v_b_508_);
lean_ctor_set(v___x_514_, 0, v_a_507_);
v___x_522_ = v___x_514_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_507_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_b_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_tail_512_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
return v_x_525_;
}
else
{
lean_object* v_key_527_; lean_object* v_value_528_; lean_object* v_tail_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_555_; 
v_key_527_ = lean_ctor_get(v_x_526_, 0);
v_value_528_ = lean_ctor_get(v_x_526_, 1);
v_tail_529_ = lean_ctor_get(v_x_526_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_555_ == 0)
{
v___x_531_ = v_x_526_;
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_tail_529_);
lean_inc(v_value_528_);
lean_inc(v_key_527_);
lean_dec(v_x_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; uint64_t v___y_535_; 
v___x_533_ = lean_array_get_size(v_x_525_);
if (lean_obj_tag(v_key_527_) == 0)
{
uint64_t v___x_553_; 
v___x_553_ = 1723ULL;
v___y_535_ = v___x_553_;
goto v___jp_534_;
}
else
{
uint64_t v_hash_554_; 
v_hash_554_ = lean_ctor_get_uint64(v_key_527_, sizeof(void*)*2);
v___y_535_ = v_hash_554_;
goto v___jp_534_;
}
v___jp_534_:
{
uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v_fold_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_536_ = 32ULL;
v___x_537_ = lean_uint64_shift_right(v___y_535_, v___x_536_);
v_fold_538_ = lean_uint64_xor(v___y_535_, v___x_537_);
v___x_539_ = 16ULL;
v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
v___x_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = lean_usize_of_nat(v___x_533_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
v___x_547_ = lean_array_uget_borrowed(v_x_525_, v___x_546_);
lean_inc(v___x_547_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v___x_547_);
v___x_549_ = v___x_531_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_key_527_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_value_528_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_array_uset(v_x_525_, v___x_546_, v___x_549_);
v_x_525_ = v___x_550_;
v_x_526_ = v_tail_529_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_556_, lean_object* v_source_557_, lean_object* v_target_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_source_557_);
v___x_560_ = lean_nat_dec_lt(v_i_556_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec_ref(v_source_557_);
lean_dec(v_i_556_);
return v_target_558_;
}
else
{
lean_object* v_es_561_; lean_object* v___x_562_; lean_object* v_source_563_; lean_object* v_target_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_es_561_ = lean_array_fget(v_source_557_, v_i_556_);
v___x_562_ = lean_box(0);
v_source_563_ = lean_array_fset(v_source_557_, v_i_556_, v___x_562_);
v_target_564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_558_, v_es_561_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_i_556_, v___x_565_);
lean_dec(v_i_556_);
v_i_556_ = v___x_566_;
v_source_557_ = v_source_563_;
v_target_558_ = v_target_564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_nbuckets_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_569_ = lean_array_get_size(v_data_568_);
v___x_570_ = lean_unsigned_to_nat(2u);
v_nbuckets_571_ = lean_nat_mul(v___x_569_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_box(0);
v___x_574_ = lean_mk_array(v_nbuckets_571_, v___x_573_);
v___x_575_ = lean_array_propagate_mark(v_data_568_, v___x_574_);
v___x_576_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_572_, v_data_568_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(lean_object* v_m_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_size_580_; lean_object* v_buckets_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_627_; 
v_size_580_ = lean_ctor_get(v_m_577_, 0);
v_buckets_581_ = lean_ctor_get(v_m_577_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_m_577_);
if (v_isSharedCheck_627_ == 0)
{
v___x_583_ = v_m_577_;
v_isShared_584_ = v_isSharedCheck_627_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_buckets_581_);
lean_inc(v_size_580_);
lean_dec(v_m_577_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_627_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; uint64_t v___y_587_; 
v___x_585_ = lean_array_get_size(v_buckets_581_);
if (lean_obj_tag(v_a_578_) == 0)
{
uint64_t v___x_625_; 
v___x_625_ = 1723ULL;
v___y_587_ = v___x_625_;
goto v___jp_586_;
}
else
{
uint64_t v_hash_626_; 
v_hash_626_ = lean_ctor_get_uint64(v_a_578_, sizeof(void*)*2);
v___y_587_ = v_hash_626_;
goto v___jp_586_;
}
v___jp_586_:
{
uint64_t v___x_588_; uint64_t v___x_589_; uint64_t v_fold_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_bkt_599_; uint8_t v___x_600_; 
v___x_588_ = 32ULL;
v___x_589_ = lean_uint64_shift_right(v___y_587_, v___x_588_);
v_fold_590_ = lean_uint64_xor(v___y_587_, v___x_589_);
v___x_591_ = 16ULL;
v___x_592_ = lean_uint64_shift_right(v_fold_590_, v___x_591_);
v___x_593_ = lean_uint64_xor(v_fold_590_, v___x_592_);
v___x_594_ = lean_uint64_to_usize(v___x_593_);
v___x_595_ = lean_usize_of_nat(v___x_585_);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_sub(v___x_595_, v___x_596_);
v___x_598_ = lean_usize_land(v___x_594_, v___x_597_);
v_bkt_599_ = lean_array_uget_borrowed(v_buckets_581_, v___x_598_);
v___x_600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_578_, v_bkt_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_size_x27_602_; lean_object* v___x_603_; lean_object* v_buckets_x27_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v_size_x27_602_ = lean_nat_add(v_size_580_, v___x_601_);
lean_dec(v_size_580_);
lean_inc(v_bkt_599_);
v___x_603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_603_, 0, v_a_578_);
lean_ctor_set(v___x_603_, 1, v_b_579_);
lean_ctor_set(v___x_603_, 2, v_bkt_599_);
v_buckets_x27_604_ = lean_array_uset(v_buckets_581_, v___x_598_, v___x_603_);
v___x_605_ = lean_unsigned_to_nat(4u);
v___x_606_ = lean_nat_mul(v_size_x27_602_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(3u);
v___x_608_ = lean_nat_div(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_array_get_size(v_buckets_x27_604_);
v___x_610_ = lean_nat_dec_le(v___x_608_, v___x_609_);
lean_dec(v___x_608_);
if (v___x_610_ == 0)
{
lean_object* v_val_611_; lean_object* v___x_613_; 
v_val_611_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_604_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_val_611_);
lean_ctor_set(v___x_583_, 0, v_size_x27_602_);
v___x_613_ = v___x_583_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_size_x27_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_val_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
else
{
lean_object* v___x_616_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_buckets_x27_604_);
lean_ctor_set(v___x_583_, 0, v_size_x27_602_);
v___x_616_ = v___x_583_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_size_x27_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_buckets_x27_604_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v___x_618_; lean_object* v_buckets_x27_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_inc(v_bkt_599_);
v___x_618_ = lean_box(0);
v_buckets_x27_619_ = lean_array_uset(v_buckets_581_, v___x_598_, v___x_618_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_578_, v_b_579_, v_bkt_599_);
v___x_621_ = lean_array_uset(v_buckets_x27_619_, v___x_598_, v___x_620_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v___x_621_);
v___x_623_ = v___x_583_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_size_580_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object* v_attrName_628_, lean_object* v_attrDescr_629_, lean_object* v_ref_630_){
_start:
{
lean_object* v___x_632_; 
lean_inc(v_ref_630_);
v___x_632_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_ref_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_n(v_a_633_, 2);
lean_dec_ref_known(v___x_632_, 1);
lean_inc(v_attrName_628_);
v___x_634_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_628_, v_attrDescr_629_, v_a_633_, v_ref_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_646_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_638_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
v___x_639_ = lean_st_ref_take(v___x_638_);
lean_inc(v_a_633_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v___x_639_, v_attrName_628_, v_a_633_);
v___x_641_ = lean_st_ref_put(v___x_638_, v___x_640_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_a_633_);
v___x_643_ = v___x_636_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_633_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_633_);
lean_dec(v_attrName_628_);
v_a_647_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_634_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_634_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec(v_ref_630_);
lean_dec_ref(v_attrDescr_629_);
lean_dec(v_attrName_628_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(lean_object* v_attrName_655_, lean_object* v_attrDescr_656_, lean_object* v_ref_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v_attrName_655_, v_attrDescr_656_, v_ref_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(lean_object* v_00_u03b2_660_, lean_object* v_m_661_, lean_object* v_a_662_, lean_object* v_b_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v_m_661_, v_a_662_, v_b_663_);
return v___x_664_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_665_, lean_object* v_a_666_, lean_object* v_x_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_669_, lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(v_00_u03b2_669_, v_a_670_, v_x_671_);
lean_dec(v_x_671_);
lean_dec(v_a_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_674_, lean_object* v_data_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_data_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_678_, v_b_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_682_, lean_object* v_i_683_, lean_object* v_source_684_, lean_object* v_target_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_683_, v_source_684_, v_target_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_709_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Lean_Meta_Sym_Simp_symSimpExtension;
v___x_715_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_714_, v_a_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_716_);
lean_dec(v_a_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems(lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems(v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_726_;
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
