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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0(lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg();
return v___x_12_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__0);
v___x_14_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
v___x_15_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_13_);
lean_ctor_set(v___x_15_, 3, v___x_13_);
lean_ctor_set(v___x_15_, 4, v___x_13_);
lean_ctor_set(v___x_15_, 5, v___x_13_);
lean_ctor_set(v___x_15_, 6, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(lean_object* v_ext_16_, lean_object* v_b_17_, uint8_t v_kind_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_toCold_23_; lean_object* v_currNamespace_24_; lean_object* v___x_25_; lean_object* v_env_26_; lean_object* v_nextMacroScope_27_; lean_object* v_ngen_28_; lean_object* v_auxDeclNGen_29_; lean_object* v_traceState_30_; lean_object* v_recordedDeps_31_; lean_object* v_messages_32_; lean_object* v_infoState_33_; lean_object* v_snapshotTasks_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_61_; 
v_toCold_23_ = lean_ctor_get(v___y_20_, 0);
v_currNamespace_24_ = lean_ctor_get(v_toCold_23_, 4);
v___x_25_ = lean_st_ref_take(v___y_21_);
v_env_26_ = lean_ctor_get(v___x_25_, 0);
v_nextMacroScope_27_ = lean_ctor_get(v___x_25_, 1);
v_ngen_28_ = lean_ctor_get(v___x_25_, 2);
v_auxDeclNGen_29_ = lean_ctor_get(v___x_25_, 3);
v_traceState_30_ = lean_ctor_get(v___x_25_, 4);
v_recordedDeps_31_ = lean_ctor_get(v___x_25_, 6);
v_messages_32_ = lean_ctor_get(v___x_25_, 7);
v_infoState_33_ = lean_ctor_get(v___x_25_, 8);
v_snapshotTasks_34_ = lean_ctor_get(v___x_25_, 9);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v___x_25_, 5);
lean_dec(v_unused_62_);
v___x_36_ = v___x_25_;
v_isShared_37_ = v_isSharedCheck_61_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_snapshotTasks_34_);
lean_inc(v_infoState_33_);
lean_inc(v_messages_32_);
lean_inc(v_recordedDeps_31_);
lean_inc(v_traceState_30_);
lean_inc(v_auxDeclNGen_29_);
lean_inc(v_ngen_28_);
lean_inc(v_nextMacroScope_27_);
lean_inc(v_env_26_);
lean_dec(v___x_25_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_61_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_currNamespace_24_);
v___x_38_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_26_, v_ext_16_, v_b_17_, v_kind_18_, v_currNamespace_24_);
v___x_39_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__1);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 5, v___x_39_);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_nextMacroScope_27_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_ngen_28_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v_auxDeclNGen_29_);
lean_ctor_set(v_reuseFailAlloc_60_, 4, v_traceState_30_);
lean_ctor_set(v_reuseFailAlloc_60_, 5, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_60_, 6, v_recordedDeps_31_);
lean_ctor_set(v_reuseFailAlloc_60_, 7, v_messages_32_);
lean_ctor_set(v_reuseFailAlloc_60_, 8, v_infoState_33_);
lean_ctor_set(v_reuseFailAlloc_60_, 9, v_snapshotTasks_34_);
v___x_41_ = v_reuseFailAlloc_60_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_mctx_44_; lean_object* v_zetaDeltaFVarIds_45_; lean_object* v_postponed_46_; lean_object* v_diag_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_58_; 
v___x_42_ = lean_st_ref_put(v___y_21_, v___x_41_);
v___x_43_ = lean_st_ref_take(v___y_19_);
v_mctx_44_ = lean_ctor_get(v___x_43_, 0);
v_zetaDeltaFVarIds_45_ = lean_ctor_get(v___x_43_, 2);
v_postponed_46_ = lean_ctor_get(v___x_43_, 3);
v_diag_47_ = lean_ctor_get(v___x_43_, 4);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v___x_43_, 1);
lean_dec(v_unused_59_);
v___x_49_ = v___x_43_;
v_isShared_50_ = v_isSharedCheck_58_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_diag_47_);
lean_inc(v_postponed_46_);
lean_inc(v_zetaDeltaFVarIds_45_);
lean_inc(v_mctx_44_);
lean_dec(v___x_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_58_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 1, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_mctx_44_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v_zetaDeltaFVarIds_45_);
lean_ctor_set(v_reuseFailAlloc_57_, 3, v_postponed_46_);
lean_ctor_set(v_reuseFailAlloc_57_, 4, v_diag_47_);
v___x_54_ = v_reuseFailAlloc_57_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_st_ref_put(v___y_19_, v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_51_);
return v___x_56_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(lean_object* v_ext_63_, lean_object* v_b_64_, lean_object* v_kind_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v_kind_boxed_70_; lean_object* v_res_71_; 
v_kind_boxed_70_ = lean_unbox(v_kind_65_);
v_res_71_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_63_, v_b_64_, v_kind_boxed_70_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object* v_ext_72_, lean_object* v_declName_73_, uint8_t v_attrKind_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_73_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_82_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_82_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_72_, v_a_81_, v_attrKind_74_, v_a_76_, v_a_77_, v_a_78_);
return v___x_82_;
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v_ext_72_);
v_a_83_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_80_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object* v_ext_91_, lean_object* v_declName_92_, lean_object* v_attrKind_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
uint8_t v_attrKind_boxed_99_; lean_object* v_res_100_; 
v_attrKind_boxed_99_ = lean_unbox(v_attrKind_93_);
v_res_100_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_91_, v_declName_92_, v_attrKind_boxed_99_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_00_u03c3_103_, lean_object* v_ext_104_, lean_object* v_b_105_, uint8_t v_kind_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_104_, v_b_105_, v_kind_106_, v___y_108_, v___y_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_00_u03c3_115_, lean_object* v_ext_116_, lean_object* v_b_117_, lean_object* v_kind_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
uint8_t v_kind_boxed_124_; lean_object* v_res_125_; 
v_kind_boxed_124_ = lean_unbox(v_kind_118_);
v_res_125_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(v_00_u03b1_113_, v_00_u03b2_114_, v_00_u03c3_115_, v_ext_116_, v_b_117_, v_kind_boxed_124_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0___redArg();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0(lean_object* v_00_u03b2_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(lean_object* v_validate_134_, lean_object* v_ext_135_, uint8_t v_attrKind_136_, lean_object* v_as_137_, size_t v_sz_138_, size_t v_i_139_, lean_object* v_b_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_dec_ref(v_ext_135_);
lean_dec_ref(v_validate_134_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v_b_140_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v_a_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v_a_149_ = lean_array_uget_borrowed(v_as_137_, v_i_139_);
lean_inc_ref(v_validate_134_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v_a_149_);
v___x_150_ = lean_apply_6(v_validate_134_, v_a_149_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, lean_box(0));
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_151_; 
lean_dec_ref_known(v___x_150_, 1);
lean_inc(v_a_149_);
lean_inc_ref(v_ext_135_);
v___x_151_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_135_, v_a_149_, v_attrKind_136_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
if (lean_obj_tag(v___x_151_) == 0)
{
size_t v___x_152_; size_t v___x_153_; 
lean_dec_ref_known(v___x_151_, 1);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_add(v_i_139_, v___x_152_);
v_i_139_ = v___x_153_;
v_b_140_ = v___x_148_;
goto _start;
}
else
{
lean_dec_ref(v_ext_135_);
lean_dec_ref(v_validate_134_);
return v___x_151_;
}
}
else
{
lean_dec_ref(v_ext_135_);
lean_dec_ref(v_validate_134_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0___boxed(lean_object* v_validate_155_, lean_object* v_ext_156_, lean_object* v_attrKind_157_, lean_object* v_as_158_, lean_object* v_sz_159_, lean_object* v_i_160_, lean_object* v_b_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_attrKind_boxed_167_; size_t v_sz_boxed_168_; size_t v_i_boxed_169_; lean_object* v_res_170_; 
v_attrKind_boxed_167_ = lean_unbox(v_attrKind_157_);
v_sz_boxed_168_ = lean_unbox_usize(v_sz_159_);
lean_dec(v_sz_159_);
v_i_boxed_169_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_155_, v_ext_156_, v_attrKind_boxed_167_, v_as_158_, v_sz_boxed_168_, v_i_boxed_169_, v_b_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v_as_158_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object* v_ext_171_, lean_object* v_declName_172_, uint8_t v_attrKind_173_, lean_object* v_validate_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Sym_Simp_getSimpTheoremNames(v_declName_172_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v_thms_182_; lean_object* v_unfold_x3f_183_; lean_object* v___x_184_; size_t v_sz_185_; size_t v___x_186_; lean_object* v___x_187_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v_thms_182_ = lean_ctor_get(v_a_181_, 0);
lean_inc_ref(v_thms_182_);
v_unfold_x3f_183_ = lean_ctor_get(v_a_181_, 1);
lean_inc(v_unfold_x3f_183_);
lean_dec(v_a_181_);
v___x_184_ = lean_box(0);
v_sz_185_ = lean_array_size(v_thms_182_);
v___x_186_ = ((size_t)0ULL);
lean_inc_ref(v_ext_171_);
lean_inc_ref(v_validate_174_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_addSymSimpDecl_spec__0(v_validate_174_, v_ext_171_, v_attrKind_173_, v_thms_182_, v_sz_185_, v___x_186_, v___x_184_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec_ref(v_thms_182_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_220_; 
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v___x_187_, 0);
lean_dec(v_unused_221_);
v___x_189_ = v___x_187_;
v_isShared_190_ = v_isSharedCheck_220_;
goto v_resetjp_188_;
}
else
{
lean_dec(v___x_187_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_220_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
if (lean_obj_tag(v_unfold_x3f_183_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; 
lean_del_object(v___x_189_);
v_val_191_ = lean_ctor_get(v_unfold_x3f_183_, 0);
lean_inc_n(v_val_191_, 2);
lean_dec_ref_known(v_unfold_x3f_183_, 1);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
v___x_192_ = lean_apply_6(v_validate_174_, v_val_191_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, lean_box(0));
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; 
lean_dec_ref_known(v___x_192_, 1);
v___x_193_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_val_191_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_expr_195_; lean_object* v_pattern_196_; lean_object* v_rhs_197_; uint8_t v_perm_198_; lean_object* v_rhsVarMask_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_208_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_expr_195_ = lean_ctor_get(v_a_194_, 0);
v_pattern_196_ = lean_ctor_get(v_a_194_, 1);
v_rhs_197_ = lean_ctor_get(v_a_194_, 2);
v_perm_198_ = lean_ctor_get_uint8(v_a_194_, sizeof(void*)*4);
v_rhsVarMask_199_ = lean_ctor_get(v_a_194_, 3);
v_isSharedCheck_208_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_208_ == 0)
{
v___x_201_ = v_a_194_;
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_rhsVarMask_199_);
lean_inc(v_rhs_197_);
lean_inc(v_pattern_196_);
lean_inc(v_expr_195_);
lean_dec(v_a_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
uint8_t v___x_203_; lean_object* v___x_205_; 
v___x_203_ = 1;
if (v_isShared_202_ == 0)
{
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_expr_195_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_pattern_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_rhs_197_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_rhsVarMask_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, sizeof(void*)*4, v_perm_198_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*4 + 1, v___x_203_);
v___x_206_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_171_, v___x_205_, v_attrKind_173_, v_a_176_, v_a_177_, v_a_178_);
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_ext_171_);
v_a_209_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_193_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_193_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_dec(v_val_191_);
lean_dec_ref(v_ext_171_);
return v___x_192_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v_unfold_x3f_183_);
lean_dec_ref(v_validate_174_);
lean_dec_ref(v_ext_171_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_184_);
v___x_218_ = v___x_189_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_184_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_dec(v_unfold_x3f_183_);
lean_dec_ref(v_validate_174_);
lean_dec_ref(v_ext_171_);
return v___x_187_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_validate_174_);
lean_dec_ref(v_ext_171_);
v_a_222_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_180_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_180_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl___boxed(lean_object* v_ext_230_, lean_object* v_declName_231_, lean_object* v_attrKind_232_, lean_object* v_validate_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
uint8_t v_attrKind_boxed_239_; lean_object* v_res_240_; 
v_attrKind_boxed_239_ = lean_unbox(v_attrKind_232_);
v_res_240_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_230_, v_declName_231_, v_attrKind_boxed_239_, v_validate_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10));
v___x_268_ = l_Lean_mkAtom(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_271_ = lean_array_push(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17));
v___x_281_ = l_Lean_mkAtom(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19);
v___x_286_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16));
v___x_287_ = lean_box(2);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_285_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20);
v___x_290_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13);
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21);
v___x_293_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22);
v___x_297_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23);
v___x_300_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24);
v___x_304_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25);
v___x_307_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27);
v___x_314_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_321_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
lean_ctor_set(v___x_323_, 3, v___x_322_);
lean_ctor_set(v___x_323_, 4, v___x_321_);
lean_ctor_set(v___x_323_, 5, v___x_321_);
lean_ctor_set(v___x_323_, 6, v___x_321_);
lean_ctor_set(v___x_323_, 7, v___x_321_);
lean_ctor_set(v___x_323_, 8, v___x_321_);
lean_ctor_set(v___x_323_, 9, v___x_321_);
lean_ctor_set(v___x_323_, 10, v___x_321_);
lean_ctor_set(v___x_323_, 11, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(32u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = ((size_t)5ULL);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_unsigned_to_nat(32u);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__2);
v___x_332_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_328_);
lean_ctor_set(v___x_332_, 3, v___x_328_);
lean_ctor_set_usize(v___x_332_, 4, v___x_327_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = lean_box(1);
v___x_334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__0);
v___x_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_333_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_toCold_342_; lean_object* v_env_343_; lean_object* v_options_344_; uint8_t v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_toCold_342_ = lean_ctor_get(v___y_338_, 0);
v_env_343_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_env_343_);
lean_dec(v___x_341_);
v_options_344_ = lean_ctor_get(v_toCold_342_, 2);
v___x_345_ = 0;
v_env_346_ = l_Lean_Environment_setRecordingDeps(v_env_343_, v___x_345_);
v___x_347_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__1);
v___x_348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_344_);
v___x_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_349_, 0, v_env_346_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_348_);
lean_ctor_set(v___x_349_, 3, v_options_344_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_msgData_337_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msgData_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_ref_361_; lean_object* v___x_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
v_ref_361_ = lean_ctor_get(v___y_358_, 2);
v___x_362_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_msg_357_, v___y_358_, v___y_359_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_371_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_inc(v_ref_361_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_ref_361_);
lean_ctor_set(v___x_367_, 1, v_a_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg___boxed(lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object* v___declName_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1);
v___x_385_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v___x_384_, v___y_381_, v___y_382_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object* v___declName_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(v___declName_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___declName_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v_x_399_);
return v_res_405_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_412_; uint64_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_413_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2(void){
_start:
{
uint64_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_uint64_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__1);
v___x_415_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__0));
v___x_416_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set_uint64(v___x_416_, sizeof(void*)*1, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_box(1);
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_426_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
lean_ctor_set(v___x_428_, 3, v___x_427_);
lean_ctor_set(v___x_428_, 4, v___x_426_);
lean_ctor_set(v___x_428_, 5, v___x_426_);
lean_ctor_set(v___x_428_, 6, v___x_426_);
lean_ctor_set(v___x_428_, 7, v___x_426_);
lean_ctor_set(v___x_428_, 8, v___x_426_);
lean_ctor_set(v___x_428_, 9, v___x_426_);
lean_ctor_set(v___x_428_, 10, v___x_426_);
lean_ctor_set(v___x_428_, 11, v___x_425_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_430_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
v___x_431_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_429_);
lean_ctor_set(v___x_431_, 3, v___x_429_);
lean_ctor_set(v___x_431_, 4, v___x_429_);
lean_ctor_set(v___x_431_, 5, v___x_429_);
lean_ctor_set(v___x_431_, 6, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__3);
v___x_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_ctor_set(v___x_433_, 3, v___x_432_);
lean_ctor_set(v___x_433_, 4, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(lean_object* v___x_434_, lean_object* v_ext_435_, lean_object* v___f_436_, lean_object* v_declName_437_, lean_object* v_x_438_, uint8_t v_attrKind_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_443_ = 0;
v___x_444_ = 1;
v___x_445_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__2);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___closed__3);
v___x_448_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__4);
v___x_449_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__5));
v___x_450_ = lean_box(0);
lean_inc(v___x_434_);
v___x_451_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_451_, 0, v___x_445_);
lean_ctor_set(v___x_451_, 1, v___x_434_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
lean_ctor_set(v___x_451_, 3, v___x_449_);
lean_ctor_set(v___x_451_, 4, v___x_450_);
lean_ctor_set(v___x_451_, 5, v___x_446_);
lean_ctor_set(v___x_451_, 6, v___x_450_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*7, v___x_443_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*7 + 1, v___x_443_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*7 + 2, v___x_443_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*7 + 3, v___x_444_);
v___x_452_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__6);
v___x_453_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__7);
v___x_454_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___closed__8);
v___x_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_455_, 0, v___x_452_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_434_);
lean_ctor_set(v___x_455_, 3, v___x_447_);
lean_ctor_set(v___x_455_, 4, v___x_454_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_st_mk_ref(v___x_455_);
v___x_458_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v_ext_435_, v_declName_437_, v_attrKind_439_, v___f_436_, v___x_451_, v___x_457_, v___y_440_, v___y_441_);
lean_dec_ref_known(v___x_451_, 7);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___x_458_, 0);
lean_dec(v_unused_467_);
v___x_460_ = v___x_458_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_dec(v___x_458_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_st_ref_get(v___x_457_);
lean_dec(v___x_457_);
lean_dec(v___x_462_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_456_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_456_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_dec(v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed(lean_object* v___x_468_, lean_object* v_ext_469_, lean_object* v___f_470_, lean_object* v_declName_471_, lean_object* v_x_472_, lean_object* v_attrKind_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v_attrKind_boxed_477_; lean_object* v_res_478_; 
v_attrKind_boxed_477_ = lean_unbox(v_attrKind_473_);
v_res_478_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2(v___x_468_, v_ext_469_, v___f_470_, v_declName_471_, v_x_472_, v_attrKind_boxed_477_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v_x_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object* v_attrName_481_, lean_object* v_attrDescr_482_, lean_object* v_ext_483_, lean_object* v_ref_484_){
_start:
{
lean_object* v___f_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___f_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___f_486_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0));
v___f_487_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__1));
v___x_488_ = lean_box(1);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__2___boxed), 9, 3);
lean_closure_set(v___f_489_, 0, v___x_488_);
lean_closure_set(v___f_489_, 1, v_ext_483_);
lean_closure_set(v___f_489_, 2, v___f_487_);
v___x_490_ = 1;
v___x_491_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_491_, 0, v_ref_484_);
lean_ctor_set(v___x_491_, 1, v_attrName_481_);
lean_ctor_set(v___x_491_, 2, v_attrDescr_482_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*3, v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___f_489_);
lean_ctor_set(v___x_492_, 2, v___f_486_);
v___x_493_ = l_Lean_registerBuiltinAttribute(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object* v_attrName_494_, lean_object* v_attrDescr_495_, lean_object* v_ext_496_, lean_object* v_ref_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_494_, v_attrDescr_495_, v_ext_496_, v_ref_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object* v_00_u03b1_500_, lean_object* v_msg_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___redArg(v_msg_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object* v_00_u03b1_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(v_00_u03b1_506_, v_msg_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_512_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
uint8_t v___x_515_; 
v___x_515_ = 0;
return v___x_515_;
}
else
{
lean_object* v_key_516_; lean_object* v_tail_517_; uint8_t v___x_518_; 
v_key_516_ = lean_ctor_get(v_x_514_, 0);
v_tail_517_ = lean_ctor_get(v_x_514_, 2);
v___x_518_ = lean_name_eq(v_key_516_, v_a_513_);
if (v___x_518_ == 0)
{
v_x_514_ = v_tail_517_;
goto _start;
}
else
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec(v_a_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_dec(v_b_525_);
lean_dec(v_a_524_);
return v_x_526_;
}
else
{
lean_object* v_key_527_; lean_object* v_value_528_; lean_object* v_tail_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_541_; 
v_key_527_ = lean_ctor_get(v_x_526_, 0);
v_value_528_ = lean_ctor_get(v_x_526_, 1);
v_tail_529_ = lean_ctor_get(v_x_526_, 2);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_541_ == 0)
{
v___x_531_ = v_x_526_;
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_tail_529_);
lean_inc(v_value_528_);
lean_inc(v_key_527_);
lean_dec(v_x_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint8_t v___x_533_; 
v___x_533_ = lean_name_eq(v_key_527_, v_a_524_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_524_, v_b_525_, v_tail_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v___x_534_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_key_527_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_value_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v___x_539_; 
lean_dec(v_value_528_);
lean_dec(v_key_527_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v_b_525_);
lean_ctor_set(v___x_531_, 0, v_a_524_);
v___x_539_ = v___x_531_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_524_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_b_525_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_tail_529_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
return v_x_542_;
}
else
{
lean_object* v_key_544_; lean_object* v_value_545_; lean_object* v_tail_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_572_; 
v_key_544_ = lean_ctor_get(v_x_543_, 0);
v_value_545_ = lean_ctor_get(v_x_543_, 1);
v_tail_546_ = lean_ctor_get(v_x_543_, 2);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_572_ == 0)
{
v___x_548_ = v_x_543_;
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_tail_546_);
lean_inc(v_value_545_);
lean_inc(v_key_544_);
lean_dec(v_x_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; uint64_t v___y_552_; 
v___x_550_ = lean_array_get_size(v_x_542_);
if (lean_obj_tag(v_key_544_) == 0)
{
uint64_t v___x_570_; 
v___x_570_ = 1723ULL;
v___y_552_ = v___x_570_;
goto v___jp_551_;
}
else
{
uint64_t v_hash_571_; 
v_hash_571_ = lean_ctor_get_uint64(v_key_544_, sizeof(void*)*2);
v___y_552_ = v_hash_571_;
goto v___jp_551_;
}
v___jp_551_:
{
uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v_fold_555_; uint64_t v___x_556_; uint64_t v___x_557_; uint64_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_553_ = 32ULL;
v___x_554_ = lean_uint64_shift_right(v___y_552_, v___x_553_);
v_fold_555_ = lean_uint64_xor(v___y_552_, v___x_554_);
v___x_556_ = 16ULL;
v___x_557_ = lean_uint64_shift_right(v_fold_555_, v___x_556_);
v___x_558_ = lean_uint64_xor(v_fold_555_, v___x_557_);
v___x_559_ = lean_uint64_to_usize(v___x_558_);
v___x_560_ = lean_usize_of_nat(v___x_550_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_sub(v___x_560_, v___x_561_);
v___x_563_ = lean_usize_land(v___x_559_, v___x_562_);
v___x_564_ = lean_array_uget_borrowed(v_x_542_, v___x_563_);
lean_inc(v___x_564_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v___x_564_);
v___x_566_ = v___x_548_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_key_544_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_value_545_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v___x_564_);
v___x_566_ = v_reuseFailAlloc_569_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_array_uset(v_x_542_, v___x_563_, v___x_566_);
v_x_542_ = v___x_567_;
v_x_543_ = v_tail_546_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_573_, lean_object* v_source_574_, lean_object* v_target_575_){
_start:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_array_get_size(v_source_574_);
v___x_577_ = lean_nat_dec_lt(v_i_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_dec_ref(v_source_574_);
lean_dec(v_i_573_);
return v_target_575_;
}
else
{
lean_object* v_es_578_; lean_object* v___x_579_; lean_object* v_source_580_; lean_object* v_target_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_es_578_ = lean_array_fget(v_source_574_, v_i_573_);
v___x_579_ = lean_box(0);
v_source_580_ = lean_array_fset(v_source_574_, v_i_573_, v___x_579_);
v_target_581_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_575_, v_es_578_);
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_i_573_, v___x_582_);
lean_dec(v_i_573_);
v_i_573_ = v___x_583_;
v_source_574_ = v_source_580_;
v_target_575_ = v_target_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_nbuckets_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_586_ = lean_array_get_size(v_data_585_);
v___x_587_ = lean_unsigned_to_nat(2u);
v_nbuckets_588_ = lean_nat_mul(v___x_586_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_box(0);
v___x_591_ = lean_mk_array(v_nbuckets_588_, v___x_590_);
v___x_592_ = lean_array_propagate_mark(v_data_585_, v___x_591_);
v___x_593_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_589_, v_data_585_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(lean_object* v_m_594_, lean_object* v_a_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_size_597_; lean_object* v_buckets_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_644_; 
v_size_597_ = lean_ctor_get(v_m_594_, 0);
v_buckets_598_ = lean_ctor_get(v_m_594_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_m_594_);
if (v_isSharedCheck_644_ == 0)
{
v___x_600_ = v_m_594_;
v_isShared_601_ = v_isSharedCheck_644_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_buckets_598_);
lean_inc(v_size_597_);
lean_dec(v_m_594_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_644_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; uint64_t v___y_604_; 
v___x_602_ = lean_array_get_size(v_buckets_598_);
if (lean_obj_tag(v_a_595_) == 0)
{
uint64_t v___x_642_; 
v___x_642_ = 1723ULL;
v___y_604_ = v___x_642_;
goto v___jp_603_;
}
else
{
uint64_t v_hash_643_; 
v_hash_643_ = lean_ctor_get_uint64(v_a_595_, sizeof(void*)*2);
v___y_604_ = v_hash_643_;
goto v___jp_603_;
}
v___jp_603_:
{
uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v_fold_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_bkt_616_; uint8_t v___x_617_; 
v___x_605_ = 32ULL;
v___x_606_ = lean_uint64_shift_right(v___y_604_, v___x_605_);
v_fold_607_ = lean_uint64_xor(v___y_604_, v___x_606_);
v___x_608_ = 16ULL;
v___x_609_ = lean_uint64_shift_right(v_fold_607_, v___x_608_);
v___x_610_ = lean_uint64_xor(v_fold_607_, v___x_609_);
v___x_611_ = lean_uint64_to_usize(v___x_610_);
v___x_612_ = lean_usize_of_nat(v___x_602_);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_sub(v___x_612_, v___x_613_);
v___x_615_ = lean_usize_land(v___x_611_, v___x_614_);
v_bkt_616_ = lean_array_uget_borrowed(v_buckets_598_, v___x_615_);
v___x_617_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_595_, v_bkt_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v_size_x27_619_; lean_object* v___x_620_; lean_object* v_buckets_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v_size_x27_619_ = lean_nat_add(v_size_597_, v___x_618_);
lean_dec(v_size_597_);
lean_inc(v_bkt_616_);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v_a_595_);
lean_ctor_set(v___x_620_, 1, v_b_596_);
lean_ctor_set(v___x_620_, 2, v_bkt_616_);
v_buckets_x27_621_ = lean_array_uset(v_buckets_598_, v___x_615_, v___x_620_);
v___x_622_ = lean_unsigned_to_nat(4u);
v___x_623_ = lean_nat_mul(v_size_x27_619_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(3u);
v___x_625_ = lean_nat_div(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_array_get_size(v_buckets_x27_621_);
v___x_627_ = lean_nat_dec_le(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
if (v___x_627_ == 0)
{
lean_object* v_val_628_; lean_object* v___x_630_; 
v_val_628_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_621_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_val_628_);
lean_ctor_set(v___x_600_, 0, v_size_x27_619_);
v___x_630_ = v___x_600_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_size_x27_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_val_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v___x_633_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_buckets_x27_621_);
lean_ctor_set(v___x_600_, 0, v_size_x27_619_);
v___x_633_ = v___x_600_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_size_x27_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_buckets_x27_621_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v___x_635_; lean_object* v_buckets_x27_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
lean_inc(v_bkt_616_);
v___x_635_ = lean_box(0);
v_buckets_x27_636_ = lean_array_uset(v_buckets_598_, v___x_615_, v___x_635_);
v___x_637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_595_, v_b_596_, v_bkt_616_);
v___x_638_ = lean_array_uset(v_buckets_x27_636_, v___x_615_, v___x_637_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_638_);
v___x_640_ = v___x_600_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_597_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object* v_attrName_645_, lean_object* v_attrDescr_646_, lean_object* v_ref_647_){
_start:
{
lean_object* v___x_649_; 
lean_inc(v_ref_647_);
v___x_649_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_ref_647_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_n(v_a_650_, 2);
lean_dec_ref_known(v___x_649_, 1);
lean_inc(v_attrName_645_);
v___x_651_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_645_, v_attrDescr_646_, v_a_650_, v_ref_647_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_662_; 
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_663_);
v___x_653_ = v___x_651_;
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_651_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_655_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
v___x_656_ = lean_st_ref_take(v___x_655_);
lean_inc(v_a_650_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v___x_656_, v_attrName_645_, v_a_650_);
v___x_658_ = lean_st_ref_put(v___x_655_, v___x_657_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_a_650_);
v___x_660_ = v___x_653_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_650_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_650_);
lean_dec(v_attrName_645_);
v_a_664_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_651_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_651_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_dec(v_ref_647_);
lean_dec_ref(v_attrDescr_646_);
lean_dec(v_attrName_645_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(lean_object* v_attrName_672_, lean_object* v_attrDescr_673_, lean_object* v_ref_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v_attrName_672_, v_attrDescr_673_, v_ref_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(lean_object* v_00_u03b2_677_, lean_object* v_m_678_, lean_object* v_a_679_, lean_object* v_b_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v_m_678_, v_a_679_, v_b_680_);
return v___x_681_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_682_, lean_object* v_a_683_, lean_object* v_x_684_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_686_, lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(v_00_u03b2_686_, v_a_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec(v_a_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_691_, lean_object* v_data_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_data_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_695_, v_b_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_699_, lean_object* v_i_700_, lean_object* v_source_701_, lean_object* v_target_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_700_, v_source_701_, v_target_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_726_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = l_Lean_Meta_Sym_Simp_symSimpExtension;
v___x_732_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_731_, v_a_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_733_);
lean_dec(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems(lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems(v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_743_;
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
