// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Attr
// Imports: public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Tactic.Simp.SimpTheorems import Lean.Meta.Eqns
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_ignoreEquations(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Erasing `Sym.simp` attributes is not supported yet."};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5;
static const lean_array_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Cannot add `"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` attribute to `"};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`: No equation theorems found."};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "`: It is a reducible definition or projection. `Sym.simp` does not support unfolding."};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17;
static const lean_string_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`: It is not a proposition nor a definition with equation theorems."};
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
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
lean_object* v_currNamespace_15_; lean_object* v___x_16_; lean_object* v_env_17_; lean_object* v_nextMacroScope_18_; lean_object* v_ngen_19_; lean_object* v_auxDeclNGen_20_; lean_object* v_traceState_21_; lean_object* v_messages_22_; lean_object* v_infoState_23_; lean_object* v_snapshotTasks_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_51_; 
v_currNamespace_15_ = lean_ctor_get(v___y_12_, 6);
v___x_16_ = lean_st_ref_take(v___y_13_);
v_env_17_ = lean_ctor_get(v___x_16_, 0);
v_nextMacroScope_18_ = lean_ctor_get(v___x_16_, 1);
v_ngen_19_ = lean_ctor_get(v___x_16_, 2);
v_auxDeclNGen_20_ = lean_ctor_get(v___x_16_, 3);
v_traceState_21_ = lean_ctor_get(v___x_16_, 4);
v_messages_22_ = lean_ctor_get(v___x_16_, 6);
v_infoState_23_ = lean_ctor_get(v___x_16_, 7);
v_snapshotTasks_24_ = lean_ctor_get(v___x_16_, 8);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_51_ == 0)
{
lean_object* v_unused_52_; 
v_unused_52_ = lean_ctor_get(v___x_16_, 5);
lean_dec(v_unused_52_);
v___x_26_ = v___x_16_;
v_isShared_27_ = v_isSharedCheck_51_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_snapshotTasks_24_);
lean_inc(v_infoState_23_);
lean_inc(v_messages_22_);
lean_inc(v_traceState_21_);
lean_inc(v_auxDeclNGen_20_);
lean_inc(v_ngen_19_);
lean_inc(v_nextMacroScope_18_);
lean_inc(v_env_17_);
lean_dec(v___x_16_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_51_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
lean_inc(v_currNamespace_15_);
v___x_28_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_17_, v_ext_8_, v_b_9_, v_kind_10_, v_currNamespace_15_);
v___x_29_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__2);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 5, v___x_29_);
lean_ctor_set(v___x_26_, 0, v___x_28_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_nextMacroScope_18_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v_ngen_19_);
lean_ctor_set(v_reuseFailAlloc_50_, 3, v_auxDeclNGen_20_);
lean_ctor_set(v_reuseFailAlloc_50_, 4, v_traceState_21_);
lean_ctor_set(v_reuseFailAlloc_50_, 5, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_50_, 6, v_messages_22_);
lean_ctor_set(v_reuseFailAlloc_50_, 7, v_infoState_23_);
lean_ctor_set(v_reuseFailAlloc_50_, 8, v_snapshotTasks_24_);
v___x_31_ = v_reuseFailAlloc_50_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_mctx_34_; lean_object* v_zetaDeltaFVarIds_35_; lean_object* v_postponed_36_; lean_object* v_diag_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_48_; 
v___x_32_ = lean_st_ref_set(v___y_13_, v___x_31_);
v___x_33_ = lean_st_ref_take(v___y_11_);
v_mctx_34_ = lean_ctor_get(v___x_33_, 0);
v_zetaDeltaFVarIds_35_ = lean_ctor_get(v___x_33_, 2);
v_postponed_36_ = lean_ctor_get(v___x_33_, 3);
v_diag_37_ = lean_ctor_get(v___x_33_, 4);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v___x_33_, 1);
lean_dec(v_unused_49_);
v___x_39_ = v___x_33_;
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_diag_37_);
lean_inc(v_postponed_36_);
lean_inc(v_zetaDeltaFVarIds_35_);
lean_inc(v_mctx_34_);
lean_dec(v___x_33_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___closed__3);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 1, v___x_41_);
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_mctx_34_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v_zetaDeltaFVarIds_35_);
lean_ctor_set(v_reuseFailAlloc_47_, 3, v_postponed_36_);
lean_ctor_set(v_reuseFailAlloc_47_, 4, v_diag_37_);
v___x_43_ = v_reuseFailAlloc_47_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_st_ref_set(v___y_11_, v___x_43_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg___boxed(lean_object* v_ext_53_, lean_object* v_b_54_, lean_object* v_kind_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
uint8_t v_kind_boxed_60_; lean_object* v_res_61_; 
v_kind_boxed_60_ = lean_unbox(v_kind_55_);
v_res_61_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_53_, v_b_54_, v_kind_boxed_60_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_00_u03c3_64_, lean_object* v_ext_65_, lean_object* v_b_66_, uint8_t v_kind_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_65_, v_b_66_, v_kind_67_, v___y_69_, v___y_70_, v___y_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___boxed(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_00_u03c3_76_, lean_object* v_ext_77_, lean_object* v_b_78_, lean_object* v_kind_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_kind_boxed_85_; lean_object* v_res_86_; 
v_kind_boxed_85_ = lean_unbox(v_kind_79_);
v_res_86_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0(v_00_u03b1_74_, v_00_u03b2_75_, v_00_u03c3_76_, v_ext_77_, v_b_78_, v_kind_boxed_85_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem(lean_object* v_ext_87_, lean_object* v_declName_88_, uint8_t v_attrKind_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_88_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref(v___x_95_);
v___x_97_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Sym_Simp_addSymSimpTheorem_spec__0___redArg(v_ext_87_, v_a_96_, v_attrKind_89_, v_a_91_, v_a_92_, v_a_93_);
return v___x_97_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_ext_87_);
v_a_98_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_95_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_95_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_addSymSimpTheorem___boxed(lean_object* v_ext_106_, lean_object* v_declName_107_, lean_object* v_attrKind_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
uint8_t v_attrKind_boxed_114_; lean_object* v_res_115_; 
v_attrKind_boxed_114_ = lean_unbox(v_attrKind_108_);
v_res_115_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_106_, v_declName_107_, v_attrKind_boxed_114_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
return v_res_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__10));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__12);
v___x_145_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__17));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__18);
v___x_158_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__19);
v___x_161_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__16));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__13);
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__21);
v___x_168_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__11));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__22);
v___x_172_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__23);
v___x_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__9));
v___x_176_ = lean_box(2);
v___x_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__24);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__25);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__7));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__26);
v___x_186_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__27);
v___x_189_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__4));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
lean_ctor_set(v___x_198_, 2, v___x_197_);
lean_ctor_set(v___x_198_, 3, v___x_197_);
lean_ctor_set(v___x_198_, 4, v___x_196_);
lean_ctor_set(v___x_198_, 5, v___x_196_);
lean_ctor_set(v___x_198_, 6, v___x_196_);
lean_ctor_set(v___x_198_, 7, v___x_196_);
lean_ctor_set(v___x_198_, 8, v___x_196_);
lean_ctor_set(v___x_198_, 9, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_unsigned_to_nat(32u);
v___x_200_ = lean_mk_empty_array_with_capacity(v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4(void){
_start:
{
size_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_202_ = ((size_t)5ULL);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_unsigned_to_nat(32u);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_204_);
v___x_206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__3);
v___x_207_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_203_);
lean_ctor_set(v___x_207_, 3, v___x_203_);
lean_ctor_set_usize(v___x_207_, 4, v___x_202_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = lean_box(1);
v___x_209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
v___x_210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__1);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(lean_object* v_msgData_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; lean_object* v_env_217_; lean_object* v_options_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_216_ = lean_st_ref_get(v___y_214_);
v_env_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_env_217_);
lean_dec(v___x_216_);
v_options_218_ = lean_ctor_get(v___y_213_, 2);
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2);
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5);
lean_inc_ref(v_options_218_);
v___x_221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_221_, 0, v_env_217_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set(v___x_221_, 3, v_options_218_);
v___x_222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msgData_212_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___boxed(lean_object* v_msgData_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(v_msgData_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_ref_233_ = lean_ctor_get(v___y_230_, 5);
v___x_234_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5(v_msg_229_, v___y_230_, v___y_231_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_inc(v_ref_233_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_233_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg___boxed(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(v_msg_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__0));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(lean_object* v___declName_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___closed__1);
v___x_257_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(v___x_256_, v___y_253_, v___y_254_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0___boxed(lean_object* v___declName_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__0(v___declName_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___declName_258_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(lean_object* v_ext_263_, uint8_t v_attrKind_264_, lean_object* v_as_265_, size_t v_sz_266_, size_t v_i_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v_ext_263_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_b_268_);
return v___x_275_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_array_uget_borrowed(v_as_265_, v_i_267_);
lean_inc(v_a_276_);
lean_inc_ref(v_ext_263_);
v___x_277_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_263_, v_a_276_, v_attrKind_264_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_278_; size_t v___x_279_; size_t v___x_280_; 
lean_dec_ref(v___x_277_);
v___x_278_ = lean_box(0);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_267_, v___x_279_);
v_i_267_ = v___x_280_;
v_b_268_ = v___x_278_;
goto _start;
}
else
{
lean_dec_ref(v_ext_263_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1___boxed(lean_object* v_ext_282_, lean_object* v_attrKind_283_, lean_object* v_as_284_, lean_object* v_sz_285_, lean_object* v_i_286_, lean_object* v_b_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
uint8_t v_attrKind_boxed_293_; size_t v_sz_boxed_294_; size_t v_i_boxed_295_; lean_object* v_res_296_; 
v_attrKind_boxed_293_ = lean_unbox(v_attrKind_283_);
v_sz_boxed_294_ = lean_unbox_usize(v_sz_285_);
lean_dec(v_sz_285_);
v_i_boxed_295_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(v_ext_282_, v_attrKind_boxed_293_, v_as_284_, v_sz_boxed_294_, v_i_boxed_295_, v_b_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v_as_284_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_env_304_; lean_object* v___x_305_; lean_object* v_mctx_306_; lean_object* v_lctx_307_; lean_object* v_options_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_303_ = lean_st_ref_get(v___y_301_);
v_env_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_env_304_);
lean_dec(v___x_303_);
v___x_305_ = lean_st_ref_get(v___y_299_);
v_mctx_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc_ref(v_mctx_306_);
lean_dec(v___x_305_);
v_lctx_307_ = lean_ctor_get(v___y_298_, 2);
v_options_308_ = lean_ctor_get(v___y_300_, 2);
lean_inc_ref(v_options_308_);
lean_inc_ref(v_lctx_307_);
v___x_309_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_309_, 0, v_env_304_);
lean_ctor_set(v___x_309_, 1, v_mctx_306_);
lean_ctor_set(v___x_309_, 2, v_lctx_307_);
lean_ctor_set(v___x_309_, 3, v_options_308_);
v___x_310_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_msgData_297_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3___boxed(lean_object* v_msgData_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(v_msgData_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_ref_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_ref_325_ = lean_ctor_get(v___y_322_, 5);
v___x_326_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2_spec__3(v_msg_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_inc(v_ref_325_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_ref_325_);
lean_ctor_set(v___x_331_, 1, v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 1);
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg___boxed(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(lean_object* v_ref_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_fileName_350_; lean_object* v_fileMap_351_; lean_object* v_options_352_; lean_object* v_currRecDepth_353_; lean_object* v_maxRecDepth_354_; lean_object* v_ref_355_; lean_object* v_currNamespace_356_; lean_object* v_openDecls_357_; lean_object* v_initHeartbeats_358_; lean_object* v_maxHeartbeats_359_; lean_object* v_quotContext_360_; lean_object* v_currMacroScope_361_; uint8_t v_diag_362_; lean_object* v_cancelTk_x3f_363_; uint8_t v_suppressElabErrors_364_; lean_object* v_inheritedTraceOptions_365_; lean_object* v_ref_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_fileName_350_ = lean_ctor_get(v___y_347_, 0);
v_fileMap_351_ = lean_ctor_get(v___y_347_, 1);
v_options_352_ = lean_ctor_get(v___y_347_, 2);
v_currRecDepth_353_ = lean_ctor_get(v___y_347_, 3);
v_maxRecDepth_354_ = lean_ctor_get(v___y_347_, 4);
v_ref_355_ = lean_ctor_get(v___y_347_, 5);
v_currNamespace_356_ = lean_ctor_get(v___y_347_, 6);
v_openDecls_357_ = lean_ctor_get(v___y_347_, 7);
v_initHeartbeats_358_ = lean_ctor_get(v___y_347_, 8);
v_maxHeartbeats_359_ = lean_ctor_get(v___y_347_, 9);
v_quotContext_360_ = lean_ctor_get(v___y_347_, 10);
v_currMacroScope_361_ = lean_ctor_get(v___y_347_, 11);
v_diag_362_ = lean_ctor_get_uint8(v___y_347_, sizeof(void*)*14);
v_cancelTk_x3f_363_ = lean_ctor_get(v___y_347_, 12);
v_suppressElabErrors_364_ = lean_ctor_get_uint8(v___y_347_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_365_ = lean_ctor_get(v___y_347_, 13);
v_ref_366_ = l_Lean_replaceRef(v_ref_343_, v_ref_355_);
lean_inc_ref(v_inheritedTraceOptions_365_);
lean_inc(v_cancelTk_x3f_363_);
lean_inc(v_currMacroScope_361_);
lean_inc(v_quotContext_360_);
lean_inc(v_maxHeartbeats_359_);
lean_inc(v_initHeartbeats_358_);
lean_inc(v_openDecls_357_);
lean_inc(v_currNamespace_356_);
lean_inc(v_maxRecDepth_354_);
lean_inc(v_currRecDepth_353_);
lean_inc_ref(v_options_352_);
lean_inc_ref(v_fileMap_351_);
lean_inc_ref(v_fileName_350_);
v___x_367_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_367_, 0, v_fileName_350_);
lean_ctor_set(v___x_367_, 1, v_fileMap_351_);
lean_ctor_set(v___x_367_, 2, v_options_352_);
lean_ctor_set(v___x_367_, 3, v_currRecDepth_353_);
lean_ctor_set(v___x_367_, 4, v_maxRecDepth_354_);
lean_ctor_set(v___x_367_, 5, v_ref_366_);
lean_ctor_set(v___x_367_, 6, v_currNamespace_356_);
lean_ctor_set(v___x_367_, 7, v_openDecls_357_);
lean_ctor_set(v___x_367_, 8, v_initHeartbeats_358_);
lean_ctor_set(v___x_367_, 9, v_maxHeartbeats_359_);
lean_ctor_set(v___x_367_, 10, v_quotContext_360_);
lean_ctor_set(v___x_367_, 11, v_currMacroScope_361_);
lean_ctor_set(v___x_367_, 12, v_cancelTk_x3f_363_);
lean_ctor_set(v___x_367_, 13, v_inheritedTraceOptions_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*14, v_diag_362_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*14 + 1, v_suppressElabErrors_364_);
v___x_368_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v_msg_344_, v___y_345_, v___y_346_, v___x_367_, v___y_348_);
lean_dec_ref(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_ref_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_369_, v_msg_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v_ref_369_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_398_, lean_object* v_declHint_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_env_403_; uint8_t v___x_404_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_env_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_402_);
v___x_404_ = l_Lean_Name_isAnonymous(v_declHint_399_);
if (v___x_404_ == 0)
{
uint8_t v_isExporting_405_; 
v_isExporting_405_ = lean_ctor_get_uint8(v_env_403_, sizeof(void*)*8);
if (v_isExporting_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v_env_403_);
lean_dec(v_declHint_399_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_msg_398_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
lean_inc_ref(v_env_403_);
v___x_407_ = l_Lean_Environment_setExporting(v_env_403_, v___x_404_);
lean_inc(v_declHint_399_);
lean_inc_ref(v___x_407_);
v___x_408_ = l_Lean_Environment_contains(v___x_407_, v_declHint_399_, v_isExporting_405_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_407_);
lean_dec_ref(v_env_403_);
lean_dec(v_declHint_399_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_msg_398_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_c_415_; lean_object* v___x_416_; 
v___x_410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__2);
v___x_411_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__5);
v___x_412_ = l_Lean_Options_empty;
v___x_413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_407_);
lean_ctor_set(v___x_413_, 1, v___x_410_);
lean_ctor_set(v___x_413_, 2, v___x_411_);
lean_ctor_set(v___x_413_, 3, v___x_412_);
lean_inc(v_declHint_399_);
v___x_414_ = l_Lean_MessageData_ofConstName(v_declHint_399_, v___x_404_);
v_c_415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_415_, 0, v___x_413_);
lean_ctor_set(v_c_415_, 1, v___x_414_);
v___x_416_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_403_, v_declHint_399_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_env_403_);
lean_dec(v_declHint_399_);
v___x_417_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_c_415_);
v___x_419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_MessageData_note(v___x_420_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v_msg_398_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_459_; 
v_val_424_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_459_ == 0)
{
v___x_426_ = v___x_416_;
v_isShared_427_ = v_isSharedCheck_459_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v___x_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_459_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_mod_431_; uint8_t v___x_432_; 
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_Environment_header(v_env_403_);
lean_dec_ref(v_env_403_);
v___x_430_ = l_Lean_EnvironmentHeader_moduleNames(v___x_429_);
v_mod_431_ = lean_array_get(v___x_428_, v___x_430_, v_val_424_);
lean_dec(v_val_424_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_isPrivateName(v_declHint_399_);
lean_dec(v_declHint_399_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_c_415_);
v___x_435_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_MessageData_ofName(v_mod_431_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_MessageData_note(v___x_440_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v_msg_398_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 0);
lean_ctor_set(v___x_426_, 0, v___x_442_);
v___x_444_ = v___x_426_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_c_415_);
v___x_448_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_MessageData_ofName(v_mod_431_);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_MessageData_note(v___x_453_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v_msg_398_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 0);
lean_ctor_set(v___x_426_, 0, v___x_455_);
v___x_457_ = v___x_426_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_460_; 
lean_dec_ref(v_env_403_);
lean_dec(v_declHint_399_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_msg_398_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_461_, lean_object* v_declHint_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_461_, v_declHint_462_, v___y_463_);
lean_dec(v___y_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(lean_object* v_msg_466_, lean_object* v_declHint_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v___x_473_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_466_, v_declHint_467_, v___y_471_);
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_478_ = l_Lean_unknownIdentifierMessageTag;
v___x_479_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_a_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8___boxed(lean_object* v_msg_484_, lean_object* v_declHint_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_484_, v_declHint_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(lean_object* v_ref_492_, lean_object* v_msg_493_, lean_object* v_declHint_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v___x_502_; 
v___x_500_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_493_, v_declHint_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_492_, v_a_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_ref_503_, lean_object* v_msg_504_, lean_object* v_declHint_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_503_, v_msg_504_, v_declHint_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_ref_503_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_518_, lean_object* v_constName_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_525_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_526_ = 0;
lean_inc(v_constName_519_);
v___x_527_ = l_Lean_MessageData_ofConstName(v_constName_519_, v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_518_, v___x_530_, v_constName_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_532_, lean_object* v_constName_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_532_, v_constName_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v_ref_532_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(lean_object* v_constName_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_ref_546_; lean_object* v___x_547_; 
v_ref_546_ = lean_ctor_get(v___y_543_, 5);
v___x_547_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_546_, v_constName_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_constName_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(lean_object* v_constName_555_, uint8_t v_skipRealize_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v___x_564_; 
v___x_562_ = lean_st_ref_get(v___y_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
lean_inc(v_constName_555_);
v___x_564_ = l_Lean_Environment_findAsync_x3f(v_env_563_, v_constName_555_, v_skipRealize_556_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_555_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
return v___x_565_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_constName_555_);
v_val_566_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_564_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v___x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 0);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_val_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0___boxed(lean_object* v_constName_574_, lean_object* v_skipRealize_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_skipRealize_boxed_581_; lean_object* v_res_582_; 
v_skipRealize_boxed_581_ = lean_unbox(v_skipRealize_575_);
v_res_582_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(v_constName_574_, v_skipRealize_boxed_581_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_582_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_589_; uint64_t v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0));
v___x_590_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_uint64_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__1);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__0));
v___x_593_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set_uint64(v___x_593_, sizeof(void*)*1, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__3);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_box(1);
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
v___x_599_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4);
v___x_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_597_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set(v___x_605_, 2, v___x_604_);
lean_ctor_set(v___x_605_, 3, v___x_604_);
lean_ctor_set(v___x_605_, 4, v___x_603_);
lean_ctor_set(v___x_605_, 5, v___x_603_);
lean_ctor_set(v___x_605_, 6, v___x_603_);
lean_ctor_set(v___x_605_, 7, v___x_603_);
lean_ctor_set(v___x_605_, 8, v___x_603_);
lean_ctor_set(v___x_605_, 9, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4);
v___x_607_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
lean_ctor_set(v___x_607_, 3, v___x_606_);
lean_ctor_set(v___x_607_, 4, v___x_606_);
lean_ctor_set(v___x_607_, 5, v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__4);
v___x_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
lean_ctor_set(v___x_609_, 4, v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__10));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__12));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__14));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__16));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__18));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(lean_object* v___x_625_, lean_object* v_ext_626_, lean_object* v_attrName_627_, lean_object* v_declName_628_, lean_object* v_x_629_, uint8_t v_attrKind_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_634_ = 0;
v___x_635_ = 1;
v___x_636_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__2);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3_spec__5___closed__4);
v___x_639_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__5);
v___x_640_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__6));
v___x_641_ = lean_box(0);
lean_inc(v___x_625_);
v___x_642_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_642_, 0, v___x_636_);
lean_ctor_set(v___x_642_, 1, v___x_625_);
lean_ctor_set(v___x_642_, 2, v___x_639_);
lean_ctor_set(v___x_642_, 3, v___x_640_);
lean_ctor_set(v___x_642_, 4, v___x_641_);
lean_ctor_set(v___x_642_, 5, v___x_637_);
lean_ctor_set(v___x_642_, 6, v___x_641_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*7, v___x_634_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*7 + 1, v___x_634_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*7 + 2, v___x_634_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*7 + 3, v___x_635_);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__7);
v___x_644_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__8);
v___x_645_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__9);
v___x_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_625_);
lean_ctor_set(v___x_646_, 3, v___x_638_);
lean_ctor_set(v___x_646_, 4, v___x_645_);
v___x_647_ = lean_st_mk_ref(v___x_646_);
lean_inc(v_declName_628_);
v___x_648_ = l_Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0(v_declName_628_, v___x_634_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; uint8_t v_kind_650_; lean_object* v_sig_651_; lean_object* v___x_652_; lean_object* v_type_653_; lean_object* v___x_654_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v_kind_650_ = lean_ctor_get_uint8(v_a_649_, sizeof(void*)*3);
v_sig_651_ = lean_ctor_get(v_a_649_, 1);
lean_inc_ref(v_sig_651_);
lean_dec(v_a_649_);
v___x_652_ = lean_task_get_own(v_sig_651_);
v_type_653_ = lean_ctor_get(v___x_652_, 2);
lean_inc_ref(v_type_653_);
lean_dec(v___x_652_);
v___x_654_ = l_Lean_Meta_isProp(v_type_653_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_724_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_724_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_724_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_724_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___y_666_; uint8_t v___x_667_; 
v___x_659_ = lean_box(0);
v___x_667_ = lean_unbox(v_a_655_);
lean_dec(v_a_655_);
if (v___x_667_ == 0)
{
if (v_kind_650_ == 0)
{
lean_object* v___x_668_; 
lean_inc(v_declName_628_);
v___x_668_ = l_Lean_Meta_Simp_ignoreEquations(v_declName_628_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; uint8_t v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref(v___x_668_);
v___x_670_ = lean_unbox(v_a_669_);
lean_dec(v_a_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v_declName_628_);
v___x_671_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_628_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref(v___x_671_);
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_673_; size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; 
lean_dec(v_declName_628_);
lean_dec(v_attrName_627_);
v_val_673_ = lean_ctor_get(v_a_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_a_672_);
v_sz_674_ = lean_array_size(v_val_673_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__1(v_ext_626_, v_attrKind_630_, v_val_673_, v_sz_674_, v___x_675_, v___x_659_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
lean_dec_ref(v___x_642_);
lean_dec(v_val_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_dec_ref(v___x_676_);
goto v___jp_660_;
}
else
{
v___y_666_ = v___x_676_;
goto v___jp_665_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_a_672_);
lean_dec_ref(v_ext_626_);
v___x_677_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11);
v___x_678_ = l_Lean_MessageData_ofName(v_attrName_627_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_MessageData_ofConstName(v_declName_628_, v___x_634_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__15);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_685_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
lean_dec_ref(v___x_642_);
v___y_666_ = v___x_686_;
goto v___jp_665_;
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_del_object(v___x_657_);
lean_dec(v___x_647_);
lean_dec_ref(v___x_642_);
lean_dec(v_declName_628_);
lean_dec(v_attrName_627_);
lean_dec_ref(v_ext_626_);
v_a_687_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_671_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_671_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v_ext_626_);
v___x_695_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11);
v___x_696_ = l_Lean_MessageData_ofName(v_attrName_627_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_MessageData_ofConstName(v_declName_628_, v___x_634_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__17);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_703_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
lean_dec_ref(v___x_642_);
v___y_666_ = v___x_704_;
goto v___jp_665_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_657_);
lean_dec(v___x_647_);
lean_dec_ref(v___x_642_);
lean_dec(v_declName_628_);
lean_dec(v_attrName_627_);
lean_dec_ref(v_ext_626_);
v_a_705_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_668_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_668_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec_ref(v_ext_626_);
v___x_713_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__11);
v___x_714_ = l_Lean_MessageData_ofName(v_attrName_627_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__13);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_MessageData_ofConstName(v_declName_628_, v___x_634_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___closed__19);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v___x_721_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
lean_dec_ref(v___x_642_);
v___y_666_ = v___x_722_;
goto v___jp_665_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v_attrName_627_);
v___x_723_ = l_Lean_Meta_Sym_Simp_addSymSimpTheorem(v_ext_626_, v_declName_628_, v_attrKind_630_, v___x_642_, v___x_647_, v___y_631_, v___y_632_);
lean_dec_ref(v___x_642_);
v___y_666_ = v___x_723_;
goto v___jp_665_;
}
v___jp_660_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_st_ref_get(v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_661_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_659_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
v___jp_665_:
{
if (lean_obj_tag(v___y_666_) == 0)
{
lean_dec_ref(v___y_666_);
goto v___jp_660_;
}
else
{
lean_del_object(v___x_657_);
lean_dec(v___x_647_);
return v___y_666_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v___x_647_);
lean_dec_ref(v___x_642_);
lean_dec(v_declName_628_);
lean_dec(v_attrName_627_);
lean_dec_ref(v_ext_626_);
v_a_725_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_654_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_654_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v___x_647_);
lean_dec_ref(v___x_642_);
lean_dec(v_declName_628_);
lean_dec(v_attrName_627_);
lean_dec_ref(v_ext_626_);
v_a_733_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_648_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_648_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed(lean_object* v___x_741_, lean_object* v_ext_742_, lean_object* v_attrName_743_, lean_object* v_declName_744_, lean_object* v_x_745_, lean_object* v_attrKind_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
uint8_t v_attrKind_boxed_750_; lean_object* v_res_751_; 
v_attrKind_boxed_750_ = lean_unbox(v_attrKind_746_);
v_res_751_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1(v___x_741_, v_ext_742_, v_attrName_743_, v_declName_744_, v_x_745_, v_attrKind_boxed_750_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_x_745_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr(lean_object* v_attrName_753_, lean_object* v_attrDescr_754_, lean_object* v_ext_755_, lean_object* v_ref_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___f_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___f_758_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___closed__0));
v___x_759_ = lean_box(1);
lean_inc(v_attrName_753_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_mkSymSimpAttr___lam__1___boxed), 9, 3);
lean_closure_set(v___f_760_, 0, v___x_759_);
lean_closure_set(v___f_760_, 1, v_ext_755_);
lean_closure_set(v___f_760_, 2, v_attrName_753_);
v___x_761_ = 1;
v___x_762_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_762_, 0, v_ref_756_);
lean_ctor_set(v___x_762_, 1, v_attrName_753_);
lean_ctor_set(v___x_762_, 2, v_attrDescr_754_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*3, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___f_760_);
lean_ctor_set(v___x_763_, 2, v___f_758_);
v___x_764_ = l_Lean_registerBuiltinAttribute(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkSymSimpAttr___boxed(lean_object* v_attrName_765_, lean_object* v_attrDescr_766_, lean_object* v_ext_767_, lean_object* v_ref_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_765_, v_attrDescr_766_, v_ext_767_, v_ref_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2(lean_object* v_00_u03b1_771_, lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___redArg(v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2___boxed(lean_object* v_00_u03b1_779_, lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__2(v_00_u03b1_779_, v_msg_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3(lean_object* v_00_u03b1_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___redArg(v_msg_788_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3___boxed(lean_object* v_00_u03b1_793_, lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_throwError___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__3(v_00_u03b1_793_, v_msg_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(lean_object* v_00_u03b1_799_, lean_object* v_constName_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___redArg(v_constName_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b1_807_, lean_object* v_constName_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0(v_00_u03b1_807_, v_constName_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_815_, lean_object* v_ref_816_, lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___redArg(v_ref_816_, v_constName_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_824_, lean_object* v_ref_825_, lean_object* v_constName_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1(v_00_u03b1_824_, v_ref_825_, v_constName_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v_ref_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b1_833_, lean_object* v_ref_834_, lean_object* v_msg_835_, lean_object* v_declHint_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___redArg(v_ref_834_, v_msg_835_, v_declHint_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b1_843_, lean_object* v_ref_844_, lean_object* v_msg_845_, lean_object* v_declHint_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7(v_00_u03b1_843_, v_ref_844_, v_msg_845_, v_declHint_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v_ref_844_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(lean_object* v_msg_853_, lean_object* v_declHint_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_853_, v_declHint_854_, v___y_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_861_, lean_object* v_declHint_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_861_, v_declHint_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_869_, lean_object* v_ref_870_, lean_object* v_msg_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___redArg(v_ref_870_, v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_878_, lean_object* v_ref_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Meta_Sym_Simp_mkSymSimpAttr_spec__0_spec__0_spec__1_spec__7_spec__9(v_00_u03b1_878_, v_ref_879_, v_msg_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v_ref_879_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_registerSymSimpAttr___auto__1(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28, &l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28_once, _init_l_Lean_Meta_Sym_Simp_mkSymSimpAttr___auto__1___closed__28);
return v___x_887_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
if (lean_obj_tag(v_x_889_) == 0)
{
uint8_t v___x_890_; 
v___x_890_ = 0;
return v___x_890_;
}
else
{
lean_object* v_key_891_; lean_object* v_tail_892_; uint8_t v___x_893_; 
v_key_891_ = lean_ctor_get(v_x_889_, 0);
v_tail_892_ = lean_ctor_get(v_x_889_, 2);
v___x_893_ = lean_name_eq(v_key_891_, v_a_888_);
if (v___x_893_ == 0)
{
v_x_889_ = v_tail_892_;
goto _start;
}
else
{
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_895_, v_x_896_);
lean_dec(v_x_896_);
lean_dec(v_a_895_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(lean_object* v_a_899_, lean_object* v_b_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec(v_b_900_);
lean_dec(v_a_899_);
return v_x_901_;
}
else
{
lean_object* v_key_902_; lean_object* v_value_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_916_; 
v_key_902_ = lean_ctor_get(v_x_901_, 0);
v_value_903_ = lean_ctor_get(v_x_901_, 1);
v_tail_904_ = lean_ctor_get(v_x_901_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_916_ == 0)
{
v___x_906_ = v_x_901_;
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_value_903_);
lean_inc(v_key_902_);
lean_dec(v_x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v___x_908_; 
v___x_908_ = lean_name_eq(v_key_902_, v_a_899_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_899_, v_b_900_, v_tail_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_key_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_value_903_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v_value_903_);
lean_dec(v_key_902_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_b_900_);
lean_ctor_set(v___x_906_, 0, v_a_899_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_899_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_b_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_tail_904_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_917_; uint64_t v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(1723u);
v___x_918_ = lean_uint64_of_nat(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
return v_x_919_;
}
else
{
lean_object* v_key_921_; lean_object* v_value_922_; lean_object* v_tail_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_949_; 
v_key_921_ = lean_ctor_get(v_x_920_, 0);
v_value_922_ = lean_ctor_get(v_x_920_, 1);
v_tail_923_ = lean_ctor_get(v_x_920_, 2);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_949_ == 0)
{
v___x_925_ = v_x_920_;
v_isShared_926_ = v_isSharedCheck_949_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_tail_923_);
lean_inc(v_value_922_);
lean_inc(v_key_921_);
lean_dec(v_x_920_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_949_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; uint64_t v___y_929_; 
v___x_927_ = lean_array_get_size(v_x_919_);
if (lean_obj_tag(v_key_921_) == 0)
{
uint64_t v___x_947_; 
v___x_947_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_929_ = v___x_947_;
goto v___jp_928_;
}
else
{
uint64_t v_hash_948_; 
v_hash_948_ = lean_ctor_get_uint64(v_key_921_, sizeof(void*)*2);
v___y_929_ = v_hash_948_;
goto v___jp_928_;
}
v___jp_928_:
{
uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v_fold_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_930_ = 32ULL;
v___x_931_ = lean_uint64_shift_right(v___y_929_, v___x_930_);
v_fold_932_ = lean_uint64_xor(v___y_929_, v___x_931_);
v___x_933_ = 16ULL;
v___x_934_ = lean_uint64_shift_right(v_fold_932_, v___x_933_);
v___x_935_ = lean_uint64_xor(v_fold_932_, v___x_934_);
v___x_936_ = lean_uint64_to_usize(v___x_935_);
v___x_937_ = lean_usize_of_nat(v___x_927_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_sub(v___x_937_, v___x_938_);
v___x_940_ = lean_usize_land(v___x_936_, v___x_939_);
v___x_941_ = lean_array_uget_borrowed(v_x_919_, v___x_940_);
lean_inc(v___x_941_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 2, v___x_941_);
v___x_943_ = v___x_925_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_key_921_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_value_922_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v___x_941_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_array_uset(v_x_919_, v___x_940_, v___x_943_);
v_x_919_ = v___x_944_;
v_x_920_ = v_tail_923_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_950_, lean_object* v_source_951_, lean_object* v_target_952_){
_start:
{
lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_953_ = lean_array_get_size(v_source_951_);
v___x_954_ = lean_nat_dec_lt(v_i_950_, v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_source_951_);
lean_dec(v_i_950_);
return v_target_952_;
}
else
{
lean_object* v_es_955_; lean_object* v___x_956_; lean_object* v_source_957_; lean_object* v_target_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_es_955_ = lean_array_fget(v_source_951_, v_i_950_);
v___x_956_ = lean_box(0);
v_source_957_ = lean_array_fset(v_source_951_, v_i_950_, v___x_956_);
v_target_958_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_952_, v_es_955_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v_i_950_, v___x_959_);
lean_dec(v_i_950_);
v_i_950_ = v___x_960_;
v_source_951_ = v_source_957_;
v_target_952_ = v_target_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(lean_object* v_data_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_nbuckets_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_963_ = lean_array_get_size(v_data_962_);
v___x_964_ = lean_unsigned_to_nat(2u);
v_nbuckets_965_ = lean_nat_mul(v___x_963_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_box(0);
v___x_968_ = lean_mk_array(v_nbuckets_965_, v___x_967_);
v___x_969_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v___x_966_, v_data_962_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(lean_object* v_m_970_, lean_object* v_a_971_, lean_object* v_b_972_){
_start:
{
lean_object* v_size_973_; lean_object* v_buckets_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1020_; 
v_size_973_ = lean_ctor_get(v_m_970_, 0);
v_buckets_974_ = lean_ctor_get(v_m_970_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_m_970_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_976_ = v_m_970_;
v_isShared_977_ = v_isSharedCheck_1020_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_buckets_974_);
lean_inc(v_size_973_);
lean_dec(v_m_970_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1020_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; uint64_t v___y_980_; 
v___x_978_ = lean_array_get_size(v_buckets_974_);
if (lean_obj_tag(v_a_971_) == 0)
{
uint64_t v___x_1018_; 
v___x_1018_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_980_ = v___x_1018_;
goto v___jp_979_;
}
else
{
uint64_t v_hash_1019_; 
v_hash_1019_ = lean_ctor_get_uint64(v_a_971_, sizeof(void*)*2);
v___y_980_ = v_hash_1019_;
goto v___jp_979_;
}
v___jp_979_:
{
uint64_t v___x_981_; uint64_t v___x_982_; uint64_t v_fold_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v_bkt_992_; uint8_t v___x_993_; 
v___x_981_ = 32ULL;
v___x_982_ = lean_uint64_shift_right(v___y_980_, v___x_981_);
v_fold_983_ = lean_uint64_xor(v___y_980_, v___x_982_);
v___x_984_ = 16ULL;
v___x_985_ = lean_uint64_shift_right(v_fold_983_, v___x_984_);
v___x_986_ = lean_uint64_xor(v_fold_983_, v___x_985_);
v___x_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = lean_usize_of_nat(v___x_978_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_sub(v___x_988_, v___x_989_);
v___x_991_ = lean_usize_land(v___x_987_, v___x_990_);
v_bkt_992_ = lean_array_uget_borrowed(v_buckets_974_, v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_971_, v_bkt_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v_size_x27_995_; lean_object* v___x_996_; lean_object* v_buckets_x27_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_994_ = lean_unsigned_to_nat(1u);
v_size_x27_995_ = lean_nat_add(v_size_973_, v___x_994_);
lean_dec(v_size_973_);
lean_inc(v_bkt_992_);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v_a_971_);
lean_ctor_set(v___x_996_, 1, v_b_972_);
lean_ctor_set(v___x_996_, 2, v_bkt_992_);
v_buckets_x27_997_ = lean_array_uset(v_buckets_974_, v___x_991_, v___x_996_);
v___x_998_ = lean_unsigned_to_nat(4u);
v___x_999_ = lean_nat_mul(v_size_x27_995_, v___x_998_);
v___x_1000_ = lean_unsigned_to_nat(3u);
v___x_1001_ = lean_nat_div(v___x_999_, v___x_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_array_get_size(v_buckets_x27_997_);
v___x_1003_ = lean_nat_dec_le(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
if (v___x_1003_ == 0)
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
v_val_1004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_buckets_x27_997_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_val_1004_);
lean_ctor_set(v___x_976_, 0, v_size_x27_995_);
v___x_1006_ = v___x_976_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_size_x27_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v___x_1009_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_buckets_x27_997_);
lean_ctor_set(v___x_976_, 0, v_size_x27_995_);
v___x_1009_ = v___x_976_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_x27_995_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_buckets_x27_997_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v_buckets_x27_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc(v_bkt_992_);
v___x_1011_ = lean_box(0);
v_buckets_x27_1012_ = lean_array_uset(v_buckets_974_, v___x_991_, v___x_1011_);
v___x_1013_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_971_, v_b_972_, v_bkt_992_);
v___x_1014_ = lean_array_uset(v_buckets_x27_1012_, v___x_991_, v___x_1013_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_1014_);
v___x_1016_ = v___x_976_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_size_973_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object* v_attrName_1021_, lean_object* v_attrDescr_1022_, lean_object* v_ref_1023_){
_start:
{
lean_object* v___x_1025_; 
lean_inc(v_ref_1023_);
v___x_1025_ = l_Lean_Meta_Sym_Simp_mkSymSimpExt(v_ref_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_n(v_a_1026_, 2);
lean_dec_ref(v___x_1025_);
lean_inc(v_attrName_1021_);
v___x_1027_ = l_Lean_Meta_Sym_Simp_mkSymSimpAttr(v_attrName_1021_, v_attrDescr_1022_, v_a_1026_, v_ref_1023_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1038_; 
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1039_);
v___x_1029_ = v___x_1027_;
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1027_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1031_ = l_Lean_Meta_Sym_Simp_symSimpExtensionMapRef;
v___x_1032_ = lean_st_ref_take(v___x_1031_);
lean_inc(v_a_1026_);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v___x_1032_, v_attrName_1021_, v_a_1026_);
v___x_1034_ = lean_st_ref_set(v___x_1031_, v___x_1033_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_a_1026_);
v___x_1036_ = v___x_1029_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1026_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_1026_);
lean_dec(v_attrName_1021_);
v_a_1040_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1027_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1027_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
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
lean_dec(v_ref_1023_);
lean_dec_ref(v_attrDescr_1022_);
lean_dec(v_attrName_1021_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr___boxed(lean_object* v_attrName_1048_, lean_object* v_attrDescr_1049_, lean_object* v_ref_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v_attrName_1048_, v_attrDescr_1049_, v_ref_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_m_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0___redArg(v_m_1054_, v_a_1055_, v_b_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___redArg(v_a_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__0(v_00_u03b2_1062_, v_a_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec(v_a_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1(lean_object* v_00_u03b2_1067_, lean_object* v_data_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1___redArg(v_data_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__2___redArg(v_a_1071_, v_b_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1075_, lean_object* v_i_1076_, lean_object* v_source_1077_, lean_object* v_target_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2___redArg(v_i_1076_, v_source_1077_, v_target_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_registerSymSimpAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_1100_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_1101_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_));
v___x_1102_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_1099_, v___x_1100_, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2____boxed(lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Sym_Simp_Attr_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Attr_3736676144____hygCtx___hyg_2_();
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_Meta_Sym_Simp_symSimpExtension;
v___x_1108_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1107_, v_a_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg___boxed(lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_1109_);
lean_dec(v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems(lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___boxed(lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems(v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1119_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
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
