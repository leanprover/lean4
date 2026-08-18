// Lean compiler output
// Module: Lean.ScopedEnvExtension
// Imports: public import Lean.Attributes
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value;
static const lean_array_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value;
static const lean_string_object l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17 = (const lean_object*)&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27;
static lean_once_cell_t l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_name___autoParam;
static const lean_string_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value),((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)}};
static const lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value;
static const lean_ctor_object l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value),((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value)}};
static const lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2 = (const lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value),((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value),((lean_object*)&l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4;
static lean_once_cell_t l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_scopedEnvExtensionsRef;
static const lean_string_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_popScope___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.ScopedEnvExtension"};
static const lean_object* l_Lean_ScopedEnvExtension_getState___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value;
static const lean_string_object l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.ScopedEnvExtension.getState"};
static const lean_object* l_Lean_ScopedEnvExtension_getState___redArg___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value;
static const lean_string_object l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_ScopedEnvExtension_getState___redArg___closed__2 = (const lean_object*)&l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value;
static lean_once_cell_t l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_getState___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_pushScope___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_pushScope___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam;
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___boxed(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx(v_00_u03b1_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_12_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v_t_12_, 2);
v___x_18_ = lean_apply_2(v_k_13_, v_a_16_, v_a_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim(lean_object* v_00_u03b1_19_, lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___boxed(lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_ScopedEnvExtension_Entry_ctorElim(v_00_u03b1_26_, v_motive_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim___redArg(lean_object* v_t_33_, lean_object* v_global_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_33_, v_global_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim(lean_object* v_00_u03b1_36_, lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_global_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_38_, v_global_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim___redArg(lean_object* v_t_42_, lean_object* v_scoped_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_42_, v_scoped_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim(lean_object* v_00_u03b1_45_, lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_scoped_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_47_, v_scoped_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0(void){
_start:
{
lean_object* v_cellCount_51_; lean_object* v___x_52_; 
v_cellCount_51_ = lean_unsigned_to_nat(16u);
v___x_52_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1(void){
_start:
{
lean_object* v_cellCount_53_; lean_object* v___x_54_; 
v_cellCount_53_ = lean_unsigned_to_nat(16u);
v___x_54_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1);
v___x_56_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
lean_ctor_set(v___x_58_, 2, v___x_55_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_59_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_63_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2);
v___x_64_ = 1;
v___x_65_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_62_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object* v_00_u03b2_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_00_u03c3_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_110_ = l_Lean_mkAtom(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_112_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_123_ = l_Lean_mkAtom(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_125_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_128_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_129_ = lean_box(2);
v___x_130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_132_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_135_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_136_ = lean_box(2);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_139_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_140_ = lean_array_push(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_142_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_143_ = lean_box(2);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_146_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_149_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_150_ = lean_box(2);
v___x_151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_153_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_154_ = lean_array_push(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_156_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_157_ = lean_box(2);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_169_, v___y_170_, v___y_171_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec(v_x_169_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_174_, lean_object* v_x_175_){
_start:
{
lean_inc(v_inst_174_);
return v_inst_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_176_, v_x_177_);
lean_dec(v_x_177_);
lean_dec(v_inst_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_179_, lean_object* v_x_180_){
_start:
{
lean_inc(v_s_179_);
return v_s_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec(v_s_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_a_185_);
lean_inc_ref_n(v___x_186_, 2);
v___x_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_ctor_set(v___x_187_, 2, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_188_, v_a_189_);
lean_dec_ref(v_x_188_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_instInhabitedError;
v___x_195_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_195_, 0, lean_box(0));
lean_closure_set(v___x_195_, 1, lean_box(0));
lean_closure_set(v___x_195_, 2, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___f_198_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_199_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_199_, 0, v_inst_197_);
v___f_200_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_201_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_202_ = lean_box(0);
v___x_203_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_204_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_205_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_205_, 0, v___x_202_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___f_198_);
lean_ctor_set(v___x_205_, 3, v___f_199_);
lean_ctor_set(v___x_205_, 4, v___f_200_);
lean_ctor_set(v___x_205_, 5, v___x_204_);
lean_ctor_set(v___x_205_, 6, v___f_201_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_00_u03c3_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_211_){
_start:
{
lean_object* v_mkInitial_213_; lean_object* v___x_214_; 
v_mkInitial_213_ = lean_ctor_get(v_descr_211_, 1);
lean_inc_ref(v_mkInitial_213_);
lean_dec_ref(v_descr_211_);
v___x_214_ = lean_apply_1(v_mkInitial_213_, lean_box(0));
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_229_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_229_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_219_ = l_Lean_NameSet_empty;
v___x_220_ = 1;
v___x_221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_221_, 0, v_a_215_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*2, v___x_220_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5);
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_225_);
v___x_227_ = v___x_217_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_a_230_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_214_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_214_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_00_u03c3_243_, lean_object* v_descr_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_00_u03c3_249_, lean_object* v_descr_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_247_, v_00_u03b2_248_, v_00_u03c3_249_, v_descr_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_253_, lean_object* v_vals_254_, lean_object* v_i_255_, lean_object* v_k_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_keys_253_);
v___x_258_ = lean_nat_dec_lt(v_i_255_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v_i_255_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v_k_x27_260_; uint8_t v___x_261_; 
v_k_x27_260_ = lean_array_fget_borrowed(v_keys_253_, v_i_255_);
v___x_261_ = lean_name_eq(v_k_256_, v_k_x27_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_i_255_, v___x_262_);
lean_dec(v_i_255_);
v_i_255_ = v___x_263_;
goto _start;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_array_fget_borrowed(v_vals_254_, v_i_255_);
lean_dec(v_i_255_);
lean_inc(v___x_265_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_267_, lean_object* v_vals_268_, lean_object* v_i_269_, lean_object* v_k_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_267_, v_vals_268_, v_i_269_, v_k_270_);
lean_dec(v_k_270_);
lean_dec_ref(v_vals_268_);
lean_dec_ref(v_keys_267_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_272_, size_t v_x_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v_es_275_; lean_object* v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_j_279_; lean_object* v___x_280_; 
v_es_275_ = lean_ctor_get(v_x_272_, 0);
v___x_276_ = lean_box(2);
v___x_277_ = ((size_t)31ULL);
v___x_278_ = lean_usize_land(v_x_273_, v___x_277_);
v_j_279_ = lean_usize_to_nat(v___x_278_);
v___x_280_ = lean_array_get_borrowed(v___x_276_, v_es_275_, v_j_279_);
lean_dec(v_j_279_);
switch(lean_obj_tag(v___x_280_))
{
case 0:
{
lean_object* v_key_281_; lean_object* v_val_282_; uint8_t v___x_283_; 
v_key_281_ = lean_ctor_get(v___x_280_, 0);
v_val_282_ = lean_ctor_get(v___x_280_, 1);
v___x_283_ = lean_name_eq(v_x_274_, v_key_281_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
lean_inc(v_val_282_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_val_282_);
return v___x_285_;
}
}
case 1:
{
lean_object* v_node_286_; size_t v___x_287_; size_t v___x_288_; 
v_node_286_ = lean_ctor_get(v___x_280_, 0);
v___x_287_ = ((size_t)5ULL);
v___x_288_ = lean_usize_shift_right(v_x_273_, v___x_287_);
v_x_272_ = v_node_286_;
v_x_273_ = v___x_288_;
goto _start;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(0);
return v___x_290_;
}
}
}
else
{
lean_object* v_ks_291_; lean_object* v_vs_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_ks_291_ = lean_ctor_get(v_x_272_, 0);
v_vs_292_ = lean_ctor_get(v_x_272_, 1);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_291_, v_vs_292_, v___x_293_, v_x_274_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
size_t v_x_1285__boxed_298_; lean_object* v_res_299_; 
v_x_1285__boxed_298_ = lean_unbox_usize(v_x_296_);
lean_dec(v_x_296_);
v_res_299_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_295_, v_x_1285__boxed_298_, v_x_297_);
lean_dec(v_x_297_);
lean_dec_ref(v_x_295_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint64_t v___y_303_; 
if (lean_obj_tag(v_x_301_) == 0)
{
uint64_t v___x_306_; 
v___x_306_ = 1723ULL;
v___y_303_ = v___x_306_;
goto v___jp_302_;
}
else
{
uint64_t v_hash_307_; 
v_hash_307_ = lean_ctor_get_uint64(v_x_301_, sizeof(void*)*2);
v___y_303_ = v_hash_307_;
goto v___jp_302_;
}
v___jp_302_:
{
size_t v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_uint64_to_usize(v___y_303_);
v___x_305_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_300_, v___x_304_, v_x_301_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_m_311_, lean_object* v_query_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_zero_316_; uint8_t v_isZero_317_; 
v_zero_316_ = lean_unsigned_to_nat(0u);
v_isZero_317_ = lean_nat_dec_eq(v_x_314_, v_zero_316_);
if (v_isZero_317_ == 1)
{
lean_dec(v_x_315_);
lean_dec(v_x_314_);
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(2);
return v___x_318_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_val_319_ = lean_ctor_get(v_x_313_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v_x_313_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v_x_313_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_val_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_keyArray_327_; lean_object* v_valueArray_328_; lean_object* v___x_329_; uint8_t v_isSome_330_; 
v_keyArray_327_ = lean_ctor_get(v_m_311_, 1);
v_valueArray_328_ = lean_ctor_get(v_m_311_, 2);
v___x_329_ = lean_array_fget_borrowed(v_keyArray_327_, v_x_315_);
v_isSome_330_ = lean_noption_is_some(v___x_329_);
if (v_isSome_330_ == 0)
{
lean_dec(v_x_314_);
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_x_315_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_x_315_);
v_val_332_ = lean_ctor_get(v_x_313_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v_x_313_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v_x_313_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_val_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_one_340_; lean_object* v_n_341_; lean_object* v___y_343_; 
v_one_340_ = lean_unsigned_to_nat(1u);
v_n_341_ = lean_nat_sub(v_x_314_, v_one_340_);
lean_dec(v_x_314_);
if (v_isSome_330_ == 0)
{
goto v___jp_349_;
}
else
{
lean_object* v___x_351_; uint8_t v_isSome_352_; 
v___x_351_ = lean_array_fget_borrowed(v_valueArray_328_, v_x_315_);
v_isSome_352_ = lean_noption_is_some(v___x_351_);
if (v_isSome_352_ == 0)
{
goto v___jp_349_;
}
else
{
lean_object* v_val_353_; uint8_t v___x_354_; 
lean_inc(v___x_329_);
v_val_353_ = lean_noption_get(v___x_329_);
v___x_354_ = lean_name_eq(v_val_353_, v_query_312_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
lean_dec(v_val_353_);
v___x_355_ = lean_array_get_size(v_keyArray_327_);
v___x_356_ = lean_nat_add(v_x_315_, v_one_340_);
lean_dec(v_x_315_);
v___x_357_ = lean_nat_dec_lt(v___x_356_, v___x_355_);
if (v___x_357_ == 0)
{
lean_dec(v___x_356_);
v_x_314_ = v_n_341_;
v_x_315_ = v_zero_316_;
goto _start;
}
else
{
v_x_314_ = v_n_341_;
v_x_315_ = v___x_356_;
goto _start;
}
}
else
{
lean_object* v_val_360_; lean_object* v___x_361_; 
lean_dec(v_n_341_);
lean_dec(v_x_313_);
lean_inc(v___x_351_);
v_val_360_ = lean_noption_get(v___x_351_);
v___x_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_361_, 0, v_x_315_);
lean_ctor_set(v___x_361_, 1, v_val_353_);
lean_ctor_set(v___x_361_, 2, v_val_360_);
return v___x_361_;
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_get_size(v_keyArray_327_);
v___x_345_ = lean_nat_add(v_x_315_, v_one_340_);
lean_dec(v_x_315_);
v___x_346_ = lean_nat_dec_lt(v___x_345_, v___x_344_);
if (v___x_346_ == 0)
{
lean_dec(v___x_345_);
v_x_313_ = v___y_343_;
v_x_314_ = v_n_341_;
v_x_315_ = v_zero_316_;
goto _start;
}
else
{
v_x_313_ = v___y_343_;
v_x_314_ = v_n_341_;
v_x_315_ = v___x_345_;
goto _start;
}
}
v___jp_349_:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_350_; 
lean_inc(v_x_315_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_x_315_);
v___y_343_ = v___x_350_;
goto v___jp_342_;
}
else
{
v___y_343_ = v_x_313_;
goto v___jp_342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_362_, lean_object* v_query_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_m_362_, v_query_363_, v_x_364_, v_x_365_, v_x_366_);
lean_dec(v_query_363_);
lean_dec_ref(v_m_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_m_368_, lean_object* v_query_369_){
_start:
{
lean_object* v_keyArray_370_; lean_object* v___x_371_; uint64_t v___y_373_; 
v_keyArray_370_ = lean_ctor_get(v_m_368_, 1);
v___x_371_ = lean_array_get_size(v_keyArray_370_);
if (lean_obj_tag(v_query_369_) == 0)
{
uint64_t v___x_388_; 
v___x_388_ = 1723ULL;
v___y_373_ = v___x_388_;
goto v___jp_372_;
}
else
{
uint64_t v_hash_389_; 
v_hash_389_ = lean_ctor_get_uint64(v_query_369_, sizeof(void*)*2);
v___y_373_ = v_hash_389_;
goto v___jp_372_;
}
v___jp_372_:
{
uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v_fold_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_374_ = 32ULL;
v___x_375_ = lean_uint64_shift_right(v___y_373_, v___x_374_);
v_fold_376_ = lean_uint64_xor(v___y_373_, v___x_375_);
v___x_377_ = 16ULL;
v___x_378_ = lean_uint64_shift_right(v_fold_376_, v___x_377_);
v___x_379_ = lean_uint64_xor(v_fold_376_, v___x_378_);
v___x_380_ = lean_uint64_to_usize(v___x_379_);
v___x_381_ = lean_usize_of_nat(v___x_371_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_sub(v___x_381_, v___x_382_);
v___x_384_ = lean_usize_land(v___x_380_, v___x_383_);
v___x_385_ = lean_usize_to_nat(v___x_384_);
v___x_386_ = lean_box(0);
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_m_368_, v_query_369_, v___x_386_, v___x_371_, v___x_385_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg___boxed(lean_object* v_m_390_, lean_object* v_query_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_m_390_, v_query_391_);
lean_dec(v_query_391_);
lean_dec_ref(v_m_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_m_393_, lean_object* v_query_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_m_393_, v_query_394_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_index_396_; lean_object* v_key_397_; lean_object* v_value_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_index_396_ = lean_ctor_get(v___x_395_, 0);
v_key_397_ = lean_ctor_get(v___x_395_, 1);
v_value_398_ = lean_ctor_get(v___x_395_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_395_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_value_398_);
lean_inc(v_key_397_);
lean_inc(v_index_396_);
lean_dec(v___x_395_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_index_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_key_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_value_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_object* v___x_406_; 
lean_dec(v___x_395_);
v___x_406_ = lean_box(1);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_407_, lean_object* v_query_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_m_407_, v_query_408_);
lean_dec(v_query_408_);
lean_dec_ref(v_m_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_m_410_, v_a_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_value_413_; lean_object* v___x_414_; 
v_value_413_ = lean_ctor_get(v___x_412_, 2);
lean_inc(v_value_413_);
lean_dec_ref_known(v___x_412_, 3);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_value_413_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_m_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_stage_u2081_421_; 
v_stage_u2081_421_ = lean_ctor_get_uint8(v_x_419_, sizeof(void*)*2);
if (v_stage_u2081_421_ == 0)
{
lean_object* v_map_u2081_422_; lean_object* v_map_u2082_423_; lean_object* v___x_424_; 
v_map_u2081_422_ = lean_ctor_get(v_x_419_, 0);
v_map_u2082_423_ = lean_ctor_get(v_x_419_, 1);
v___x_424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_423_, v_x_420_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_422_, v_x_420_);
return v___x_425_;
}
else
{
return v___x_424_;
}
}
else
{
lean_object* v_map_u2081_426_; lean_object* v___x_427_; 
v_map_u2081_426_ = lean_ctor_get(v_x_419_, 0);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_426_, v_x_420_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12___redArg(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_ks_435_; lean_object* v_vs_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_460_; 
v_ks_435_ = lean_ctor_get(v_x_431_, 0);
v_vs_436_ = lean_ctor_get(v_x_431_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_460_ == 0)
{
v___x_438_ = v_x_431_;
v_isShared_439_ = v_isSharedCheck_460_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_vs_436_);
lean_inc(v_ks_435_);
lean_dec(v_x_431_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_460_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_array_get_size(v_ks_435_);
v___x_441_ = lean_nat_dec_lt(v_x_432_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_x_432_);
v___x_442_ = lean_array_push(v_ks_435_, v_x_433_);
v___x_443_ = lean_array_push(v_vs_436_, v_x_434_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_443_);
lean_ctor_set(v___x_438_, 0, v___x_442_);
v___x_445_ = v___x_438_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v_k_x27_447_; uint8_t v___x_448_; 
v_k_x27_447_ = lean_array_fget_borrowed(v_ks_435_, v_x_432_);
v___x_448_ = lean_name_eq(v_x_433_, v_k_x27_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_450_; 
if (v_isShared_439_ == 0)
{
v___x_450_ = v___x_438_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_ks_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_vs_436_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_x_432_, v___x_451_);
lean_dec(v_x_432_);
v_x_431_ = v___x_450_;
v_x_432_ = v___x_452_;
goto _start;
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_array_fset(v_ks_435_, v_x_432_, v_x_433_);
v___x_456_ = lean_array_fset(v_vs_436_, v_x_432_, v_x_434_);
lean_dec(v_x_432_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_456_);
lean_ctor_set(v___x_438_, 0, v___x_455_);
v___x_458_ = v___x_438_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_n_461_, lean_object* v_k_462_, lean_object* v_v_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12___redArg(v_n_461_, v___x_464_, v_k_462_, v_v_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_x_467_, size_t v_x_468_, size_t v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v_es_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v_j_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_es_472_ = lean_ctor_get(v_x_467_, 0);
v___x_473_ = ((size_t)31ULL);
v___x_474_ = lean_usize_land(v_x_468_, v___x_473_);
v_j_475_ = lean_usize_to_nat(v___x_474_);
v___x_476_ = lean_array_get_size(v_es_472_);
v___x_477_ = lean_nat_dec_lt(v_j_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v_j_475_);
lean_dec(v_x_471_);
lean_dec(v_x_470_);
return v_x_467_;
}
else
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_516_; 
lean_inc_ref(v_es_472_);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_x_467_, 0);
lean_dec(v_unused_517_);
v___x_479_ = v_x_467_;
v_isShared_480_ = v_isSharedCheck_516_;
goto v_resetjp_478_;
}
else
{
lean_dec(v_x_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_516_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_v_481_; lean_object* v___x_482_; lean_object* v_xs_x27_483_; lean_object* v___y_485_; 
v_v_481_ = lean_array_fget(v_es_472_, v_j_475_);
v___x_482_ = lean_box(0);
v_xs_x27_483_ = lean_array_fset(v_es_472_, v_j_475_, v___x_482_);
switch(lean_obj_tag(v_v_481_))
{
case 0:
{
lean_object* v_key_490_; lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_501_; 
v_key_490_ = lean_ctor_get(v_v_481_, 0);
v_val_491_ = lean_ctor_get(v_v_481_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_v_481_);
if (v_isSharedCheck_501_ == 0)
{
v___x_493_ = v_v_481_;
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_inc(v_key_490_);
lean_dec(v_v_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_name_eq(v_x_470_, v_key_490_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_del_object(v___x_493_);
v___x_496_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_490_, v_val_491_, v_x_470_, v_x_471_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
v___y_485_ = v___x_497_;
goto v___jp_484_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_val_491_);
lean_dec(v_key_490_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_x_471_);
lean_ctor_set(v___x_493_, 0, v_x_470_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_x_470_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_x_471_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
v___y_485_ = v___x_499_;
goto v___jp_484_;
}
}
}
}
case 1:
{
lean_object* v_node_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_514_; 
v_node_502_ = lean_ctor_get(v_v_481_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_v_481_);
if (v_isSharedCheck_514_ == 0)
{
v___x_504_ = v_v_481_;
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_node_502_);
lean_dec(v_v_481_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_506_ = ((size_t)5ULL);
v___x_507_ = lean_usize_shift_right(v_x_468_, v___x_506_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_x_469_, v___x_508_);
v___x_510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_node_502_, v___x_507_, v___x_509_, v_x_470_, v_x_471_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_510_);
v___x_512_ = v___x_504_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
v___y_485_ = v___x_512_;
goto v___jp_484_;
}
}
}
default: 
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_x_470_);
lean_ctor_set(v___x_515_, 1, v_x_471_);
v___y_485_ = v___x_515_;
goto v___jp_484_;
}
}
v___jp_484_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_array_fset(v_xs_x27_483_, v_j_475_, v___y_485_);
lean_dec(v_j_475_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_486_);
v___x_488_ = v___x_479_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
lean_object* v_ks_518_; lean_object* v_vs_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_539_; 
v_ks_518_ = lean_ctor_get(v_x_467_, 0);
v_vs_519_ = lean_ctor_get(v_x_467_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_539_ == 0)
{
v___x_521_ = v_x_467_;
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_vs_519_);
lean_inc(v_ks_518_);
lean_dec(v_x_467_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_539_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_ks_518_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_vs_519_);
v___x_524_ = v_reuseFailAlloc_538_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v_newNode_525_; uint8_t v___y_527_; size_t v___x_533_; uint8_t v___x_534_; 
v_newNode_525_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10___redArg(v___x_524_, v_x_470_, v_x_471_);
v___x_533_ = ((size_t)7ULL);
v___x_534_ = lean_usize_dec_le(v___x_533_, v_x_469_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_525_);
v___x_536_ = lean_unsigned_to_nat(4u);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
lean_dec(v___x_535_);
v___y_527_ = v___x_537_;
goto v___jp_526_;
}
else
{
v___y_527_ = v___x_534_;
goto v___jp_526_;
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v_ks_528_; lean_object* v_vs_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_ks_528_ = lean_ctor_get(v_newNode_525_, 0);
lean_inc_ref(v_ks_528_);
v_vs_529_ = lean_ctor_get(v_newNode_525_, 1);
lean_inc_ref(v_vs_529_);
lean_dec_ref(v_newNode_525_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___closed__0);
v___x_532_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg(v_x_469_, v_ks_528_, v_vs_529_, v___x_530_, v___x_531_);
lean_dec_ref(v_vs_529_);
lean_dec_ref(v_ks_528_);
return v___x_532_;
}
else
{
return v_newNode_525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg(size_t v_depth_540_, lean_object* v_keys_541_, lean_object* v_vals_542_, lean_object* v_i_543_, lean_object* v_entries_544_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_get_size(v_keys_541_);
v___x_546_ = lean_nat_dec_lt(v_i_543_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v_i_543_);
return v_entries_544_;
}
else
{
lean_object* v_k_547_; lean_object* v_v_548_; uint64_t v___y_550_; 
v_k_547_ = lean_array_fget_borrowed(v_keys_541_, v_i_543_);
v_v_548_ = lean_array_fget_borrowed(v_vals_542_, v_i_543_);
if (lean_obj_tag(v_k_547_) == 0)
{
uint64_t v___x_561_; 
v___x_561_ = 1723ULL;
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
uint64_t v_hash_562_; 
v_hash_562_ = lean_ctor_get_uint64(v_k_547_, sizeof(void*)*2);
v___y_550_ = v_hash_562_;
goto v___jp_549_;
}
v___jp_549_:
{
size_t v_h_551_; size_t v___x_552_; lean_object* v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v_h_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_h_551_ = lean_uint64_to_usize(v___y_550_);
v___x_552_ = ((size_t)5ULL);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_sub(v_depth_540_, v___x_554_);
v___x_556_ = lean_usize_mul(v___x_552_, v___x_555_);
v_h_557_ = lean_usize_shift_right(v_h_551_, v___x_556_);
v___x_558_ = lean_nat_add(v_i_543_, v___x_553_);
lean_dec(v_i_543_);
lean_inc(v_v_548_);
lean_inc(v_k_547_);
v___x_559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_entries_544_, v_h_557_, v_depth_540_, v_k_547_, v_v_548_);
v_i_543_ = v___x_558_;
v_entries_544_ = v___x_559_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg___boxed(lean_object* v_depth_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_entries_567_){
_start:
{
size_t v_depth_boxed_568_; lean_object* v_res_569_; 
v_depth_boxed_568_ = lean_unbox_usize(v_depth_563_);
lean_dec(v_depth_563_);
v_res_569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg(v_depth_boxed_568_, v_keys_564_, v_vals_565_, v_i_566_, v_entries_567_);
lean_dec_ref(v_vals_565_);
lean_dec_ref(v_keys_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v_x_1603__boxed_575_; size_t v_x_1604__boxed_576_; lean_object* v_res_577_; 
v_x_1603__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_x_1604__boxed_576_ = lean_unbox_usize(v_x_572_);
lean_dec(v_x_572_);
v_res_577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_x_570_, v_x_1603__boxed_575_, v_x_1604__boxed_576_, v_x_573_, v_x_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
uint64_t v___y_582_; 
if (lean_obj_tag(v_x_579_) == 0)
{
uint64_t v___x_586_; 
v___x_586_ = 1723ULL;
v___y_582_ = v___x_586_;
goto v___jp_581_;
}
else
{
uint64_t v_hash_587_; 
v_hash_587_ = lean_ctor_get_uint64(v_x_579_, sizeof(void*)*2);
v___y_582_ = v_hash_587_;
goto v___jp_581_;
}
v___jp_581_:
{
size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_uint64_to_usize(v___y_582_);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_x_578_, v___x_583_, v___x_584_, v_x_579_, v_x_580_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg(lean_object* v_b_588_, lean_object* v_acc_589_, lean_object* v_i_590_){
_start:
{
lean_object* v___y_592_; lean_object* v_keyArray_600_; lean_object* v_valueArray_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_keyArray_600_ = lean_ctor_get(v_b_588_, 1);
v_valueArray_601_ = lean_ctor_get(v_b_588_, 2);
v___x_602_ = lean_array_get_size(v_keyArray_600_);
v___x_603_ = lean_nat_dec_lt(v_i_590_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v_i_590_);
return v_acc_589_;
}
else
{
lean_object* v___x_604_; uint8_t v_isSome_605_; 
v___x_604_ = lean_array_fget_borrowed(v_keyArray_600_, v_i_590_);
v_isSome_605_ = lean_noption_is_some(v___x_604_);
if (v_isSome_605_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_606_; uint8_t v_isSome_607_; 
v___x_606_ = lean_array_fget_borrowed(v_valueArray_601_, v_i_590_);
v_isSome_607_ = lean_noption_is_some(v___x_606_);
if (v_isSome_607_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v_val_608_; lean_object* v_val_609_; lean_object* v_i_611_; lean_object* v___x_616_; 
lean_inc(v___x_604_);
v_val_608_ = lean_noption_get(v___x_604_);
lean_inc(v___x_606_);
v_val_609_ = lean_noption_get(v___x_606_);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_acc_589_, v_val_608_);
switch(lean_obj_tag(v___x_616_))
{
case 0:
{
lean_object* v_index_617_; lean_object* v_size_618_; lean_object* v___x_619_; 
v_index_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_index_617_);
lean_dec_ref_known(v___x_616_, 3);
v_size_618_ = lean_ctor_get(v_acc_589_, 0);
lean_inc(v_size_618_);
v___x_619_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_589_, v_size_618_, v_index_617_, v_val_608_, v_val_609_);
lean_dec(v_index_617_);
v___y_592_ = v___x_619_;
goto v___jp_591_;
}
case 1:
{
lean_object* v_index_620_; 
v_index_620_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_index_620_);
lean_dec_ref_known(v___x_616_, 1);
v_i_611_ = v_index_620_;
goto v___jp_610_;
}
default: 
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_589_, v___x_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_index_623_; 
v_index_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_index_623_);
lean_dec_ref_known(v___x_622_, 1);
v_i_611_ = v_index_623_;
goto v___jp_610_;
}
else
{
lean_dec(v_val_609_);
lean_dec(v_val_608_);
v___y_592_ = v_acc_589_;
goto v___jp_591_;
}
}
}
v___jp_610_:
{
lean_object* v_size_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_size_612_ = lean_ctor_get(v_acc_589_, 0);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_size_612_, v___x_613_);
v___x_615_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_589_, v___x_614_, v_i_611_, v_val_608_, v_val_609_);
lean_dec(v_i_611_);
v___y_592_ = v___x_615_;
goto v___jp_591_;
}
}
}
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_i_590_, v___x_593_);
lean_dec(v_i_590_);
v_acc_589_ = v___y_592_;
v_i_590_ = v___x_594_;
goto _start;
}
v___jp_596_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_i_590_, v___x_597_);
lean_dec(v_i_590_);
v_i_590_ = v___x_598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_b_624_, lean_object* v_acc_625_, lean_object* v_i_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg(v_b_624_, v_acc_625_, v_i_626_);
lean_dec_ref(v_b_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg(lean_object* v_init_628_, lean_object* v_b_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg(v_b_629_, v_init_628_, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg___boxed(lean_object* v_init_632_, lean_object* v_b_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg(v_init_632_, v_b_633_);
lean_dec_ref(v_b_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(lean_object* v_m_635_){
_start:
{
lean_object* v_keyArray_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_cellCount_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_target_643_; lean_object* v___x_644_; 
v_keyArray_636_ = lean_ctor_get(v_m_635_, 1);
v___x_637_ = lean_array_get_size(v_keyArray_636_);
v___x_638_ = lean_unsigned_to_nat(2u);
v_cellCount_639_ = lean_nat_mul(v___x_637_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_639_);
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_639_);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_639_);
v_target_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_643_, 0, v___x_640_);
lean_ctor_set(v_target_643_, 1, v___x_641_);
lean_ctor_set(v_target_643_, 2, v___x_642_);
v___x_644_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg(v_target_643_, v_m_635_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg___boxed(lean_object* v_m_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(v_m_645_);
lean_dec_ref(v_m_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_stage_u2081_650_; lean_object* v_map_u2081_651_; lean_object* v_map_u2082_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_732_; 
v_stage_u2081_650_ = lean_ctor_get_uint8(v_x_647_, sizeof(void*)*2);
v_map_u2081_651_ = lean_ctor_get(v_x_647_, 0);
v_map_u2082_652_ = lean_ctor_get(v_x_647_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_732_ == 0)
{
v___x_654_ = v_x_647_;
v_isShared_655_ = v_isSharedCheck_732_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_map_u2082_652_);
lean_inc(v_map_u2081_651_);
lean_dec(v_x_647_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_732_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___y_657_; lean_object* v_i_658_; lean_object* v___y_667_; lean_object* v___y_679_; lean_object* v_i_680_; 
if (v_stage_u2081_650_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_del_object(v___x_654_);
v___x_698_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2082_652_, v_x_648_, v_x_649_);
v___x_699_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_699_, 0, v_map_u2081_651_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2081_651_, v_x_648_);
switch(lean_obj_tag(v___x_700_))
{
case 0:
{
lean_object* v_index_701_; lean_object* v_size_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_del_object(v___x_654_);
v_index_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_index_701_);
lean_dec_ref_known(v___x_700_, 3);
v_size_702_ = lean_ctor_get(v_map_u2081_651_, 0);
lean_inc(v_size_702_);
v___x_703_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_651_, v_size_702_, v_index_701_, v_x_648_, v_x_649_);
lean_dec(v_index_701_);
v___x_704_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_704_;
}
case 1:
{
lean_object* v_index_705_; lean_object* v_size_706_; lean_object* v_keyArray_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
lean_del_object(v___x_654_);
v_index_705_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_index_705_);
lean_dec_ref_known(v___x_700_, 1);
v_size_706_ = lean_ctor_get(v_map_u2081_651_, 0);
v_keyArray_707_ = lean_ctor_get(v_map_u2081_651_, 1);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_size_706_, v___x_708_);
v___x_710_ = lean_array_get_size(v_keyArray_707_);
v___x_711_ = lean_nat_dec_lt(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_dec(v___x_709_);
lean_dec(v_index_705_);
goto v___jp_686_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_712_ = lean_unsigned_to_nat(4u);
v___x_713_ = lean_nat_mul(v___x_709_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(3u);
v___x_715_ = lean_nat_mul(v___x_710_, v___x_714_);
v___x_716_ = lean_nat_dec_le(v___x_713_, v___x_715_);
lean_dec(v___x_715_);
lean_dec(v___x_713_);
if (v___x_716_ == 0)
{
lean_dec(v___x_709_);
lean_dec(v_index_705_);
goto v___jp_686_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_651_, v___x_709_, v_index_705_, v_x_648_, v_x_649_);
lean_dec(v_index_705_);
v___x_718_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_718_;
}
}
}
default: 
{
lean_object* v_size_719_; lean_object* v_keyArray_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_size_719_ = lean_ctor_get(v_map_u2081_651_, 0);
v_keyArray_720_ = lean_ctor_get(v_map_u2081_651_, 1);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_size_719_, v___x_721_);
v___x_723_ = lean_array_get_size(v_keyArray_720_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v___x_722_);
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(v_map_u2081_651_);
lean_dec_ref(v_map_u2081_651_);
v___y_667_ = v___x_725_;
goto v___jp_666_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_726_ = lean_unsigned_to_nat(4u);
v___x_727_ = lean_nat_mul(v___x_722_, v___x_726_);
lean_dec(v___x_722_);
v___x_728_ = lean_unsigned_to_nat(3u);
v___x_729_ = lean_nat_mul(v___x_723_, v___x_728_);
v___x_730_ = lean_nat_dec_le(v___x_727_, v___x_729_);
lean_dec(v___x_729_);
lean_dec(v___x_727_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(v_map_u2081_651_);
lean_dec_ref(v_map_u2081_651_);
v___y_667_ = v___x_731_;
goto v___jp_666_;
}
else
{
v___y_667_ = v_map_u2081_651_;
goto v___jp_666_;
}
}
}
}
}
v___jp_656_:
{
lean_object* v_size_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v_size_659_ = lean_ctor_get(v___y_657_, 0);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_size_659_, v___x_660_);
v___x_662_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_657_, v___x_661_, v_i_658_, v_x_648_, v_x_649_);
lean_dec(v_i_658_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_662_);
v___x_664_ = v___x_654_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v_reuseFailAlloc_665_, sizeof(void*)*2, v_stage_u2081_650_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
v___jp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v___y_667_, v_x_648_);
switch(lean_obj_tag(v___x_668_))
{
case 0:
{
lean_object* v_index_669_; lean_object* v_size_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_654_);
v_index_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_index_669_);
lean_dec_ref_known(v___x_668_, 3);
v_size_670_ = lean_ctor_get(v___y_667_, 0);
lean_inc(v_size_670_);
v___x_671_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_667_, v_size_670_, v_index_669_, v_x_648_, v_x_649_);
lean_dec(v_index_669_);
v___x_672_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_672_;
}
case 1:
{
lean_object* v_index_673_; 
v_index_673_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_index_673_);
lean_dec_ref_known(v___x_668_, 1);
v___y_657_ = v___y_667_;
v_i_658_ = v_index_673_;
goto v___jp_656_;
}
default: 
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_667_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_index_676_; 
v_index_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_index_676_);
lean_dec_ref_known(v___x_675_, 1);
v___y_657_ = v___y_667_;
v_i_658_ = v_index_676_;
goto v___jp_656_;
}
else
{
lean_object* v___x_677_; 
lean_del_object(v___x_654_);
lean_dec(v_x_649_);
lean_dec(v_x_648_);
v___x_677_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_677_, 0, v___y_667_);
lean_ctor_set(v___x_677_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_677_;
}
}
}
}
v___jp_678_:
{
lean_object* v_size_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_size_681_ = lean_ctor_get(v___y_679_, 0);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_size_681_, v___x_682_);
v___x_684_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_679_, v___x_683_, v_i_680_, v_x_648_, v_x_649_);
lean_dec(v_i_680_);
v___x_685_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_685_;
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(v_map_u2081_651_);
lean_dec_ref(v_map_u2081_651_);
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v___x_687_, v_x_648_);
switch(lean_obj_tag(v___x_688_))
{
case 0:
{
lean_object* v_index_689_; lean_object* v_size_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_index_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_index_689_);
lean_dec_ref_known(v___x_688_, 3);
v_size_690_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_size_690_);
v___x_691_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_687_, v_size_690_, v_index_689_, v_x_648_, v_x_649_);
lean_dec(v_index_689_);
v___x_692_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_692_;
}
case 1:
{
lean_object* v_index_693_; 
v_index_693_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_index_693_);
lean_dec_ref_known(v___x_688_, 1);
v___y_679_ = v___x_687_;
v_i_680_ = v_index_693_;
goto v___jp_678_;
}
default: 
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_687_, v___x_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_index_696_; 
v_index_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_695_, 1);
v___y_679_ = v___x_687_;
v_i_680_ = v_index_696_;
goto v___jp_678_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_x_649_);
lean_dec(v_x_648_);
v___x_697_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_697_, 0, v___x_687_);
lean_ctor_set(v___x_697_, 1, v_map_u2082_652_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*2, v_stage_u2081_650_);
return v___x_697_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(32u);
v___x_734_ = lean_mk_empty_array_with_capacity(v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = ((size_t)5ULL);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_unsigned_to_nat(32u);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_738_);
v___x_740_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_741_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_737_);
lean_ctor_set(v___x_741_, 3, v___x_737_);
lean_ctor_set_usize(v___x_741_, 4, v___x_736_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_742_, lean_object* v_ns_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_742_, v_ns_743_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_747_ = l_Lean_PersistentArray_push___redArg(v___x_746_, v_b_744_);
v___x_748_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_742_, v_ns_743_, v___x_747_);
return v___x_748_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_val_749_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v___x_745_, 1);
v___x_750_ = l_Lean_PersistentArray_push___redArg(v_val_749_, v_b_744_);
v___x_751_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_742_, v_ns_743_, v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_752_, lean_object* v_scopedEntries_753_, lean_object* v_ns_754_, lean_object* v_b_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_753_, v_ns_754_, v_b_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_761_, v_x_762_, v_x_763_);
lean_dec(v_x_763_);
lean_dec_ref(v_x_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_766_, v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_774_, v_x_775_, v_x_776_);
lean_dec(v_x_776_);
lean_dec_ref(v_x_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_778_, lean_object* v_m_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_779_, v_a_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_782_, lean_object* v_m_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_782_, v_m_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_m_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_786_, lean_object* v_m_787_, lean_object* v_query_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_m_787_, v_query_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___boxed(lean_object* v_00_u03b2_790_, lean_object* v_m_791_, lean_object* v_query_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(v_00_u03b2_790_, v_m_791_, v_query_792_);
lean_dec(v_query_792_);
lean_dec_ref(v_m_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_x_795_, v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5(lean_object* v_00_u03b2_799_, lean_object* v_m_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___redArg(v_m_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5___boxed(lean_object* v_00_u03b2_802_, lean_object* v_m_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5(v_00_u03b2_802_, v_m_803_);
lean_dec_ref(v_m_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, size_t v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_806_, v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_2080__boxed_814_; lean_object* v_res_815_; 
v_x_2080__boxed_814_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_815_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_810_, v_x_811_, v_x_2080__boxed_814_, v_x_813_);
lean_dec(v_x_813_);
lean_dec_ref(v_x_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_query_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_m_817_, v_query_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_820_, lean_object* v_m_821_, lean_object* v_query_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_820_, v_m_821_, v_query_822_);
lean_dec(v_query_822_);
lean_dec_ref(v_m_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_824_, lean_object* v_m_825_, lean_object* v_query_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_m_825_, v_query_826_, v_x_827_, v_x_828_, v_x_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_832_, lean_object* v_m_833_, lean_object* v_query_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_832_, v_m_833_, v_query_834_, v_x_835_, v_x_836_, v_x_837_, v_x_838_);
lean_dec(v_query_834_);
lean_dec_ref(v_m_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, size_t v_x_842_, size_t v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
size_t v_x_2107__boxed_853_; size_t v_x_2108__boxed_854_; lean_object* v_res_855_; 
v_x_2107__boxed_853_ = lean_unbox_usize(v_x_849_);
lean_dec(v_x_849_);
v_x_2108__boxed_854_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_res_855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_847_, v_x_848_, v_x_2107__boxed_853_, v_x_2108__boxed_854_, v_x_851_, v_x_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_856_, lean_object* v_init_857_, lean_object* v_b_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___redArg(v_init_857_, v_b_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10___boxed(lean_object* v_00_u03b2_860_, lean_object* v_init_861_, lean_object* v_b_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10(v_00_u03b2_860_, v_init_861_, v_b_862_);
lean_dec_ref(v_b_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_heq_867_, lean_object* v_i_868_, lean_object* v_k_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_865_, v_vals_866_, v_i_868_, v_k_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_heq_874_, lean_object* v_i_875_, lean_object* v_k_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_871_, v_keys_872_, v_vals_873_, v_heq_874_, v_i_875_, v_k_876_);
lean_dec(v_k_876_);
lean_dec_ref(v_vals_873_);
lean_dec_ref(v_keys_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b2_878_, lean_object* v_n_879_, lean_object* v_k_880_, lean_object* v_v_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10___redArg(v_n_879_, v_k_880_, v_v_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_883_, size_t v_depth_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_heq_887_, lean_object* v_i_888_, lean_object* v_entries_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___redArg(v_depth_884_, v_keys_885_, v_vals_886_, v_i_888_, v_entries_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11___boxed(lean_object* v_00_u03b2_891_, lean_object* v_depth_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_heq_895_, lean_object* v_i_896_, lean_object* v_entries_897_){
_start:
{
size_t v_depth_boxed_898_; lean_object* v_res_899_; 
v_depth_boxed_898_ = lean_unbox_usize(v_depth_892_);
lean_dec(v_depth_892_);
v_res_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__11(v_00_u03b2_891_, v_depth_boxed_898_, v_keys_893_, v_vals_894_, v_heq_895_, v_i_896_, v_entries_897_);
lean_dec_ref(v_vals_894_);
lean_dec_ref(v_keys_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14(lean_object* v_00_u03b2_900_, lean_object* v_b_901_, lean_object* v_acc_902_, lean_object* v_i_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___redArg(v_b_901_, v_acc_902_, v_i_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14___boxed(lean_object* v_00_u03b2_905_, lean_object* v_b_906_, lean_object* v_acc_907_, lean_object* v_i_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__5_spec__10_spec__14(v_00_u03b2_905_, v_b_906_, v_acc_907_, v_i_908_);
lean_dec_ref(v_b_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_spec__10_spec__12___redArg(v_x_911_, v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_916_, lean_object* v_as_917_, size_t v_sz_918_, size_t v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_a_924_; uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec_ref(v_descr_916_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_b_920_);
return v___x_929_;
}
else
{
lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_970_; 
v_fst_930_ = lean_ctor_get(v_b_920_, 0);
v_snd_931_ = lean_ctor_get(v_b_920_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_b_920_);
if (v_isSharedCheck_970_ == 0)
{
v___x_933_ = v_b_920_;
v_isShared_934_ = v_isSharedCheck_970_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v_b_920_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_970_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_a_935_; 
v_a_935_ = lean_array_uget_borrowed(v_as_917_, v_i_919_);
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v_a_936_; lean_object* v_ofOLeanEntry_937_; lean_object* v_addEntry_938_; lean_object* v___x_939_; 
v_a_936_ = lean_ctor_get(v_a_935_, 0);
v_ofOLeanEntry_937_ = lean_ctor_get(v_descr_916_, 2);
v_addEntry_938_ = lean_ctor_get(v_descr_916_, 4);
lean_inc_ref(v_ofOLeanEntry_937_);
lean_inc_ref(v___y_921_);
lean_inc(v_a_936_);
lean_inc(v_fst_930_);
v___x_939_ = lean_apply_4(v_ofOLeanEntry_937_, v_fst_930_, v_a_936_, v___y_921_, lean_box(0));
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
lean_inc(v_addEntry_938_);
v___x_941_ = lean_apply_2(v_addEntry_938_, v_fst_930_, v_a_940_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_941_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_snd_931_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
v_a_924_ = v___x_943_;
goto v___jp_923_;
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_del_object(v___x_933_);
lean_dec(v_snd_931_);
lean_dec(v_fst_930_);
lean_dec_ref(v_descr_916_);
v_a_945_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_939_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_939_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v_ofOLeanEntry_955_; lean_object* v___x_956_; 
v_a_953_ = lean_ctor_get(v_a_935_, 0);
v_a_954_ = lean_ctor_get(v_a_935_, 1);
v_ofOLeanEntry_955_ = lean_ctor_get(v_descr_916_, 2);
lean_inc_ref(v_ofOLeanEntry_955_);
lean_inc_ref(v___y_921_);
lean_inc(v_a_954_);
lean_inc(v_fst_930_);
v___x_956_ = lean_apply_4(v_ofOLeanEntry_955_, v_fst_930_, v_a_954_, v___y_921_, lean_box(0));
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
lean_inc(v_a_953_);
v___x_958_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_931_, v_a_953_, v_a_957_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_958_);
v___x_960_ = v___x_933_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fst_930_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v_a_924_ = v___x_960_;
goto v___jp_923_;
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_933_);
lean_dec(v_snd_931_);
lean_dec(v_fst_930_);
lean_dec_ref(v_descr_916_);
v_a_962_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_956_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_956_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
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
v___jp_923_:
{
size_t v___x_925_; size_t v___x_926_; 
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_919_, v___x_925_);
v_i_919_ = v___x_926_;
v_b_920_ = v_a_924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_971_, lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
size_t v_sz_boxed_978_; size_t v_i_boxed_979_; lean_object* v_res_980_; 
v_sz_boxed_978_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_979_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_971_, v_as_972_, v_sz_boxed_978_, v_i_boxed_979_, v_b_975_, v___y_976_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_981_, lean_object* v_as_982_, size_t v_sz_983_, size_t v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_lt(v_i_984_, v_sz_983_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_descr_981_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_b_985_);
return v___x_989_;
}
else
{
lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1015_; 
v_fst_990_ = lean_ctor_get(v_b_985_, 0);
v_snd_991_ = lean_ctor_get(v_b_985_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_b_985_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_993_ = v_b_985_;
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_snd_991_);
lean_inc(v_fst_990_);
lean_dec(v_b_985_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_a_995_; lean_object* v___x_997_; 
v_a_995_ = lean_array_uget_borrowed(v_as_982_, v_i_984_);
if (v_isShared_994_ == 0)
{
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_fst_990_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_991_);
v___x_997_ = v_reuseFailAlloc_1014_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
size_t v_sz_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v_sz_998_ = lean_array_size(v_a_995_);
v___x_999_ = ((size_t)0ULL);
lean_inc_ref(v_descr_981_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_981_, v_a_995_, v_sz_998_, v___x_999_, v___x_997_, v___y_986_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_fst_1002_; lean_object* v_snd_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1013_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v_fst_1002_ = lean_ctor_get(v_a_1001_, 0);
v_snd_1003_ = lean_ctor_get(v_a_1001_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_1001_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1005_ = v_a_1001_;
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_snd_1003_);
lean_inc(v_fst_1002_);
lean_dec(v_a_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_fst_1002_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_snd_1003_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_984_, v___x_1009_);
v_i_984_ = v___x_1010_;
v_b_985_ = v___x_1008_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_981_);
return v___x_1000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_1016_, lean_object* v_as_1017_, lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
size_t v_sz_boxed_1023_; size_t v_i_boxed_1024_; lean_object* v_res_1025_; 
v_sz_boxed_1023_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1024_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1016_, v_as_1017_, v_sz_boxed_1023_, v_i_boxed_1024_, v_b_1020_, v___y_1021_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_as_1017_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_1026_, lean_object* v_as_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_mkInitial_1030_; lean_object* v_finalizeImport_1031_; lean_object* v___x_1032_; 
v_mkInitial_1030_ = lean_ctor_get(v_descr_1026_, 1);
v_finalizeImport_1031_ = lean_ctor_get(v_descr_1026_, 5);
lean_inc(v_finalizeImport_1031_);
lean_inc_ref(v_mkInitial_1030_);
v___x_1032_ = lean_apply_1(v_mkInitial_1030_, lean_box(0));
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = 1;
v___x_1035_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__5);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_a_1033_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v_sz_1037_ = lean_array_size(v_as_1027_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1026_, v_as_1027_, v_sz_1037_, v___x_1038_, v___x_1036_, v_a_1028_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1061_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1061_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1061_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1060_; 
v_fst_1044_ = lean_ctor_get(v_a_1040_, 0);
v_snd_1045_ = lean_ctor_get(v_a_1040_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1047_ = v_a_1040_;
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_a_1040_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1049_ = lean_apply_1(v_finalizeImport_1031_, v_fst_1044_);
v___x_1050_ = l_Lean_NameSet_empty;
v___x_1051_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*2, v___x_1034_);
v___x_1052_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 1);
lean_ctor_set(v___x_1047_, 1, v___x_1052_);
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1054_ = v___x_1047_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_snd_1045_);
lean_ctor_set(v___x_1055_, 2, v___x_1052_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1055_);
v___x_1057_ = v___x_1042_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_finalizeImport_1031_);
v_a_1062_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1039_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1039_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_finalizeImport_1031_);
lean_dec_ref(v_descr_1026_);
v_a_1070_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1032_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1032_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1078_, lean_object* v_as_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1078_, v_as_1079_, v_a_1080_);
lean_dec_ref(v_a_1080_);
lean_dec_ref(v_as_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_00_u03c3_1085_, lean_object* v_descr_1086_, lean_object* v_as_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1086_, v_as_1087_, v_a_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_00_u03c3_1093_, lean_object* v_descr_1094_, lean_object* v_as_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1091_, v_00_u03b2_1092_, v_00_u03c3_1093_, v_descr_1094_, v_as_1095_, v_a_1096_);
lean_dec_ref(v_a_1096_);
lean_dec_ref(v_as_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03c3_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_descr_1102_, lean_object* v_as_1103_, size_t v_sz_1104_, size_t v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1102_, v_as_1103_, v_sz_1104_, v_i_1105_, v_b_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03c3_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_descr_1113_, lean_object* v_as_1114_, lean_object* v_sz_1115_, lean_object* v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
size_t v_sz_boxed_1120_; size_t v_i_boxed_1121_; lean_object* v_res_1122_; 
v_sz_boxed_1120_ = lean_unbox_usize(v_sz_1115_);
lean_dec(v_sz_1115_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_res_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1110_, v_00_u03c3_1111_, v_00_u03b2_1112_, v_descr_1113_, v_as_1114_, v_sz_boxed_1120_, v_i_boxed_1121_, v_b_1117_, v___y_1118_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1114_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_descr_1126_, lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1126_, v_as_1127_, v_sz_1128_, v_i_1129_, v_b_1130_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03c3_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_descr_1137_, lean_object* v_as_1138_, lean_object* v_sz_1139_, lean_object* v_i_1140_, lean_object* v_b_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1139_);
lean_dec(v_sz_1139_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1140_);
lean_dec(v_i_1140_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1134_, v_00_u03c3_1135_, v_00_u03b2_1136_, v_descr_1137_, v_as_1138_, v_sz_boxed_1144_, v_i_boxed_1145_, v_b_1141_, v___y_1142_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v_as_1138_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
if (lean_obj_tag(v_a_1149_) == 0)
{
lean_object* v___x_1151_; 
lean_dec(v_a_1148_);
lean_dec_ref(v_descr_1147_);
v___x_1151_ = l_List_reverse___redArg(v_a_1150_);
return v___x_1151_;
}
else
{
lean_object* v_head_1152_; lean_object* v_tail_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1173_; 
v_head_1152_ = lean_ctor_get(v_a_1149_, 0);
v_tail_1153_ = lean_ctor_get(v_a_1149_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1155_ = v_a_1149_;
v_isShared_1156_ = v_isSharedCheck_1173_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_tail_1153_);
lean_inc(v_head_1152_);
lean_dec(v_a_1149_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1173_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_addEntry_1157_; lean_object* v_state_1158_; lean_object* v_activeScopes_1159_; uint8_t v_delimitsLocal_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1172_; 
v_addEntry_1157_ = lean_ctor_get(v_descr_1147_, 4);
v_state_1158_ = lean_ctor_get(v_head_1152_, 0);
v_activeScopes_1159_ = lean_ctor_get(v_head_1152_, 1);
v_delimitsLocal_1160_ = lean_ctor_get_uint8(v_head_1152_, sizeof(void*)*2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_head_1152_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1162_ = v_head_1152_;
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_activeScopes_1159_);
lean_inc(v_state_1158_);
lean_dec(v_head_1152_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_inc(v_addEntry_1157_);
lean_inc(v_a_1148_);
v___x_1164_ = lean_apply_2(v_addEntry_1157_, v_state_1158_, v_a_1148_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_activeScopes_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*2, v_delimitsLocal_1160_);
v___x_1166_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_a_1150_);
lean_ctor_set(v___x_1155_, 0, v___x_1166_);
v___x_1168_ = v___x_1155_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_a_1150_);
v___x_1168_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v_a_1149_ = v_tail_1153_;
v_a_1150_ = v___x_1168_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1174_, lean_object* v_descr_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
if (lean_obj_tag(v_a_1177_) == 0)
{
lean_object* v___x_1179_; 
lean_dec(v_a_1176_);
lean_dec_ref(v_descr_1175_);
v___x_1179_ = l_List_reverse___redArg(v_a_1178_);
return v___x_1179_;
}
else
{
lean_object* v_head_1180_; lean_object* v_tail_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1206_; 
v_head_1180_ = lean_ctor_get(v_a_1177_, 0);
v_tail_1181_ = lean_ctor_get(v_a_1177_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1183_ = v_a_1177_;
v_isShared_1184_ = v_isSharedCheck_1206_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_tail_1181_);
lean_inc(v_head_1180_);
lean_dec(v_a_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1206_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___y_1186_; lean_object* v_state_1191_; lean_object* v_activeScopes_1192_; uint8_t v_delimitsLocal_1193_; uint8_t v___x_1194_; 
v_state_1191_ = lean_ctor_get(v_head_1180_, 0);
v_activeScopes_1192_ = lean_ctor_get(v_head_1180_, 1);
v_delimitsLocal_1193_ = lean_ctor_get_uint8(v_head_1180_, sizeof(void*)*2);
v___x_1194_ = l_Lean_NameSet_contains(v_activeScopes_1192_, v_a_1174_);
if (v___x_1194_ == 0)
{
v___y_1186_ = v_head_1180_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1203_; 
lean_inc(v_activeScopes_1192_);
lean_inc(v_state_1191_);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_head_1180_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; lean_object* v_unused_1205_; 
v_unused_1204_ = lean_ctor_get(v_head_1180_, 1);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_head_1180_, 0);
lean_dec(v_unused_1205_);
v___x_1196_ = v_head_1180_;
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v_head_1180_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_addEntry_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v_addEntry_1198_ = lean_ctor_get(v_descr_1175_, 4);
lean_inc(v_addEntry_1198_);
lean_inc(v_a_1176_);
v___x_1199_ = lean_apply_2(v_addEntry_1198_, v_state_1191_, v_a_1176_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_activeScopes_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1202_, sizeof(void*)*2, v_delimitsLocal_1193_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v___y_1186_ = v___x_1201_;
goto v___jp_1185_;
}
}
}
v___jp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_a_1178_);
lean_ctor_set(v___x_1183_, 0, v___y_1186_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___y_1186_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1178_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
v_a_1177_ = v_tail_1181_;
v_a_1178_ = v___x_1188_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1207_, lean_object* v_descr_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1207_, v_descr_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1213_, lean_object* v_s_1214_, lean_object* v_e_1215_){
_start:
{
if (lean_obj_tag(v_e_1215_) == 0)
{
lean_object* v_stateStack_1216_; lean_object* v_scopedEntries_1217_; lean_object* v_newEntries_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1238_; 
v_stateStack_1216_ = lean_ctor_get(v_s_1214_, 0);
v_scopedEntries_1217_ = lean_ctor_get(v_s_1214_, 1);
v_newEntries_1218_ = lean_ctor_get(v_s_1214_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_s_1214_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1220_ = v_s_1214_;
v_isShared_1221_ = v_isSharedCheck_1238_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_newEntries_1218_);
lean_inc(v_scopedEntries_1217_);
lean_inc(v_stateStack_1216_);
lean_dec(v_s_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1238_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1237_; 
v_a_1222_ = lean_ctor_get(v_e_1215_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_e_1215_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1224_ = v_e_1215_;
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v_e_1215_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_toOLeanEntry_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_toOLeanEntry_1226_ = lean_ctor_get(v_descr_1213_, 3);
lean_inc(v_toOLeanEntry_1226_);
v___x_1227_ = lean_box(0);
lean_inc(v_a_1222_);
v___x_1228_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1213_, v_a_1222_, v_stateStack_1216_, v___x_1227_);
v___x_1229_ = lean_apply_1(v_toOLeanEntry_1226_, v_a_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1229_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_newEntries_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v___x_1232_);
lean_ctor_set(v___x_1220_, 0, v___x_1228_);
v___x_1234_ = v___x_1220_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_scopedEntries_1217_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1239_; lean_object* v_scopedEntries_1240_; lean_object* v_newEntries_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1263_; 
v_stateStack_1239_ = lean_ctor_get(v_s_1214_, 0);
v_scopedEntries_1240_ = lean_ctor_get(v_s_1214_, 1);
v_newEntries_1241_ = lean_ctor_get(v_s_1214_, 2);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_s_1214_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1243_ = v_s_1214_;
v_isShared_1244_ = v_isSharedCheck_1263_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_newEntries_1241_);
lean_inc(v_scopedEntries_1240_);
lean_inc(v_stateStack_1239_);
lean_dec(v_s_1214_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1263_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_a_1245_; lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1262_; 
v_a_1245_ = lean_ctor_get(v_e_1215_, 0);
v_a_1246_ = lean_ctor_get(v_e_1215_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_e_1215_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1248_ = v_e_1215_;
v_isShared_1249_ = v_isSharedCheck_1262_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_inc(v_a_1245_);
lean_dec(v_e_1215_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1262_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_toOLeanEntry_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v_toOLeanEntry_1250_ = lean_ctor_get(v_descr_1213_, 3);
lean_inc(v_toOLeanEntry_1250_);
v___x_1251_ = lean_box(0);
lean_inc_n(v_a_1246_, 2);
v___x_1252_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1245_, v_descr_1213_, v_a_1246_, v_stateStack_1239_, v___x_1251_);
lean_inc(v_a_1245_);
v___x_1253_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1240_, v_a_1245_, v_a_1246_);
v___x_1254_ = lean_apply_1(v_toOLeanEntry_1250_, v_a_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___x_1254_);
v___x_1256_ = v___x_1248_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1245_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_newEntries_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 2, v___x_1257_);
lean_ctor_set(v___x_1243_, 1, v___x_1253_);
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1259_ = v___x_1243_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_00_u03c3_1266_, lean_object* v_descr_1267_, lean_object* v_s_1268_, lean_object* v_e_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1267_, v_s_1268_, v_e_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_00_u03b1_1273_, lean_object* v_descr_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1279_, lean_object* v_a_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_00_u03b1_1282_, lean_object* v_descr_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1280_, v_descr_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1288_, lean_object* v_a_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_00_u03b1_1291_, lean_object* v_descr_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1288_, v_a_1289_, v_00_u03b2_1290_, v_00_u03b1_1291_, v_descr_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1289_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1297_, lean_object* v_env_1298_, lean_object* v_as_1299_, size_t v_sz_1300_, size_t v_i_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v_a_1304_; uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1301_, v_sz_1300_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_env_1298_);
lean_dec_ref(v_descr_1297_);
return v_b_1302_;
}
else
{
lean_object* v_snd_1309_; lean_object* v_fst_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1410_; 
v_snd_1309_ = lean_ctor_get(v_b_1302_, 1);
v_fst_1310_ = lean_ctor_get(v_b_1302_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_b_1302_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1312_ = v_b_1302_;
v_isShared_1313_ = v_isSharedCheck_1410_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_snd_1309_);
lean_inc(v_fst_1310_);
lean_dec(v_b_1302_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1410_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1409_; 
v_fst_1314_ = lean_ctor_get(v_snd_1309_, 0);
v_snd_1315_ = lean_ctor_get(v_snd_1309_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_snd_1309_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1317_ = v_snd_1309_;
v_isShared_1318_ = v_isSharedCheck_1409_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_snd_1309_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1409_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_a_1319_; 
v_a_1319_ = lean_array_uget(v_as_1299_, v_i_1301_);
if (lean_obj_tag(v_a_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1369_; 
v_a_1320_ = lean_ctor_get(v_a_1319_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1322_ = v_a_1319_;
v_isShared_1323_ = v_isSharedCheck_1369_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v_a_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1369_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_exportEntry_x3f_1324_; lean_object* v___x_1325_; lean_object* v_exported_1326_; lean_object* v_server_1327_; lean_object* v_private_1328_; lean_object* v___y_1330_; lean_object* v_server_1331_; lean_object* v_exported_1350_; 
v_exportEntry_x3f_1324_ = lean_ctor_get(v_descr_1297_, 6);
lean_inc_ref(v_exportEntry_x3f_1324_);
lean_inc_ref(v_env_1298_);
v___x_1325_ = lean_apply_2(v_exportEntry_x3f_1324_, v_env_1298_, v_a_1320_);
v_exported_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_exported_1326_);
v_server_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_server_1327_);
v_private_1328_ = lean_ctor_get(v___x_1325_, 2);
lean_inc(v_private_1328_);
lean_dec_ref(v___x_1325_);
if (lean_obj_tag(v_exported_1326_) == 1)
{
lean_object* v_val_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_val_1360_ = lean_ctor_get(v_exported_1326_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_exported_1326_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v_exported_1326_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_val_1360_);
lean_dec(v_exported_1326_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 0);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_val_1360_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_array_push(v_fst_1310_, v___x_1365_);
v_exported_1350_ = v___x_1366_;
goto v___jp_1349_;
}
}
}
else
{
lean_dec(v_exported_1326_);
v_exported_1350_ = v_fst_1310_;
goto v___jp_1349_;
}
v___jp_1329_:
{
if (lean_obj_tag(v_private_1328_) == 1)
{
lean_object* v_val_1332_; lean_object* v___x_1334_; 
v_val_1332_ = lean_ctor_get(v_private_1328_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_private_1328_, 1);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_val_1332_);
v___x_1334_ = v___x_1322_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_val_1332_);
v___x_1334_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_array_push(v_snd_1315_, v___x_1334_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1335_);
lean_ctor_set(v___x_1317_, 0, v_server_1331_);
v___x_1337_ = v___x_1317_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_server_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1337_);
lean_ctor_set(v___x_1312_, 0, v___y_1330_);
v___x_1339_ = v___x_1312_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___y_1330_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
v_a_1304_ = v___x_1339_;
goto v___jp_1303_;
}
}
}
}
else
{
lean_object* v___x_1344_; 
lean_dec(v_private_1328_);
lean_del_object(v___x_1322_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_server_1331_);
v___x_1344_ = v___x_1317_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_server_1331_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1315_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1344_);
lean_ctor_set(v___x_1312_, 0, v___y_1330_);
v___x_1346_ = v___x_1312_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___y_1330_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v_a_1304_ = v___x_1346_;
goto v___jp_1303_;
}
}
}
}
v___jp_1349_:
{
if (lean_obj_tag(v_server_1327_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
v_val_1351_ = lean_ctor_get(v_server_1327_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_server_1327_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1353_ = v_server_1327_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v_server_1327_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1351_);
v___x_1356_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_array_push(v_fst_1314_, v___x_1356_);
v___y_1330_ = v_exported_1350_;
v_server_1331_ = v___x_1357_;
goto v___jp_1329_;
}
}
}
else
{
lean_dec(v_server_1327_);
v___y_1330_ = v_exported_1350_;
v_server_1331_ = v_fst_1314_;
goto v___jp_1329_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1408_; 
v_a_1370_ = lean_ctor_get(v_a_1319_, 0);
v_a_1371_ = lean_ctor_get(v_a_1319_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1373_ = v_a_1319_;
v_isShared_1374_ = v_isSharedCheck_1408_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_inc(v_a_1370_);
lean_dec(v_a_1319_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1408_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_exportEntry_x3f_1375_; lean_object* v___x_1376_; lean_object* v_exported_1377_; lean_object* v_server_1378_; lean_object* v_private_1379_; lean_object* v___y_1381_; lean_object* v_server_1382_; lean_object* v_exported_1401_; 
v_exportEntry_x3f_1375_ = lean_ctor_get(v_descr_1297_, 6);
lean_inc_ref(v_exportEntry_x3f_1375_);
lean_inc_ref(v_env_1298_);
v___x_1376_ = lean_apply_2(v_exportEntry_x3f_1375_, v_env_1298_, v_a_1371_);
v_exported_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_exported_1377_);
v_server_1378_ = lean_ctor_get(v___x_1376_, 1);
lean_inc(v_server_1378_);
v_private_1379_ = lean_ctor_get(v___x_1376_, 2);
lean_inc(v_private_1379_);
lean_dec_ref(v___x_1376_);
if (lean_obj_tag(v_exported_1377_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_val_1405_ = lean_ctor_get(v_exported_1377_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v_exported_1377_, 1);
lean_inc(v_a_1370_);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_a_1370_);
lean_ctor_set(v___x_1406_, 1, v_val_1405_);
v___x_1407_ = lean_array_push(v_fst_1310_, v___x_1406_);
v_exported_1401_ = v___x_1407_;
goto v___jp_1400_;
}
else
{
lean_dec(v_exported_1377_);
v_exported_1401_ = v_fst_1310_;
goto v___jp_1400_;
}
v___jp_1380_:
{
if (lean_obj_tag(v_private_1379_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1385_; 
v_val_1383_ = lean_ctor_get(v_private_1379_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_private_1379_, 1);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_val_1383_);
v___x_1385_ = v___x_1373_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1370_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_val_1383_);
v___x_1385_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = lean_array_push(v_snd_1315_, v___x_1385_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1386_);
lean_ctor_set(v___x_1317_, 0, v_server_1382_);
v___x_1388_ = v___x_1317_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_server_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1388_);
lean_ctor_set(v___x_1312_, 0, v___y_1381_);
v___x_1390_ = v___x_1312_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___y_1381_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v_a_1304_ = v___x_1390_;
goto v___jp_1303_;
}
}
}
}
else
{
lean_object* v___x_1395_; 
lean_dec(v_private_1379_);
lean_del_object(v___x_1373_);
lean_dec(v_a_1370_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_server_1382_);
v___x_1395_ = v___x_1317_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_server_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_snd_1315_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1395_);
lean_ctor_set(v___x_1312_, 0, v___y_1381_);
v___x_1397_ = v___x_1312_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___y_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v_a_1304_ = v___x_1397_;
goto v___jp_1303_;
}
}
}
}
v___jp_1400_:
{
if (lean_obj_tag(v_server_1378_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_val_1402_ = lean_ctor_get(v_server_1378_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_server_1378_, 1);
lean_inc(v_a_1370_);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_a_1370_);
lean_ctor_set(v___x_1403_, 1, v_val_1402_);
v___x_1404_ = lean_array_push(v_fst_1314_, v___x_1403_);
v___y_1381_ = v_exported_1401_;
v_server_1382_ = v___x_1404_;
goto v___jp_1380_;
}
else
{
lean_dec(v_server_1378_);
v___y_1381_ = v_exported_1401_;
v_server_1382_ = v_fst_1314_;
goto v___jp_1380_;
}
}
}
}
}
}
}
v___jp_1303_:
{
size_t v___x_1305_; size_t v___x_1306_; 
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1301_, v___x_1305_);
v_i_1301_ = v___x_1306_;
v_b_1302_ = v_a_1304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1411_, lean_object* v_env_1412_, lean_object* v_as_1413_, lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_b_1416_){
_start:
{
size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1411_, v_env_1412_, v_as_1413_, v_sz_boxed_1417_, v_i_boxed_1418_, v_b_1416_);
lean_dec_ref(v_as_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1427_, lean_object* v_env_1428_, lean_object* v_s_1429_){
_start:
{
lean_object* v_newEntries_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1447_; 
v_newEntries_1430_ = lean_ctor_get(v_s_1429_, 2);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_s_1429_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1448_ = lean_ctor_get(v_s_1429_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_s_1429_, 0);
lean_dec(v_unused_1449_);
v___x_1432_ = v_s_1429_;
v_isShared_1433_ = v_isSharedCheck_1447_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_newEntries_1430_);
lean_dec(v_s_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1447_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; size_t v_sz_1437_; size_t v___x_1438_; lean_object* v___x_1439_; lean_object* v_snd_1440_; lean_object* v_fst_1441_; lean_object* v_fst_1442_; lean_object* v_snd_1443_; lean_object* v___x_1445_; 
v___x_1434_ = lean_array_mk(v_newEntries_1430_);
v___x_1435_ = l_Array_reverse___redArg(v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1437_ = lean_array_size(v___x_1435_);
v___x_1438_ = ((size_t)0ULL);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1427_, v_env_1428_, v___x_1435_, v_sz_1437_, v___x_1438_, v___x_1436_);
lean_dec_ref(v___x_1435_);
v_snd_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_snd_1440_);
v_fst_1441_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_fst_1441_);
lean_dec_ref(v___x_1439_);
v_fst_1442_ = lean_ctor_get(v_snd_1440_, 0);
lean_inc(v_fst_1442_);
v_snd_1443_ = lean_ctor_get(v_snd_1440_, 1);
lean_inc(v_snd_1443_);
lean_dec(v_snd_1440_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v_snd_1443_);
lean_ctor_set(v___x_1432_, 1, v_fst_1442_);
lean_ctor_set(v___x_1432_, 0, v_fst_1441_);
v___x_1445_ = v___x_1432_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_fst_1441_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_fst_1442_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_snd_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_00_u03c3_1452_, lean_object* v_descr_1453_, lean_object* v_env_1454_, lean_object* v_s_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1453_, v_env_1454_, v_s_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_00_u03c3_1459_, lean_object* v_descr_1460_, lean_object* v_env_1461_, lean_object* v_as_1462_, size_t v_sz_1463_, size_t v_i_1464_, lean_object* v_b_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1460_, v_env_1461_, v_as_1462_, v_sz_1463_, v_i_1464_, v_b_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1467_, lean_object* v_00_u03b2_1468_, lean_object* v_00_u03c3_1469_, lean_object* v_descr_1470_, lean_object* v_env_1471_, lean_object* v_as_1472_, lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_b_1475_){
_start:
{
size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1467_, v_00_u03b2_1468_, v_00_u03c3_1469_, v_descr_1470_, v_env_1471_, v_as_1472_, v_sz_boxed_1476_, v_i_boxed_1477_, v_b_1475_);
lean_dec_ref(v_as_1472_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1484_, v___y_1485_);
lean_dec_ref(v___y_1485_);
lean_dec_ref(v_x_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1488_, lean_object* v_x_1489_){
_start:
{
lean_inc_ref(v_s_1488_);
return v_s_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1490_, v_x_1491_);
lean_dec_ref(v_x_1491_);
lean_dec_ref(v_s_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1498_, v_x_1499_);
lean_dec_ref(v_x_1499_);
lean_dec_ref(v_x_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1503_);
lean_dec_ref(v_x_1503_);
return v_res_1504_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___f_1510_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1511_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1512_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1513_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1516_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1514_);
lean_ctor_set(v___x_1516_, 2, v___f_1513_);
lean_ctor_set(v___x_1516_, 3, v___f_1512_);
lean_ctor_set(v___x_1516_, 4, v___f_1511_);
lean_ctor_set(v___x_1516_, 5, v___f_1510_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1517_){
_start:
{
lean_object* v___f_1518_; lean_object* v___f_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___f_1518_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1519_, 0, v_inst_1517_);
v___f_1520_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1521_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1524_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1525_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
lean_ctor_set(v___x_1525_, 2, v___f_1518_);
lean_ctor_set(v___x_1525_, 3, v___f_1519_);
lean_ctor_set(v___x_1525_, 4, v___f_1520_);
lean_ctor_set(v___x_1525_, 5, v___x_1524_);
lean_ctor_set(v___x_1525_, 6, v___f_1521_);
v___x_1526_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_00_u03c3_1530_, lean_object* v_inst_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1535_, lean_object* v_inst_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1544_ = lean_st_mk_ref(v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1551_){
_start:
{
lean_object* v_newEntries_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_newEntries_1552_ = lean_ctor_get(v_s_1551_, 2);
v___x_1553_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1554_ = l_List_lengthTR___redArg(v_newEntries_1552_);
v___x_1555_ = l_Nat_reprFast(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1553_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1558_);
lean_dec_ref(v_s_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1562_);
lean_dec_ref(v_x_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1566_){
_start:
{
lean_object* v_name_1568_; lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_name_1568_ = lean_ctor_get(v_descr_1566_, 0);
v___f_1569_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1570_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1566_, 4);
v___x_1571_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1571_, 0, lean_box(0));
lean_closure_set(v___x_1571_, 1, lean_box(0));
lean_closure_set(v___x_1571_, 2, lean_box(0));
lean_closure_set(v___x_1571_, 3, v_descr_1566_);
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1572_, 0, lean_box(0));
lean_closure_set(v___x_1572_, 1, lean_box(0));
lean_closure_set(v___x_1572_, 2, lean_box(0));
lean_closure_set(v___x_1572_, 3, v_descr_1566_);
v___x_1573_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1573_, 0, lean_box(0));
lean_closure_set(v___x_1573_, 1, lean_box(0));
lean_closure_set(v___x_1573_, 2, lean_box(0));
lean_closure_set(v___x_1573_, 3, v_descr_1566_);
v___x_1574_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1574_, 0, lean_box(0));
lean_closure_set(v___x_1574_, 1, lean_box(0));
lean_closure_set(v___x_1574_, 2, lean_box(0));
lean_closure_set(v___x_1574_, 3, v_descr_1566_);
v___x_1575_ = lean_box(2);
v___x_1576_ = lean_box(0);
lean_inc(v_name_1568_);
v___x_1577_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1577_, 0, v_name_1568_);
lean_ctor_set(v___x_1577_, 1, v___x_1571_);
lean_ctor_set(v___x_1577_, 2, v___x_1572_);
lean_ctor_set(v___x_1577_, 3, v___x_1573_);
lean_ctor_set(v___x_1577_, 4, v___x_1574_);
lean_ctor_set(v___x_1577_, 5, v___f_1569_);
lean_ctor_set(v___x_1577_, 6, v___x_1575_);
lean_ctor_set(v___x_1577_, 7, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___f_1570_);
v___x_1579_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1592_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1592_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1592_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1584_ = l_Lean_scopedEnvExtensionsRef;
v___x_1585_ = lean_st_ref_take(v___x_1584_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_descr_1566_);
lean_ctor_set(v___x_1586_, 1, v_a_1580_);
lean_inc_ref(v___x_1586_);
v___x_1587_ = lean_array_push(v___x_1585_, v___x_1586_);
v___x_1588_ = lean_st_ref_put(v___x_1584_, v___x_1587_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1586_);
v___x_1590_ = v___x_1582_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1586_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_descr_1566_);
v_a_1593_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1579_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1579_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1604_, lean_object* v_00_u03b2_1605_, lean_object* v_00_u03c3_1606_, lean_object* v_descr_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_00_u03c3_1612_, lean_object* v_descr_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1610_, v_00_u03b2_1611_, v_00_u03c3_1612_, v_descr_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1616_){
_start:
{
lean_object* v_stateStack_1617_; 
v_stateStack_1617_ = lean_ctor_get(v_s_1616_, 0);
if (lean_obj_tag(v_stateStack_1617_) == 0)
{
return v_s_1616_;
}
else
{
lean_object* v_head_1618_; lean_object* v_scopedEntries_1619_; lean_object* v_newEntries_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1638_; 
lean_inc_ref(v_stateStack_1617_);
v_head_1618_ = lean_ctor_get(v_stateStack_1617_, 0);
lean_inc(v_head_1618_);
v_scopedEntries_1619_ = lean_ctor_get(v_s_1616_, 1);
v_newEntries_1620_ = lean_ctor_get(v_s_1616_, 2);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_s_1616_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_s_1616_, 0);
lean_dec(v_unused_1639_);
v___x_1622_ = v_s_1616_;
v_isShared_1623_ = v_isSharedCheck_1638_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_newEntries_1620_);
lean_inc(v_scopedEntries_1619_);
lean_dec(v_s_1616_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1638_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_state_1624_; lean_object* v_activeScopes_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1637_; 
v_state_1624_ = lean_ctor_get(v_head_1618_, 0);
v_activeScopes_1625_ = lean_ctor_get(v_head_1618_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_head_1618_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1627_ = v_head_1618_;
v_isShared_1628_ = v_isSharedCheck_1637_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_activeScopes_1625_);
lean_inc(v_state_1624_);
lean_dec(v_head_1618_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1637_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = 1;
if (v_isShared_1628_ == 0)
{
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_state_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_activeScopes_1625_);
v___x_1631_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*2, v___x_1629_);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_stateStack_1617_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1632_);
v___x_1634_ = v___x_1622_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_scopedEntries_1619_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_newEntries_1620_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1641_, lean_object* v_env_1642_){
_start:
{
lean_object* v_ext_1643_; lean_object* v___f_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_ext_1643_ = lean_ctor_get(v_ext_1641_, 1);
lean_inc_ref(v_ext_1643_);
lean_dec_ref(v_ext_1641_);
v___f_1644_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1645_ = lean_box(1);
v___x_1646_ = lean_box(0);
v___x_1647_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1643_, v_env_1642_, v___f_1644_, v___x_1645_, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_00_u03c3_1650_, lean_object* v_ext_1651_, lean_object* v_env_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1651_, v_env_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1654_){
_start:
{
lean_object* v_stateStack_1655_; 
v_stateStack_1655_ = lean_ctor_get(v_s_1654_, 0);
if (lean_obj_tag(v_stateStack_1655_) == 1)
{
lean_object* v_tail_1656_; 
v_tail_1656_ = lean_ctor_get(v_stateStack_1655_, 1);
if (lean_obj_tag(v_tail_1656_) == 1)
{
lean_object* v_scopedEntries_1657_; lean_object* v_newEntries_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_inc_ref(v_tail_1656_);
v_scopedEntries_1657_ = lean_ctor_get(v_s_1654_, 1);
v_newEntries_1658_ = lean_ctor_get(v_s_1654_, 2);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_s_1654_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_s_1654_, 0);
lean_dec(v_unused_1666_);
v___x_1660_ = v_s_1654_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_newEntries_1658_);
lean_inc(v_scopedEntries_1657_);
lean_dec(v_s_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v_tail_1656_);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_tail_1656_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_scopedEntries_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_newEntries_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
return v_s_1654_;
}
}
else
{
return v_s_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1668_, lean_object* v_env_1669_){
_start:
{
lean_object* v_ext_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_ext_1670_ = lean_ctor_get(v_ext_1668_, 1);
lean_inc_ref(v_ext_1670_);
lean_dec_ref(v_ext_1668_);
v___f_1671_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1672_ = lean_box(1);
v___x_1673_ = lean_box(0);
v___x_1674_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1670_, v_env_1669_, v___f_1671_, v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1675_, lean_object* v_00_u03b2_1676_, lean_object* v_00_u03c3_1677_, lean_object* v_ext_1678_, lean_object* v_env_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1678_, v_env_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_zero_1683_; uint8_t v_isZero_1684_; 
v_zero_1683_ = lean_unsigned_to_nat(0u);
v_isZero_1684_ = lean_nat_dec_eq(v_a_1681_, v_zero_1683_);
if (v_isZero_1684_ == 1)
{
return v_a_1682_;
}
else
{
if (lean_obj_tag(v_a_1682_) == 0)
{
return v_a_1682_;
}
else
{
lean_object* v_head_1685_; lean_object* v_tail_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1705_; 
v_head_1685_ = lean_ctor_get(v_a_1682_, 0);
v_tail_1686_ = lean_ctor_get(v_a_1682_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1682_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1688_ = v_a_1682_;
v_isShared_1689_ = v_isSharedCheck_1705_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_tail_1686_);
lean_inc(v_head_1685_);
lean_dec(v_a_1682_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1705_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_state_1690_; lean_object* v_activeScopes_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1704_; 
v_state_1690_ = lean_ctor_get(v_head_1685_, 0);
v_activeScopes_1691_ = lean_ctor_get(v_head_1685_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_head_1685_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1693_ = v_head_1685_;
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_activeScopes_1691_);
lean_inc(v_state_1690_);
lean_dec(v_head_1685_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_one_1695_; lean_object* v_n_1696_; lean_object* v___x_1698_; 
v_one_1695_ = lean_unsigned_to_nat(1u);
v_n_1696_ = lean_nat_sub(v_a_1681_, v_one_1695_);
if (v_isShared_1694_ == 0)
{
v___x_1698_ = v___x_1693_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_state_1690_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_activeScopes_1691_);
v___x_1698_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*2, v_isZero_1684_);
v___x_1699_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1696_, v_tail_1686_);
lean_dec(v_n_1696_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v___x_1699_);
lean_ctor_set(v___x_1688_, 0, v___x_1698_);
v___x_1701_ = v___x_1688_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1706_, v_a_1707_);
lean_dec(v_a_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1710_, v_a_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1717_, lean_object* v_s_1718_){
_start:
{
lean_object* v_stateStack_1719_; lean_object* v_scopedEntries_1720_; lean_object* v_newEntries_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1729_; 
v_stateStack_1719_ = lean_ctor_get(v_s_1718_, 0);
v_scopedEntries_1720_ = lean_ctor_get(v_s_1718_, 1);
v_newEntries_1721_ = lean_ctor_get(v_s_1718_, 2);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_s_1718_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1723_ = v_s_1718_;
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_newEntries_1721_);
lean_inc(v_scopedEntries_1720_);
lean_inc(v_stateStack_1719_);
lean_dec(v_s_1718_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1729_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1717_, v_stateStack_1719_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_scopedEntries_1720_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_newEntries_1721_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1730_, lean_object* v_s_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1730_, v_s_1731_);
lean_dec(v_depth_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1733_, lean_object* v_env_1734_, lean_object* v_depth_1735_){
_start:
{
lean_object* v_ext_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_ext_1736_ = lean_ctor_get(v_ext_1733_, 1);
lean_inc_ref(v_ext_1736_);
lean_dec_ref(v_ext_1733_);
v___f_1737_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1737_, 0, v_depth_1735_);
v___x_1738_ = lean_box(1);
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1736_, v_env_1734_, v___f_1737_, v___x_1738_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_00_u03c3_1743_, lean_object* v_ext_1744_, lean_object* v_env_1745_, lean_object* v_depth_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1744_, v_env_1745_, v_depth_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1748_, lean_object* v_env_1749_, lean_object* v_b_1750_){
_start:
{
lean_object* v_ext_1751_; lean_object* v_toEnvExtension_1752_; lean_object* v_asyncMode_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_ext_1751_ = lean_ctor_get(v_ext_1748_, 1);
lean_inc_ref(v_ext_1751_);
lean_dec_ref(v_ext_1748_);
v_toEnvExtension_1752_ = lean_ctor_get(v_ext_1751_, 0);
v_asyncMode_1753_ = lean_ctor_get(v_toEnvExtension_1752_, 2);
lean_inc(v_asyncMode_1753_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_b_1750_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1751_, v_env_1749_, v___x_1754_, v_asyncMode_1753_, v___x_1755_);
lean_dec(v_asyncMode_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_00_u03c3_1759_, lean_object* v_ext_1760_, lean_object* v_env_1761_, lean_object* v_b_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1760_, v_env_1761_, v_b_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1764_, lean_object* v_env_1765_, lean_object* v_namespaceName_1766_, lean_object* v_b_1767_){
_start:
{
lean_object* v_ext_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1779_; 
v_ext_1768_ = lean_ctor_get(v_ext_1764_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_ext_1764_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_ext_1764_, 0);
lean_dec(v_unused_1780_);
v___x_1770_ = v_ext_1764_;
v_isShared_1771_ = v_isSharedCheck_1779_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_ext_1768_);
lean_dec(v_ext_1764_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1779_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_toEnvExtension_1772_; lean_object* v_asyncMode_1773_; lean_object* v___x_1775_; 
v_toEnvExtension_1772_ = lean_ctor_get(v_ext_1768_, 0);
v_asyncMode_1773_ = lean_ctor_get(v_toEnvExtension_1772_, 2);
lean_inc(v_asyncMode_1773_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
lean_ctor_set(v___x_1770_, 1, v_b_1767_);
lean_ctor_set(v___x_1770_, 0, v_namespaceName_1766_);
v___x_1775_ = v___x_1770_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_namespaceName_1766_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_b_1767_);
v___x_1775_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1768_, v_env_1765_, v___x_1775_, v_asyncMode_1773_, v___x_1776_);
lean_dec(v_asyncMode_1773_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1781_, lean_object* v_00_u03b2_1782_, lean_object* v_00_u03c3_1783_, lean_object* v_ext_1784_, lean_object* v_env_1785_, lean_object* v_namespaceName_1786_, lean_object* v_b_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1784_, v_env_1785_, v_namespaceName_1786_, v_b_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1789_, lean_object* v_states_1790_, lean_object* v_b_1791_){
_start:
{
if (lean_obj_tag(v_states_1790_) == 0)
{
lean_dec(v_b_1791_);
lean_dec_ref(v_ext_1789_);
return v_states_1790_;
}
else
{
lean_object* v_descr_1792_; lean_object* v_head_1793_; lean_object* v_tail_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1817_; 
v_descr_1792_ = lean_ctor_get(v_ext_1789_, 0);
v_head_1793_ = lean_ctor_get(v_states_1790_, 0);
v_tail_1794_ = lean_ctor_get(v_states_1790_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_states_1790_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1796_ = v_states_1790_;
v_isShared_1797_ = v_isSharedCheck_1817_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_tail_1794_);
lean_inc(v_head_1793_);
lean_dec(v_states_1790_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1817_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_addEntry_1798_; lean_object* v_state_1799_; lean_object* v_activeScopes_1800_; uint8_t v_delimitsLocal_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1816_; 
v_addEntry_1798_ = lean_ctor_get(v_descr_1792_, 4);
v_state_1799_ = lean_ctor_get(v_head_1793_, 0);
v_activeScopes_1800_ = lean_ctor_get(v_head_1793_, 1);
v_delimitsLocal_1801_ = lean_ctor_get_uint8(v_head_1793_, sizeof(void*)*2);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_head_1793_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1803_ = v_head_1793_;
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_activeScopes_1800_);
lean_inc(v_state_1799_);
lean_dec(v_head_1793_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v_top_1807_; 
lean_inc(v_addEntry_1798_);
lean_inc(v_b_1791_);
v___x_1805_ = lean_apply_2(v_addEntry_1798_, v_state_1799_, v_b_1791_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v_top_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_activeScopes_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1815_, sizeof(void*)*2, v_delimitsLocal_1801_);
v_top_1807_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
if (v_delimitsLocal_1801_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = l_Lean_stateStackModify___redArg(v_ext_1789_, v_tail_1794_, v_b_1791_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1808_);
lean_ctor_set(v___x_1796_, 0, v_top_1807_);
v___x_1810_ = v___x_1796_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_top_1807_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
lean_object* v___x_1813_; 
lean_dec(v_b_1791_);
lean_dec_ref(v_ext_1789_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v_top_1807_);
v___x_1813_ = v___x_1796_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_top_1807_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_tail_1794_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_00_u03c3_1820_, lean_object* v_ext_1821_, lean_object* v_states_1822_, lean_object* v_b_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_stateStackModify___redArg(v_ext_1821_, v_states_1822_, v_b_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1825_, lean_object* v_b_1826_, lean_object* v_s_1827_){
_start:
{
lean_object* v_stateStack_1828_; lean_object* v_scopedEntries_1829_; lean_object* v_newEntries_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
v_stateStack_1828_ = lean_ctor_get(v_s_1827_, 0);
v_scopedEntries_1829_ = lean_ctor_get(v_s_1827_, 1);
v_newEntries_1830_ = lean_ctor_get(v_s_1827_, 2);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_s_1827_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v_s_1827_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_newEntries_1830_);
lean_inc(v_scopedEntries_1829_);
lean_inc(v_stateStack_1828_);
lean_dec(v_s_1827_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = l_Lean_stateStackModify___redArg(v_ext_1825_, v_stateStack_1828_, v_b_1826_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_scopedEntries_1829_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_newEntries_1830_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1839_, lean_object* v_env_1840_, lean_object* v_b_1841_){
_start:
{
lean_object* v_ext_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_ext_1842_ = lean_ctor_get(v_ext_1839_, 1);
lean_inc_ref(v_ext_1842_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1843_, 0, v_ext_1839_);
lean_closure_set(v___f_1843_, 1, v_b_1841_);
v___x_1844_ = lean_box(1);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1842_, v_env_1840_, v___f_1843_, v___x_1844_, v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_00_u03c3_1849_, lean_object* v_ext_1850_, lean_object* v_env_1851_, lean_object* v_b_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1850_, v_env_1851_, v_b_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1854_, lean_object* v_ext_1855_, lean_object* v_b_1856_, uint8_t v_kind_1857_, lean_object* v_namespaceName_1858_){
_start:
{
switch(v_kind_1857_)
{
case 0:
{
lean_object* v___x_1859_; 
lean_dec(v_namespaceName_1858_);
v___x_1859_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1855_, v_env_1854_, v_b_1856_);
return v___x_1859_;
}
case 1:
{
lean_object* v___x_1860_; 
lean_dec(v_namespaceName_1858_);
v___x_1860_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1855_, v_env_1854_, v_b_1856_);
return v___x_1860_;
}
default: 
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1855_, v_env_1854_, v_namespaceName_1858_, v_b_1856_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1862_, lean_object* v_ext_1863_, lean_object* v_b_1864_, lean_object* v_kind_1865_, lean_object* v_namespaceName_1866_){
_start:
{
uint8_t v_kind_boxed_1867_; lean_object* v_res_1868_; 
v_kind_boxed_1867_ = lean_unbox(v_kind_1865_);
v_res_1868_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1862_, v_ext_1863_, v_b_1864_, v_kind_boxed_1867_, v_namespaceName_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_00_u03c3_1871_, lean_object* v_env_1872_, lean_object* v_ext_1873_, lean_object* v_b_1874_, uint8_t v_kind_1875_, lean_object* v_namespaceName_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1872_, v_ext_1873_, v_b_1874_, v_kind_1875_, v_namespaceName_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_00_u03b2_1879_, lean_object* v_00_u03c3_1880_, lean_object* v_env_1881_, lean_object* v_ext_1882_, lean_object* v_b_1883_, lean_object* v_kind_1884_, lean_object* v_namespaceName_1885_){
_start:
{
uint8_t v_kind_boxed_1886_; lean_object* v_res_1887_; 
v_kind_boxed_1886_ = lean_unbox(v_kind_1884_);
v_res_1887_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1878_, v_00_u03b2_1879_, v_00_u03c3_1880_, v_env_1881_, v_ext_1882_, v_b_1883_, v_kind_boxed_1886_, v_namespaceName_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1888_, lean_object* v_b_1889_, uint8_t v_kind_1890_, lean_object* v_ns_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1892_, v_ext_1888_, v_b_1889_, v_kind_1890_, v_ns_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1894_, lean_object* v_b_1895_, lean_object* v_kind_1896_, lean_object* v_ns_1897_, lean_object* v_x_1898_){
_start:
{
uint8_t v_kind_boxed_1899_; lean_object* v_res_1900_; 
v_kind_boxed_1899_ = lean_unbox(v_kind_1896_);
v_res_1900_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1894_, v_b_1895_, v_kind_boxed_1899_, v_ns_1897_, v_x_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1901_, lean_object* v_ext_1902_, lean_object* v_b_1903_, uint8_t v_kind_1904_, lean_object* v_ns_1905_){
_start:
{
lean_object* v_modifyEnv_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; 
v_modifyEnv_1906_ = lean_ctor_get(v_inst_1901_, 1);
lean_inc(v_modifyEnv_1906_);
lean_dec_ref(v_inst_1901_);
v___x_1907_ = lean_box(v_kind_1904_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1908_, 0, v_ext_1902_);
lean_closure_set(v___f_1908_, 1, v_b_1903_);
lean_closure_set(v___f_1908_, 2, v___x_1907_);
lean_closure_set(v___f_1908_, 3, v_ns_1905_);
v___x_1909_ = lean_apply_1(v_modifyEnv_1906_, v___f_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1910_, lean_object* v_ext_1911_, lean_object* v_b_1912_, lean_object* v_kind_1913_, lean_object* v_ns_1914_){
_start:
{
uint8_t v_kind_boxed_1915_; lean_object* v_res_1916_; 
v_kind_boxed_1915_ = lean_unbox(v_kind_1913_);
v_res_1916_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1910_, v_ext_1911_, v_b_1912_, v_kind_boxed_1915_, v_ns_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_ext_1920_, lean_object* v_b_1921_, uint8_t v_kind_1922_){
_start:
{
lean_object* v_toBind_1923_; lean_object* v_getCurrNamespace_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v_toBind_1923_ = lean_ctor_get(v_inst_1917_, 1);
lean_inc(v_toBind_1923_);
lean_dec_ref(v_inst_1917_);
v_getCurrNamespace_1924_ = lean_ctor_get(v_inst_1918_, 0);
lean_inc(v_getCurrNamespace_1924_);
lean_dec_ref(v_inst_1918_);
v___x_1925_ = lean_box(v_kind_1922_);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1926_, 0, v_inst_1919_);
lean_closure_set(v___f_1926_, 1, v_ext_1920_);
lean_closure_set(v___f_1926_, 2, v_b_1921_);
lean_closure_set(v___f_1926_, 3, v___x_1925_);
v___x_1927_ = lean_apply_4(v_toBind_1923_, lean_box(0), lean_box(0), v_getCurrNamespace_1924_, v___f_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_ext_1931_, lean_object* v_b_1932_, lean_object* v_kind_1933_){
_start:
{
uint8_t v_kind_boxed_1934_; lean_object* v_res_1935_; 
v_kind_boxed_1934_ = lean_unbox(v_kind_1933_);
v_res_1935_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1928_, v_inst_1929_, v_inst_1930_, v_ext_1931_, v_b_1932_, v_kind_boxed_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1936_, lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_00_u03c3_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_ext_1943_, lean_object* v_b_1944_, uint8_t v_kind_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1940_, v_inst_1941_, v_inst_1942_, v_ext_1943_, v_b_1944_, v_kind_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1947_, lean_object* v_00_u03b1_1948_, lean_object* v_00_u03b2_1949_, lean_object* v_00_u03c3_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_ext_1954_, lean_object* v_b_1955_, lean_object* v_kind_1956_){
_start:
{
uint8_t v_kind_boxed_1957_; lean_object* v_res_1958_; 
v_kind_boxed_1957_ = lean_unbox(v_kind_1956_);
v_res_1958_ = l_Lean_ScopedEnvExtension_add(v_m_1947_, v_00_u03b1_1948_, v_00_u03b2_1949_, v_00_u03c3_1950_, v_inst_1951_, v_inst_1952_, v_inst_1953_, v_ext_1954_, v_b_1955_, v_kind_boxed_1957_);
return v_res_1958_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1962_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1963_ = lean_unsigned_to_nat(16u);
v___x_1964_ = lean_unsigned_to_nat(209u);
v___x_1965_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1966_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1967_ = l_mkPanicMessageWithDecl(v___x_1966_, v___x_1965_, v___x_1964_, v___x_1963_, v___x_1962_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1968_, lean_object* v_ext_1969_, lean_object* v_env_1970_, lean_object* v_asyncMode_1971_){
_start:
{
lean_object* v_ext_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_stateStack_1976_; 
v_ext_1972_ = lean_ctor_get(v_ext_1969_, 1);
v___x_1973_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1974_ = lean_box(0);
v___x_1975_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1973_, v_ext_1972_, v_env_1970_, v_asyncMode_1971_, v___x_1974_);
v_stateStack_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_stateStack_1976_);
lean_dec(v___x_1975_);
if (lean_obj_tag(v_stateStack_1976_) == 1)
{
lean_object* v_head_1977_; lean_object* v_state_1978_; 
v_head_1977_ = lean_ctor_get(v_stateStack_1976_, 0);
lean_inc(v_head_1977_);
lean_dec_ref_known(v_stateStack_1976_, 2);
v_state_1978_ = lean_ctor_get(v_head_1977_, 0);
lean_inc(v_state_1978_);
lean_dec(v_head_1977_);
return v_state_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_stateStack_1976_);
v___x_1979_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1980_ = l_panic___redArg(v_inst_1968_, v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1981_, lean_object* v_ext_1982_, lean_object* v_env_1983_, lean_object* v_asyncMode_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1981_, v_ext_1982_, v_env_1983_, v_asyncMode_1984_);
lean_dec(v_asyncMode_1984_);
lean_dec_ref(v_ext_1982_);
lean_dec(v_inst_1981_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1986_, lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_inst_1989_, lean_object* v_ext_1990_, lean_object* v_env_1991_, lean_object* v_asyncMode_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1989_, v_ext_1990_, v_env_1991_, v_asyncMode_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1994_, lean_object* v_00_u03b1_1995_, lean_object* v_00_u03b2_1996_, lean_object* v_inst_1997_, lean_object* v_ext_1998_, lean_object* v_env_1999_, lean_object* v_asyncMode_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1994_, v_00_u03b1_1995_, v_00_u03b2_1996_, v_inst_1997_, v_ext_1998_, v_env_1999_, v_asyncMode_2000_);
lean_dec(v_asyncMode_2000_);
lean_dec_ref(v_ext_1998_);
lean_dec(v_inst_1997_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_2002_, lean_object* v_as_2003_, size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_b_2006_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v_ext_2002_);
return v_b_2006_;
}
else
{
lean_object* v_descr_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2023_; 
v_descr_2008_ = lean_ctor_get(v_ext_2002_, 0);
v_snd_2009_ = lean_ctor_get(v_b_2006_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_b_2006_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_b_2006_, 0);
lean_dec(v_unused_2024_);
v___x_2011_ = v_b_2006_;
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_dec(v_b_2006_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_addEntry_2013_; lean_object* v___x_2014_; lean_object* v_a_2015_; lean_object* v_state_2016_; lean_object* v___x_2018_; 
v_addEntry_2013_ = lean_ctor_get(v_descr_2008_, 4);
v___x_2014_ = lean_box(0);
v_a_2015_ = lean_array_uget_borrowed(v_as_2003_, v_i_2005_);
lean_inc(v_addEntry_2013_);
lean_inc(v_a_2015_);
v_state_2016_ = lean_apply_2(v_addEntry_2013_, v_snd_2009_, v_a_2015_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v_state_2016_);
lean_ctor_set(v___x_2011_, 0, v___x_2014_);
v___x_2018_ = v___x_2011_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_state_2016_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
size_t v___x_2019_; size_t v___x_2020_; 
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_2005_, v___x_2019_);
v_i_2005_ = v___x_2020_;
v_b_2006_ = v___x_2018_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_2025_, lean_object* v_as_2026_, lean_object* v_sz_2027_, lean_object* v_i_2028_, lean_object* v_b_2029_){
_start:
{
size_t v_sz_boxed_2030_; size_t v_i_boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2030_ = lean_unbox_usize(v_sz_2027_);
lean_dec(v_sz_2027_);
v_i_boxed_2031_ = lean_unbox_usize(v_i_2028_);
lean_dec(v_i_2028_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2025_, v_as_2026_, v_sz_boxed_2030_, v_i_boxed_2031_, v_b_2029_);
lean_dec_ref(v_as_2026_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_){
_start:
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_usize_dec_lt(v_i_2036_, v_sz_2035_);
if (v___x_2038_ == 0)
{
lean_dec_ref(v_ext_2033_);
return v_b_2037_;
}
else
{
lean_object* v_descr_2039_; lean_object* v_snd_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2054_; 
v_descr_2039_ = lean_ctor_get(v_ext_2033_, 0);
v_snd_2040_ = lean_ctor_get(v_b_2037_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_b_2037_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v_b_2037_, 0);
lean_dec(v_unused_2055_);
v___x_2042_ = v_b_2037_;
v_isShared_2043_ = v_isSharedCheck_2054_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snd_2040_);
lean_dec(v_b_2037_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2054_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_addEntry_2044_; lean_object* v___x_2045_; lean_object* v_a_2046_; lean_object* v_state_2047_; lean_object* v___x_2049_; 
v_addEntry_2044_ = lean_ctor_get(v_descr_2039_, 4);
v___x_2045_ = lean_box(0);
v_a_2046_ = lean_array_uget_borrowed(v_as_2034_, v_i_2036_);
lean_inc(v_addEntry_2044_);
lean_inc(v_a_2046_);
v_state_2047_ = lean_apply_2(v_addEntry_2044_, v_snd_2040_, v_a_2046_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v_state_2047_);
lean_ctor_set(v___x_2042_, 0, v___x_2045_);
v___x_2049_ = v___x_2042_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_state_2047_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2036_, v___x_2050_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2033_, v_as_2034_, v_sz_2035_, v___x_2051_, v___x_2049_);
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_2056_, lean_object* v_as_2057_, lean_object* v_sz_2058_, lean_object* v_i_2059_, lean_object* v_b_2060_){
_start:
{
size_t v_sz_boxed_2061_; size_t v_i_boxed_2062_; lean_object* v_res_2063_; 
v_sz_boxed_2061_ = lean_unbox_usize(v_sz_2058_);
lean_dec(v_sz_2058_);
v_i_boxed_2062_ = lean_unbox_usize(v_i_2059_);
lean_dec(v_i_2059_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2056_, v_as_2057_, v_sz_boxed_2061_, v_i_boxed_2062_, v_b_2060_);
lean_dec_ref(v_as_2057_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_2064_, lean_object* v_ext_2065_, lean_object* v_n_2066_, lean_object* v_b_2067_){
_start:
{
if (lean_obj_tag(v_n_2066_) == 0)
{
lean_object* v_cs_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; lean_object* v_fst_2074_; 
v_cs_2068_ = lean_ctor_get(v_n_2066_, 0);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v_b_2067_);
v_sz_2071_ = lean_array_size(v_cs_2068_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2064_, v_ext_2065_, v_cs_2068_, v_sz_2071_, v___x_2072_, v___x_2070_);
v_fst_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_fst_2074_);
if (lean_obj_tag(v_fst_2074_) == 0)
{
lean_object* v_snd_2075_; lean_object* v___x_2076_; 
v_snd_2075_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_snd_2075_);
lean_dec_ref(v___x_2073_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_snd_2075_);
return v___x_2076_;
}
else
{
lean_object* v_val_2077_; 
lean_dec_ref(v___x_2073_);
v_val_2077_ = lean_ctor_get(v_fst_2074_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v_fst_2074_, 1);
return v_val_2077_;
}
}
else
{
lean_object* v_vs_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; size_t v_sz_2081_; size_t v___x_2082_; lean_object* v___x_2083_; lean_object* v_fst_2084_; 
v_vs_2078_ = lean_ctor_get(v_n_2066_, 0);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_b_2067_);
v_sz_2081_ = lean_array_size(v_vs_2078_);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2065_, v_vs_2078_, v_sz_2081_, v___x_2082_, v___x_2080_);
v_fst_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_fst_2084_);
if (lean_obj_tag(v_fst_2084_) == 0)
{
lean_object* v_snd_2085_; lean_object* v___x_2086_; 
v_snd_2085_ = lean_ctor_get(v___x_2083_, 1);
lean_inc(v_snd_2085_);
lean_dec_ref(v___x_2083_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_snd_2085_);
return v___x_2086_;
}
else
{
lean_object* v_val_2087_; 
lean_dec_ref(v___x_2083_);
v_val_2087_ = lean_ctor_get(v_fst_2084_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v_fst_2084_, 1);
return v_val_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2088_, lean_object* v_ext_2089_, lean_object* v_as_2090_, size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_b_2093_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2094_ == 0)
{
lean_dec_ref(v_ext_2089_);
return v_b_2093_;
}
else
{
lean_object* v_snd_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2113_; 
v_snd_2095_ = lean_ctor_get(v_b_2093_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_b_2093_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_b_2093_, 0);
lean_dec(v_unused_2114_);
v___x_2097_ = v_b_2093_;
v_isShared_2098_ = v_isSharedCheck_2113_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snd_2095_);
lean_dec(v_b_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2113_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_array_uget_borrowed(v_as_2090_, v_i_2092_);
lean_inc(v_snd_2095_);
lean_inc_ref(v_ext_2089_);
v___x_2100_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2088_, v_ext_2089_, v_a_2099_, v_snd_2095_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_dec_ref(v_ext_2089_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_snd_2095_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec(v_snd_2095_);
v_a_2105_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2106_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v_a_2105_);
lean_ctor_set(v___x_2097_, 0, v___x_2106_);
v___x_2108_ = v___x_2097_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_a_2105_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
size_t v___x_2109_; size_t v___x_2110_; 
v___x_2109_ = ((size_t)1ULL);
v___x_2110_ = lean_usize_add(v_i_2092_, v___x_2109_);
v_i_2092_ = v___x_2110_;
v_b_2093_ = v___x_2108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2115_, lean_object* v_ext_2116_, lean_object* v_as_2117_, lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_b_2120_){
_start:
{
size_t v_sz_boxed_2121_; size_t v_i_boxed_2122_; lean_object* v_res_2123_; 
v_sz_boxed_2121_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2122_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2115_, v_ext_2116_, v_as_2117_, v_sz_boxed_2121_, v_i_boxed_2122_, v_b_2120_);
lean_dec_ref(v_as_2117_);
lean_dec(v_init_2115_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2124_, lean_object* v_ext_2125_, lean_object* v_n_2126_, lean_object* v_b_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2124_, v_ext_2125_, v_n_2126_, v_b_2127_);
lean_dec_ref(v_n_2126_);
lean_dec(v_init_2124_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2129_, lean_object* v_as_2130_, size_t v_sz_2131_, size_t v_i_2132_, lean_object* v_b_2133_){
_start:
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_usize_dec_lt(v_i_2132_, v_sz_2131_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v_ext_2129_);
return v_b_2133_;
}
else
{
lean_object* v_descr_2135_; lean_object* v_snd_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2150_; 
v_descr_2135_ = lean_ctor_get(v_ext_2129_, 0);
v_snd_2136_ = lean_ctor_get(v_b_2133_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_b_2133_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_b_2133_, 0);
lean_dec(v_unused_2151_);
v___x_2138_ = v_b_2133_;
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snd_2136_);
lean_dec(v_b_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_addEntry_2140_; lean_object* v___x_2141_; lean_object* v_a_2142_; lean_object* v_state_2143_; lean_object* v___x_2145_; 
v_addEntry_2140_ = lean_ctor_get(v_descr_2135_, 4);
v___x_2141_ = lean_box(0);
v_a_2142_ = lean_array_uget_borrowed(v_as_2130_, v_i_2132_);
lean_inc(v_addEntry_2140_);
lean_inc(v_a_2142_);
v_state_2143_ = lean_apply_2(v_addEntry_2140_, v_snd_2136_, v_a_2142_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v_state_2143_);
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2145_ = v___x_2138_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_state_2143_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
size_t v___x_2146_; size_t v___x_2147_; 
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2132_, v___x_2146_);
v_i_2132_ = v___x_2147_;
v_b_2133_ = v___x_2145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2152_, lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_){
_start:
{
size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2152_, v_as_2153_, v_sz_boxed_2157_, v_i_boxed_2158_, v_b_2156_);
lean_dec_ref(v_as_2153_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2160_, lean_object* v_as_2161_, size_t v_sz_2162_, size_t v_i_2163_, lean_object* v_b_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v_ext_2160_);
return v_b_2164_;
}
else
{
lean_object* v_descr_2166_; lean_object* v_snd_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2181_; 
v_descr_2166_ = lean_ctor_get(v_ext_2160_, 0);
v_snd_2167_ = lean_ctor_get(v_b_2164_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2182_);
v___x_2169_ = v_b_2164_;
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snd_2167_);
lean_dec(v_b_2164_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_addEntry_2171_; lean_object* v___x_2172_; lean_object* v_a_2173_; lean_object* v_state_2174_; lean_object* v___x_2176_; 
v_addEntry_2171_ = lean_ctor_get(v_descr_2166_, 4);
v___x_2172_ = lean_box(0);
v_a_2173_ = lean_array_uget_borrowed(v_as_2161_, v_i_2163_);
lean_inc(v_addEntry_2171_);
lean_inc(v_a_2173_);
v_state_2174_ = lean_apply_2(v_addEntry_2171_, v_snd_2167_, v_a_2173_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v_state_2174_);
lean_ctor_set(v___x_2169_, 0, v___x_2172_);
v___x_2176_ = v___x_2169_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_state_2174_);
v___x_2176_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2163_, v___x_2177_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2160_, v_as_2161_, v_sz_2162_, v___x_2178_, v___x_2176_);
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2183_, lean_object* v_as_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_b_2187_){
_start:
{
size_t v_sz_boxed_2188_; size_t v_i_boxed_2189_; lean_object* v_res_2190_; 
v_sz_boxed_2188_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2189_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2183_, v_as_2184_, v_sz_boxed_2188_, v_i_boxed_2189_, v_b_2187_);
lean_dec_ref(v_as_2184_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2191_, lean_object* v_t_2192_, lean_object* v_init_2193_){
_start:
{
lean_object* v_root_2194_; lean_object* v_tail_2195_; lean_object* v___x_2196_; 
v_root_2194_ = lean_ctor_get(v_t_2192_, 0);
v_tail_2195_ = lean_ctor_get(v_t_2192_, 1);
lean_inc_ref(v_ext_2191_);
lean_inc(v_init_2193_);
v___x_2196_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2193_, v_ext_2191_, v_root_2194_, v_init_2193_);
lean_dec(v_init_2193_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; 
lean_dec_ref(v_ext_2191_);
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
return v_a_2197_;
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; size_t v_sz_2201_; size_t v___x_2202_; lean_object* v___x_2203_; lean_object* v_fst_2204_; 
v_a_2198_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_a_2198_);
v_sz_2201_ = lean_array_size(v_tail_2195_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2191_, v_tail_2195_, v_sz_2201_, v___x_2202_, v___x_2200_);
v_fst_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_fst_2204_);
if (lean_obj_tag(v_fst_2204_) == 0)
{
lean_object* v_snd_2205_; 
v_snd_2205_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_snd_2205_);
lean_dec_ref(v___x_2203_);
return v_snd_2205_;
}
else
{
lean_object* v_val_2206_; 
lean_dec_ref(v___x_2203_);
v_val_2206_ = lean_ctor_get(v_fst_2204_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v_fst_2204_, 1);
return v_val_2206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2207_, lean_object* v_t_2208_, lean_object* v_init_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2207_, v_t_2208_, v_init_2209_);
lean_dec_ref(v_t_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2211_, lean_object* v_ext_2212_, lean_object* v_s_2213_){
_start:
{
lean_object* v_stateStack_2214_; 
v_stateStack_2214_ = lean_ctor_get(v_s_2213_, 0);
lean_inc(v_stateStack_2214_);
if (lean_obj_tag(v_stateStack_2214_) == 1)
{
lean_object* v_scopedEntries_2215_; lean_object* v_newEntries_2216_; lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2247_; 
v_scopedEntries_2215_ = lean_ctor_get(v_s_2213_, 1);
v_newEntries_2216_ = lean_ctor_get(v_s_2213_, 2);
v_head_2217_ = lean_ctor_get(v_stateStack_2214_, 0);
v_tail_2218_ = lean_ctor_get(v_stateStack_2214_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_stateStack_2214_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2220_ = v_stateStack_2214_;
v_isShared_2221_ = v_isSharedCheck_2247_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_tail_2218_);
lean_inc(v_head_2217_);
lean_dec(v_stateStack_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2247_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___y_2223_; lean_object* v_state_2228_; lean_object* v_activeScopes_2229_; uint8_t v_delimitsLocal_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2246_; 
v_state_2228_ = lean_ctor_get(v_head_2217_, 0);
v_activeScopes_2229_ = lean_ctor_get(v_head_2217_, 1);
v_delimitsLocal_2230_ = lean_ctor_get_uint8(v_head_2217_, sizeof(void*)*2);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_head_2217_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2232_ = v_head_2217_;
v_isShared_2233_ = v_isSharedCheck_2246_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_activeScopes_2229_);
lean_inc(v_state_2228_);
lean_dec(v_head_2217_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2246_;
goto v_resetjp_2231_;
}
v___jp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___y_2223_);
v___x_2225_ = v___x_2220_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___y_2223_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_tail_2218_);
v___x_2225_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_scopedEntries_2215_);
lean_ctor_set(v___x_2226_, 2, v_newEntries_2216_);
return v___x_2226_;
}
}
v_resetjp_2231_:
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_NameSet_contains(v_activeScopes_2229_, v_namespaceName_2211_);
if (v___x_2234_ == 0)
{
lean_object* v_activeScopes_2235_; lean_object* v___x_2236_; 
lean_inc(v_newEntries_2216_);
lean_inc_ref(v_scopedEntries_2215_);
lean_dec_ref(v_s_2213_);
lean_inc(v_namespaceName_2211_);
v_activeScopes_2235_ = l_Lean_NameSet_insert(v_activeScopes_2229_, v_namespaceName_2211_);
v___x_2236_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2215_, v_namespaceName_2211_);
lean_dec(v_namespaceName_2211_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2238_; 
lean_dec_ref(v_ext_2212_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_activeScopes_2235_);
v___x_2238_ = v___x_2232_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_state_2228_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_activeScopes_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2239_, sizeof(void*)*2, v_delimitsLocal_2230_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v___y_2223_ = v___x_2238_;
goto v___jp_2222_;
}
}
else
{
lean_object* v_val_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v_val_2240_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2241_ = 1;
v___x_2242_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2212_, v_val_2240_, v_state_2228_);
lean_dec(v_val_2240_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_activeScopes_2235_);
lean_ctor_set(v___x_2232_, 0, v___x_2242_);
v___x_2244_ = v___x_2232_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_activeScopes_2235_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*2, v___x_2241_);
v___y_2223_ = v___x_2244_;
goto v___jp_2222_;
}
}
}
else
{
lean_del_object(v___x_2232_);
lean_dec(v_activeScopes_2229_);
lean_dec(v_state_2228_);
lean_del_object(v___x_2220_);
lean_dec(v_tail_2218_);
lean_dec_ref(v_ext_2212_);
lean_dec(v_namespaceName_2211_);
return v_s_2213_;
}
}
}
}
else
{
lean_dec(v_stateStack_2214_);
lean_dec_ref(v_ext_2212_);
lean_dec(v_namespaceName_2211_);
return v_s_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2248_, lean_object* v_env_2249_, lean_object* v_namespaceName_2250_){
_start:
{
lean_object* v_ext_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_ext_2251_ = lean_ctor_get(v_ext_2248_, 1);
lean_inc_ref(v_ext_2251_);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2252_, 0, v_namespaceName_2250_);
lean_closure_set(v___f_2252_, 1, v_ext_2248_);
v___x_2253_ = lean_box(1);
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2251_, v_env_2249_, v___f_2252_, v___x_2253_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2256_, lean_object* v_00_u03b2_2257_, lean_object* v_00_u03c3_2258_, lean_object* v_ext_2259_, lean_object* v_env_2260_, lean_object* v_namespaceName_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2259_, v_env_2260_, v_namespaceName_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2263_, lean_object* v_00_u03c3_2264_, lean_object* v_00_u03b1_2265_, lean_object* v_ext_2266_, lean_object* v_t_2267_, lean_object* v_init_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2266_, v_t_2267_, v_init_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2270_, lean_object* v_00_u03c3_2271_, lean_object* v_00_u03b1_2272_, lean_object* v_ext_2273_, lean_object* v_t_2274_, lean_object* v_init_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2270_, v_00_u03c3_2271_, v_00_u03b1_2272_, v_ext_2273_, v_t_2274_, v_init_2275_);
lean_dec_ref(v_t_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2277_, lean_object* v_00_u03c3_2278_, lean_object* v_init_2279_, lean_object* v_00_u03b1_2280_, lean_object* v_ext_2281_, lean_object* v_n_2282_, lean_object* v_b_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2279_, v_ext_2281_, v_n_2282_, v_b_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_00_u03c3_2286_, lean_object* v_init_2287_, lean_object* v_00_u03b1_2288_, lean_object* v_ext_2289_, lean_object* v_n_2290_, lean_object* v_b_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2285_, v_00_u03c3_2286_, v_init_2287_, v_00_u03b1_2288_, v_ext_2289_, v_n_2290_, v_b_2291_);
lean_dec_ref(v_n_2290_);
lean_dec(v_init_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2293_, lean_object* v_00_u03c3_2294_, lean_object* v_00_u03b1_2295_, lean_object* v_ext_2296_, lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_b_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2296_, v_as_2297_, v_sz_2298_, v_i_2299_, v_b_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2302_, lean_object* v_00_u03c3_2303_, lean_object* v_00_u03b1_2304_, lean_object* v_ext_2305_, lean_object* v_as_2306_, lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_b_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2302_, v_00_u03c3_2303_, v_00_u03b1_2304_, v_ext_2305_, v_as_2306_, v_sz_boxed_2310_, v_i_boxed_2311_, v_b_2309_);
lean_dec_ref(v_as_2306_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2313_, lean_object* v_00_u03c3_2314_, lean_object* v_init_2315_, lean_object* v_00_u03b1_2316_, lean_object* v_ext_2317_, lean_object* v_as_2318_, size_t v_sz_2319_, size_t v_i_2320_, lean_object* v_b_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2315_, v_ext_2317_, v_as_2318_, v_sz_2319_, v_i_2320_, v_b_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2323_, lean_object* v_00_u03c3_2324_, lean_object* v_init_2325_, lean_object* v_00_u03b1_2326_, lean_object* v_ext_2327_, lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_b_2331_){
_start:
{
size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2323_, v_00_u03c3_2324_, v_init_2325_, v_00_u03b1_2326_, v_ext_2327_, v_as_2328_, v_sz_boxed_2332_, v_i_boxed_2333_, v_b_2331_);
lean_dec_ref(v_as_2328_);
lean_dec(v_init_2325_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2335_, lean_object* v_00_u03c3_2336_, lean_object* v_00_u03b1_2337_, lean_object* v_ext_2338_, lean_object* v_as_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_b_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2338_, v_as_2339_, v_sz_2340_, v_i_2341_, v_b_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_00_u03c3_2345_, lean_object* v_00_u03b1_2346_, lean_object* v_ext_2347_, lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_b_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2344_, v_00_u03c3_2345_, v_00_u03b1_2346_, v_ext_2347_, v_as_2348_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2351_);
lean_dec_ref(v_as_2348_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2355_, lean_object* v_00_u03c3_2356_, lean_object* v_00_u03b1_2357_, lean_object* v_ext_2358_, lean_object* v_as_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_b_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2358_, v_as_2359_, v_sz_2360_, v_i_2361_, v_b_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_00_u03c3_2365_, lean_object* v_00_u03b1_2366_, lean_object* v_ext_2367_, lean_object* v_as_2368_, lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_b_2371_){
_start:
{
size_t v_sz_boxed_2372_; size_t v_i_boxed_2373_; lean_object* v_res_2374_; 
v_sz_boxed_2372_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2373_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2364_, v_00_u03c3_2365_, v_00_u03b1_2366_, v_ext_2367_, v_as_2368_, v_sz_boxed_2372_, v_i_boxed_2373_, v_b_2371_);
lean_dec_ref(v_as_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2375_, lean_object* v_00_u03c3_2376_, lean_object* v_00_u03b1_2377_, lean_object* v_ext_2378_, lean_object* v_as_2379_, size_t v_sz_2380_, size_t v_i_2381_, lean_object* v_b_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2378_, v_as_2379_, v_sz_2380_, v_i_2381_, v_b_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_00_u03c3_2385_, lean_object* v_00_u03b1_2386_, lean_object* v_ext_2387_, lean_object* v_as_2388_, lean_object* v_sz_2389_, lean_object* v_i_2390_, lean_object* v_b_2391_){
_start:
{
size_t v_sz_boxed_2392_; size_t v_i_boxed_2393_; lean_object* v_res_2394_; 
v_sz_boxed_2392_ = lean_unbox_usize(v_sz_2389_);
lean_dec(v_sz_2389_);
v_i_boxed_2393_ = lean_unbox_usize(v_i_2390_);
lean_dec(v_i_2390_);
v_res_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2384_, v_00_u03c3_2385_, v_00_u03b1_2386_, v_ext_2387_, v_as_2388_, v_sz_boxed_2392_, v_i_boxed_2393_, v_b_2391_);
lean_dec_ref(v_as_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2395_, lean_object* v_s_2396_){
_start:
{
lean_object* v_stateStack_2397_; 
v_stateStack_2397_ = lean_ctor_get(v_s_2396_, 0);
lean_inc(v_stateStack_2397_);
if (lean_obj_tag(v_stateStack_2397_) == 1)
{
lean_object* v_head_2398_; lean_object* v_scopedEntries_2399_; lean_object* v_newEntries_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2427_; 
v_head_2398_ = lean_ctor_get(v_stateStack_2397_, 0);
lean_inc(v_head_2398_);
v_scopedEntries_2399_ = lean_ctor_get(v_s_2396_, 1);
v_newEntries_2400_ = lean_ctor_get(v_s_2396_, 2);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_s_2396_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v_s_2396_, 0);
lean_dec(v_unused_2428_);
v___x_2402_ = v_s_2396_;
v_isShared_2403_ = v_isSharedCheck_2427_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_newEntries_2400_);
lean_inc(v_scopedEntries_2399_);
lean_dec(v_s_2396_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2427_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v_tail_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2425_; 
v_tail_2404_ = lean_ctor_get(v_stateStack_2397_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_stateStack_2397_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v_stateStack_2397_, 0);
lean_dec(v_unused_2426_);
v___x_2406_ = v_stateStack_2397_;
v_isShared_2407_ = v_isSharedCheck_2425_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_tail_2404_);
lean_dec(v_stateStack_2397_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2425_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_state_2408_; lean_object* v_activeScopes_2409_; uint8_t v_delimitsLocal_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2424_; 
v_state_2408_ = lean_ctor_get(v_head_2398_, 0);
v_activeScopes_2409_ = lean_ctor_get(v_head_2398_, 1);
v_delimitsLocal_2410_ = lean_ctor_get_uint8(v_head_2398_, sizeof(void*)*2);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_head_2398_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2412_ = v_head_2398_;
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_activeScopes_2409_);
lean_inc(v_state_2408_);
lean_dec(v_head_2398_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2424_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = lean_apply_1(v_f_2395_, v_state_2408_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_activeScopes_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*2, v_delimitsLocal_2410_);
v___x_2416_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2416_);
v___x_2418_ = v___x_2406_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_tail_2404_);
v___x_2418_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2418_);
v___x_2420_ = v___x_2402_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_scopedEntries_2399_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_newEntries_2400_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2397_);
lean_dec(v_f_2395_);
return v_s_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2429_, lean_object* v_env_2430_, lean_object* v_f_2431_){
_start:
{
lean_object* v_ext_2432_; lean_object* v_toEnvExtension_2433_; lean_object* v_asyncMode_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_ext_2432_ = lean_ctor_get(v_ext_2429_, 1);
lean_inc_ref(v_ext_2432_);
lean_dec_ref(v_ext_2429_);
v_toEnvExtension_2433_ = lean_ctor_get(v_ext_2432_, 0);
v_asyncMode_2434_ = lean_ctor_get(v_toEnvExtension_2433_, 2);
lean_inc(v_asyncMode_2434_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2435_, 0, v_f_2431_);
v___x_2436_ = lean_box(0);
v___x_2437_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2432_, v_env_2430_, v___f_2435_, v_asyncMode_2434_, v___x_2436_);
lean_dec(v_asyncMode_2434_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2438_, lean_object* v_00_u03b2_2439_, lean_object* v_00_u03c3_2440_, lean_object* v_ext_2441_, lean_object* v_env_2442_, lean_object* v_f_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2441_, v_env_2442_, v_f_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2445_, lean_object* v_____s_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_apply_2(v_toPure_2445_, lean_box(0), v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2449_, lean_object* v_toPure_2450_, lean_object* v_r_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2449_);
v___x_2453_ = lean_apply_2(v_toPure_2450_, lean_box(0), v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2454_, lean_object* v_toBind_2455_, lean_object* v___f_2456_, lean_object* v_a_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_modifyEnv_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_modifyEnv_2460_ = lean_ctor_get(v_inst_2454_, 1);
lean_inc(v_modifyEnv_2460_);
lean_dec_ref(v_inst_2454_);
v___x_2461_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2461_, 0, lean_box(0));
lean_closure_set(v___x_2461_, 1, lean_box(0));
lean_closure_set(v___x_2461_, 2, lean_box(0));
lean_closure_set(v___x_2461_, 3, v_a_2457_);
v___x_2462_ = lean_apply_1(v_modifyEnv_2460_, v___x_2461_);
v___x_2463_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2462_, v___f_2456_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2464_, lean_object* v_inst_2465_, lean_object* v_toBind_2466_, lean_object* v_inst_2467_, lean_object* v___f_2468_, lean_object* v_____do__lift_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; size_t v_sz_2473_; size_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2470_ = lean_box(0);
v___f_2471_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2471_, 0, v___x_2470_);
lean_closure_set(v___f_2471_, 1, v_toPure_2464_);
lean_inc(v_toBind_2466_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2472_, 0, v_inst_2465_);
lean_closure_set(v___f_2472_, 1, v_toBind_2466_);
lean_closure_set(v___f_2472_, 2, v___f_2471_);
v_sz_2473_ = lean_array_size(v_____do__lift_2469_);
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2467_, v_____do__lift_2469_, v___f_2472_, v_sz_2473_, v___x_2474_, v___x_2470_);
v___x_2476_ = lean_apply_4(v_toBind_2466_, lean_box(0), lean_box(0), v___x_2475_, v___f_2468_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = l_Lean_scopedEnvExtensionsRef;
v___x_2478_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2478_, 0, lean_box(0));
lean_closure_set(v___x_2478_, 1, lean_box(0));
lean_closure_set(v___x_2478_, 2, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_){
_start:
{
lean_object* v_toApplicative_2482_; lean_object* v_toBind_2483_; lean_object* v_toPure_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; 
v_toApplicative_2482_ = lean_ctor_get(v_inst_2479_, 0);
v_toBind_2483_ = lean_ctor_get(v_inst_2479_, 1);
lean_inc_n(v_toBind_2483_, 2);
v_toPure_2484_ = lean_ctor_get(v_toApplicative_2482_, 1);
lean_inc_n(v_toPure_2484_, 2);
v___x_2485_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2486_ = lean_apply_2(v_inst_2481_, lean_box(0), v___x_2485_);
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2487_, 0, v_toPure_2484_);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2488_, 0, v_toPure_2484_);
lean_closure_set(v___f_2488_, 1, v_inst_2480_);
lean_closure_set(v___f_2488_, 2, v_toBind_2483_);
lean_closure_set(v___f_2488_, 3, v_inst_2479_);
lean_closure_set(v___f_2488_, 4, v___f_2487_);
v___x_2489_ = lean_apply_4(v_toBind_2483_, lean_box(0), lean_box(0), v___x_2486_, v___f_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_pushScope___redArg(v_inst_2491_, v_inst_2492_, v_inst_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2495_, lean_object* v_toBind_2496_, lean_object* v___f_2497_, lean_object* v_a_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_modifyEnv_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_modifyEnv_2501_ = lean_ctor_get(v_inst_2495_, 1);
lean_inc(v_modifyEnv_2501_);
lean_dec_ref(v_inst_2495_);
v___x_2502_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2502_, 0, lean_box(0));
lean_closure_set(v___x_2502_, 1, lean_box(0));
lean_closure_set(v___x_2502_, 2, lean_box(0));
lean_closure_set(v___x_2502_, 3, v_a_2498_);
v___x_2503_ = lean_apply_1(v_modifyEnv_2501_, v___x_2502_);
v___x_2504_ = lean_apply_4(v_toBind_2496_, lean_box(0), lean_box(0), v___x_2503_, v___f_2497_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2505_, lean_object* v_inst_2506_, lean_object* v_toBind_2507_, lean_object* v_inst_2508_, lean_object* v___f_2509_, lean_object* v_____do__lift_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2511_ = lean_box(0);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2512_, 0, v___x_2511_);
lean_closure_set(v___f_2512_, 1, v_toPure_2505_);
lean_inc(v_toBind_2507_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2513_, 0, v_inst_2506_);
lean_closure_set(v___f_2513_, 1, v_toBind_2507_);
lean_closure_set(v___f_2513_, 2, v___f_2512_);
v_sz_2514_ = lean_array_size(v_____do__lift_2510_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2508_, v_____do__lift_2510_, v___f_2513_, v_sz_2514_, v___x_2515_, v___x_2511_);
v___x_2517_ = lean_apply_4(v_toBind_2507_, lean_box(0), lean_box(0), v___x_2516_, v___f_2509_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_){
_start:
{
lean_object* v_toApplicative_2521_; lean_object* v_toBind_2522_; lean_object* v_toPure_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___f_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v_toApplicative_2521_ = lean_ctor_get(v_inst_2518_, 0);
v_toBind_2522_ = lean_ctor_get(v_inst_2518_, 1);
lean_inc_n(v_toBind_2522_, 2);
v_toPure_2523_ = lean_ctor_get(v_toApplicative_2521_, 1);
lean_inc_n(v_toPure_2523_, 2);
v___x_2524_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2525_ = lean_apply_2(v_inst_2520_, lean_box(0), v___x_2524_);
v___f_2526_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2526_, 0, v_toPure_2523_);
v___f_2527_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2527_, 0, v_toPure_2523_);
lean_closure_set(v___f_2527_, 1, v_inst_2519_);
lean_closure_set(v___f_2527_, 2, v_toBind_2522_);
lean_closure_set(v___f_2527_, 3, v_inst_2518_);
lean_closure_set(v___f_2527_, 4, v___f_2526_);
v___x_2528_ = lean_apply_4(v_toBind_2522_, lean_box(0), lean_box(0), v___x_2525_, v___f_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_popScope___redArg(v_inst_2530_, v_inst_2531_, v_inst_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2534_, lean_object* v_depth_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2534_, v_x_2536_, v_depth_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2538_, lean_object* v_depth_2539_, lean_object* v_toBind_2540_, lean_object* v___f_2541_, lean_object* v_a_2542_, lean_object* v_x_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_modifyEnv_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_modifyEnv_2545_ = lean_ctor_get(v_inst_2538_, 1);
lean_inc(v_modifyEnv_2545_);
lean_dec_ref(v_inst_2538_);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2546_, 0, v_a_2542_);
lean_closure_set(v___f_2546_, 1, v_depth_2539_);
v___x_2547_ = lean_apply_1(v_modifyEnv_2545_, v___f_2546_);
v___x_2548_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2547_, v___f_2541_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2549_, lean_object* v_inst_2550_, lean_object* v_depth_2551_, lean_object* v_toBind_2552_, lean_object* v_inst_2553_, lean_object* v___f_2554_, lean_object* v_____do__lift_2555_){
_start:
{
lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; size_t v_sz_2559_; size_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2556_ = lean_box(0);
v___f_2557_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2557_, 0, v___x_2556_);
lean_closure_set(v___f_2557_, 1, v_toPure_2549_);
lean_inc(v_toBind_2552_);
v___f_2558_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2558_, 0, v_inst_2550_);
lean_closure_set(v___f_2558_, 1, v_depth_2551_);
lean_closure_set(v___f_2558_, 2, v_toBind_2552_);
lean_closure_set(v___f_2558_, 3, v___f_2557_);
v_sz_2559_ = lean_array_size(v_____do__lift_2555_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2553_, v_____do__lift_2555_, v___f_2558_, v_sz_2559_, v___x_2560_, v___x_2556_);
v___x_2562_ = lean_apply_4(v_toBind_2552_, lean_box(0), lean_box(0), v___x_2561_, v___f_2554_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_depth_2566_){
_start:
{
lean_object* v_toApplicative_2567_; lean_object* v_toBind_2568_; lean_object* v_toPure_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; 
v_toApplicative_2567_ = lean_ctor_get(v_inst_2563_, 0);
v_toBind_2568_ = lean_ctor_get(v_inst_2563_, 1);
lean_inc_n(v_toBind_2568_, 2);
v_toPure_2569_ = lean_ctor_get(v_toApplicative_2567_, 1);
lean_inc_n(v_toPure_2569_, 2);
v___x_2570_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2571_ = lean_apply_2(v_inst_2565_, lean_box(0), v___x_2570_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2572_, 0, v_toPure_2569_);
v___f_2573_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2573_, 0, v_toPure_2569_);
lean_closure_set(v___f_2573_, 1, v_inst_2564_);
lean_closure_set(v___f_2573_, 2, v_depth_2566_);
lean_closure_set(v___f_2573_, 3, v_toBind_2568_);
lean_closure_set(v___f_2573_, 4, v_inst_2563_);
lean_closure_set(v___f_2573_, 5, v___f_2572_);
v___x_2574_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2571_, v___f_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_depth_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_setDelimitsLocal___redArg(v_inst_2576_, v_inst_2577_, v_inst_2578_, v_depth_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2581_, lean_object* v_namespaceName_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2581_, v_x_2583_, v_namespaceName_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2585_, lean_object* v_namespaceName_2586_, lean_object* v_toBind_2587_, lean_object* v___f_2588_, lean_object* v_a_2589_, lean_object* v_x_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_modifyEnv_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_modifyEnv_2592_ = lean_ctor_get(v_inst_2585_, 1);
lean_inc(v_modifyEnv_2592_);
lean_dec_ref(v_inst_2585_);
v___f_2593_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2593_, 0, v_a_2589_);
lean_closure_set(v___f_2593_, 1, v_namespaceName_2586_);
v___x_2594_ = lean_apply_1(v_modifyEnv_2592_, v___f_2593_);
v___x_2595_ = lean_apply_4(v_toBind_2587_, lean_box(0), lean_box(0), v___x_2594_, v___f_2588_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2596_, lean_object* v_inst_2597_, lean_object* v_namespaceName_2598_, lean_object* v_toBind_2599_, lean_object* v_inst_2600_, lean_object* v___f_2601_, lean_object* v_____do__lift_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; size_t v_sz_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2603_ = lean_box(0);
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2604_, 0, v___x_2603_);
lean_closure_set(v___f_2604_, 1, v_toPure_2596_);
lean_inc(v_toBind_2599_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2605_, 0, v_inst_2597_);
lean_closure_set(v___f_2605_, 1, v_namespaceName_2598_);
lean_closure_set(v___f_2605_, 2, v_toBind_2599_);
lean_closure_set(v___f_2605_, 3, v___f_2604_);
v_sz_2606_ = lean_array_size(v_____do__lift_2602_);
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2600_, v_____do__lift_2602_, v___f_2605_, v_sz_2606_, v___x_2607_, v___x_2603_);
v___x_2609_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2608_, v___f_2601_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_namespaceName_2613_){
_start:
{
lean_object* v_toApplicative_2614_; lean_object* v_toBind_2615_; lean_object* v_toPure_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
v_toApplicative_2614_ = lean_ctor_get(v_inst_2610_, 0);
v_toBind_2615_ = lean_ctor_get(v_inst_2610_, 1);
lean_inc_n(v_toBind_2615_, 2);
v_toPure_2616_ = lean_ctor_get(v_toApplicative_2614_, 1);
lean_inc_n(v_toPure_2616_, 2);
v___x_2617_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2618_ = lean_apply_2(v_inst_2612_, lean_box(0), v___x_2617_);
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2619_, 0, v_toPure_2616_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2620_, 0, v_toPure_2616_);
lean_closure_set(v___f_2620_, 1, v_inst_2611_);
lean_closure_set(v___f_2620_, 2, v_namespaceName_2613_);
lean_closure_set(v___f_2620_, 3, v_toBind_2615_);
lean_closure_set(v___f_2620_, 4, v_inst_2610_);
lean_closure_set(v___f_2620_, 5, v___f_2619_);
v___x_2621_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v___x_2618_, v___f_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_namespaceName_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_activateScoped___redArg(v_inst_2623_, v_inst_2624_, v_inst_2625_, v_namespaceName_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2629_){
_start:
{
lean_inc(v___y_2629_);
return v___y_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2630_);
lean_dec(v___y_2630_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2632_, lean_object* v_a_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_a_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2637_, lean_object* v_a_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2637_, v_a_2638_, v___y_2639_);
lean_dec_ref(v___y_2639_);
lean_dec(v_x_2637_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_initial_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2650_){
_start:
{
lean_object* v_name_2652_; lean_object* v_addEntry_2653_; lean_object* v_initial_2654_; lean_object* v_finalizeImport_2655_; lean_object* v_exportEntry_x3f_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_name_2652_ = lean_ctor_get(v_descr_2650_, 0);
lean_inc(v_name_2652_);
v_addEntry_2653_ = lean_ctor_get(v_descr_2650_, 1);
lean_inc(v_addEntry_2653_);
v_initial_2654_ = lean_ctor_get(v_descr_2650_, 2);
lean_inc(v_initial_2654_);
v_finalizeImport_2655_ = lean_ctor_get(v_descr_2650_, 3);
lean_inc(v_finalizeImport_2655_);
v_exportEntry_x3f_2656_ = lean_ctor_get(v_descr_2650_, 4);
lean_inc_ref(v_exportEntry_x3f_2656_);
lean_dec_ref(v_descr_2650_);
v___f_2657_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2658_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2659_, 0, v_initial_2654_);
v___x_2660_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2660_, 0, v_name_2652_);
lean_ctor_set(v___x_2660_, 1, v___f_2659_);
lean_ctor_set(v___x_2660_, 2, v___f_2658_);
lean_ctor_set(v___x_2660_, 3, v___f_2657_);
lean_ctor_set(v___x_2660_, 4, v_addEntry_2653_);
lean_ctor_set(v___x_2660_, 5, v_finalizeImport_2655_);
lean_ctor_set(v___x_2660_, 6, v_exportEntry_x3f_2656_);
v___x_2661_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2665_, lean_object* v_00_u03c3_2666_, lean_object* v_descr_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2670_, lean_object* v_00_u03c3_2671_, lean_object* v_descr_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2670_, v_00_u03c3_2671_, v_descr_2672_);
return v_res_2674_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_scopedEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_scopedEnvExtensionsRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ScopedEnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_ScopedEnvExtension_Descr_name___autoParam = _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam();
lean_mark_persistent(l_Lean_ScopedEnvExtension_Descr_name___autoParam);
l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam = _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam();
lean_mark_persistent(l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ScopedEnvExtension(builtin);
}
#ifdef __cplusplus
}
#endif
