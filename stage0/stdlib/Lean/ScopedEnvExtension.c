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
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_unsigned_to_nat(16u);
v___x_53_ = lean_mk_array(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_57_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3);
v___x_61_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1);
v___x_62_ = 1;
v___x_63_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_60_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object* v_00_u03b2_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_box(0));
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_70_ = lean_box(0);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_00_u03c3_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_108_ = l_Lean_mkAtom(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_110_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_121_ = l_Lean_mkAtom(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_123_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_126_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_127_ = lean_box(2);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_130_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_133_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_134_ = lean_box(2);
v___x_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
lean_ctor_set(v___x_135_, 2, v___x_132_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_137_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_138_ = lean_array_push(v___x_137_, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_140_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_141_ = lean_box(2);
v___x_142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
lean_ctor_set(v___x_142_, 2, v___x_139_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_144_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_145_ = lean_array_push(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_147_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_148_ = lean_box(2);
v___x_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_151_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_152_ = lean_array_push(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_153_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_154_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_155_ = lean_box(2);
v___x_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_153_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_167_, v___y_168_, v___y_169_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec(v_x_167_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_172_, lean_object* v_x_173_){
_start:
{
lean_inc(v_inst_172_);
return v_inst_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec(v_inst_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_177_, lean_object* v_x_178_){
_start:
{
lean_inc(v_s_177_);
return v_s_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec(v_s_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_a_183_);
lean_inc_ref_n(v___x_184_, 2);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_186_, v_a_187_);
lean_dec_ref(v_x_186_);
return v_res_188_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = l_instInhabitedError;
v___x_193_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_193_, 0, lean_box(0));
lean_closure_set(v___x_193_, 1, lean_box(0));
lean_closure_set(v___x_193_, 2, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___f_196_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_197_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_197_, 0, v_inst_195_);
v___f_198_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_199_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_200_ = lean_box(0);
v___x_201_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_202_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_203_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_203_, 0, v___x_200_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___f_196_);
lean_ctor_set(v___x_203_, 3, v___f_197_);
lean_ctor_set(v___x_203_, 4, v___f_198_);
lean_ctor_set(v___x_203_, 5, v___x_202_);
lean_ctor_set(v___x_203_, 6, v___f_199_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_00_u03c3_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_209_){
_start:
{
lean_object* v_mkInitial_211_; lean_object* v___x_212_; 
v_mkInitial_211_ = lean_ctor_get(v_descr_209_, 1);
lean_inc_ref(v_mkInitial_211_);
lean_dec_ref(v_descr_209_);
v___x_212_ = lean_apply_1(v_mkInitial_211_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_227_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_227_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_217_ = l_Lean_NameSet_empty;
v___x_218_ = 1;
v___x_219_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_219_, 0, v_a_213_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*2, v___x_218_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_223_);
v___x_225_ = v___x_215_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_212_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_212_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_00_u03c3_241_, lean_object* v_descr_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_00_u03c3_247_, lean_object* v_descr_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_245_, v_00_u03b2_246_, v_00_u03c3_247_, v_descr_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v_key_254_; lean_object* v_value_255_; lean_object* v_tail_256_; uint8_t v___x_257_; 
v_key_254_ = lean_ctor_get(v_x_252_, 0);
v_value_255_ = lean_ctor_get(v_x_252_, 1);
v_tail_256_ = lean_ctor_get(v_x_252_, 2);
v___x_257_ = lean_name_eq(v_key_254_, v_a_251_);
if (v___x_257_ == 0)
{
v_x_252_ = v_tail_256_;
goto _start;
}
else
{
lean_object* v___x_259_; 
lean_inc(v_value_255_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_value_255_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_buckets_265_; lean_object* v___x_266_; uint64_t v___y_268_; 
v_buckets_265_ = lean_ctor_get(v_m_263_, 1);
v___x_266_ = lean_array_get_size(v_buckets_265_);
if (lean_obj_tag(v_a_264_) == 0)
{
uint64_t v___x_282_; 
v___x_282_ = 1723ULL;
v___y_268_ = v___x_282_;
goto v___jp_267_;
}
else
{
uint64_t v_hash_283_; 
v_hash_283_ = lean_ctor_get_uint64(v_a_264_, sizeof(void*)*2);
v___y_268_ = v_hash_283_;
goto v___jp_267_;
}
v___jp_267_:
{
uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v_fold_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_269_ = 32ULL;
v___x_270_ = lean_uint64_shift_right(v___y_268_, v___x_269_);
v_fold_271_ = lean_uint64_xor(v___y_268_, v___x_270_);
v___x_272_ = 16ULL;
v___x_273_ = lean_uint64_shift_right(v_fold_271_, v___x_272_);
v___x_274_ = lean_uint64_xor(v_fold_271_, v___x_273_);
v___x_275_ = lean_uint64_to_usize(v___x_274_);
v___x_276_ = lean_usize_of_nat(v___x_266_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_sub(v___x_276_, v___x_277_);
v___x_279_ = lean_usize_land(v___x_275_, v___x_278_);
v___x_280_ = lean_array_uget_borrowed(v_buckets_265_, v___x_279_);
v___x_281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_264_, v___x_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_m_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_287_, lean_object* v_vals_288_, lean_object* v_i_289_, lean_object* v_k_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_keys_287_);
v___x_292_ = lean_nat_dec_lt(v_i_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_i_289_);
v___x_293_ = lean_box(0);
return v___x_293_;
}
else
{
lean_object* v_k_x27_294_; uint8_t v___x_295_; 
v_k_x27_294_ = lean_array_fget_borrowed(v_keys_287_, v_i_289_);
v___x_295_ = lean_name_eq(v_k_290_, v_k_x27_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_289_, v___x_296_);
lean_dec(v_i_289_);
v_i_289_ = v___x_297_;
goto _start;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_vals_288_, v_i_289_);
lean_dec(v_i_289_);
lean_inc(v___x_299_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_301_, lean_object* v_vals_302_, lean_object* v_i_303_, lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_301_, v_vals_302_, v_i_303_, v_k_304_);
lean_dec(v_k_304_);
lean_dec_ref(v_vals_302_);
lean_dec_ref(v_keys_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_306_, size_t v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v_es_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v_j_313_; lean_object* v___x_314_; 
v_es_309_ = lean_ctor_get(v_x_306_, 0);
v___x_310_ = lean_box(2);
v___x_311_ = ((size_t)31ULL);
v___x_312_ = lean_usize_land(v_x_307_, v___x_311_);
v_j_313_ = lean_usize_to_nat(v___x_312_);
v___x_314_ = lean_array_get_borrowed(v___x_310_, v_es_309_, v_j_313_);
lean_dec(v_j_313_);
switch(lean_obj_tag(v___x_314_))
{
case 0:
{
lean_object* v_key_315_; lean_object* v_val_316_; uint8_t v___x_317_; 
v_key_315_ = lean_ctor_get(v___x_314_, 0);
v_val_316_ = lean_ctor_get(v___x_314_, 1);
v___x_317_ = lean_name_eq(v_x_308_, v_key_315_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
lean_inc(v_val_316_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v_val_316_);
return v___x_319_;
}
}
case 1:
{
lean_object* v_node_320_; size_t v___x_321_; size_t v___x_322_; 
v_node_320_ = lean_ctor_get(v___x_314_, 0);
v___x_321_ = ((size_t)5ULL);
v___x_322_ = lean_usize_shift_right(v_x_307_, v___x_321_);
v_x_306_ = v_node_320_;
v_x_307_ = v___x_322_;
goto _start;
}
default: 
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
}
else
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_ks_325_ = lean_ctor_get(v_x_306_, 0);
v_vs_326_ = lean_ctor_get(v_x_306_, 1);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_325_, v_vs_326_, v___x_327_, v_x_308_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
size_t v_x_1046__boxed_332_; lean_object* v_res_333_; 
v_x_1046__boxed_332_ = lean_unbox_usize(v_x_330_);
lean_dec(v_x_330_);
v_res_333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_329_, v_x_1046__boxed_332_, v_x_331_);
lean_dec(v_x_331_);
lean_dec_ref(v_x_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint64_t v___y_337_; 
if (lean_obj_tag(v_x_335_) == 0)
{
uint64_t v___x_340_; 
v___x_340_ = 1723ULL;
v___y_337_ = v___x_340_;
goto v___jp_336_;
}
else
{
uint64_t v_hash_341_; 
v_hash_341_ = lean_ctor_get_uint64(v_x_335_, sizeof(void*)*2);
v___y_337_ = v_hash_341_;
goto v___jp_336_;
}
v___jp_336_:
{
size_t v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_uint64_to_usize(v___y_337_);
v___x_339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_334_, v___x_338_, v_x_335_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_342_, v_x_343_);
lean_dec(v_x_343_);
lean_dec_ref(v_x_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_stage_u2081_347_; 
v_stage_u2081_347_ = lean_ctor_get_uint8(v_x_345_, sizeof(void*)*2);
if (v_stage_u2081_347_ == 0)
{
lean_object* v_map_u2081_348_; lean_object* v_map_u2082_349_; lean_object* v___x_350_; 
v_map_u2081_348_ = lean_ctor_get(v_x_345_, 0);
v_map_u2082_349_ = lean_ctor_get(v_x_345_, 1);
v___x_350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_349_, v_x_346_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_348_, v_x_346_);
return v___x_351_;
}
else
{
return v___x_350_;
}
}
else
{
lean_object* v_map_u2081_352_; lean_object* v___x_353_; 
v_map_u2081_352_ = lean_ctor_get(v_x_345_, 0);
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_352_, v_x_346_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_354_, v_x_355_);
lean_dec(v_x_355_);
lean_dec_ref(v_x_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_dec(v_b_358_);
lean_dec(v_a_357_);
return v_x_359_;
}
else
{
lean_object* v_key_360_; lean_object* v_value_361_; lean_object* v_tail_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_374_; 
v_key_360_ = lean_ctor_get(v_x_359_, 0);
v_value_361_ = lean_ctor_get(v_x_359_, 1);
v_tail_362_ = lean_ctor_get(v_x_359_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_359_);
if (v_isSharedCheck_374_ == 0)
{
v___x_364_ = v_x_359_;
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_tail_362_);
lean_inc(v_value_361_);
lean_inc(v_key_360_);
lean_dec(v_x_359_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; 
v___x_366_ = lean_name_eq(v_key_360_, v_a_357_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_357_, v_b_358_, v_tail_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_key_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_value_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v_value_361_);
lean_dec(v_key_360_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_b_358_);
lean_ctor_set(v___x_364_, 0, v_a_357_);
v___x_372_ = v___x_364_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_b_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_tail_362_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
return v_x_375_;
}
else
{
lean_object* v_key_377_; lean_object* v_value_378_; lean_object* v_tail_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_405_; 
v_key_377_ = lean_ctor_get(v_x_376_, 0);
v_value_378_ = lean_ctor_get(v_x_376_, 1);
v_tail_379_ = lean_ctor_get(v_x_376_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_405_ == 0)
{
v___x_381_ = v_x_376_;
v_isShared_382_ = v_isSharedCheck_405_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_tail_379_);
lean_inc(v_value_378_);
lean_inc(v_key_377_);
lean_dec(v_x_376_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_405_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint64_t v___y_385_; 
v___x_383_ = lean_array_get_size(v_x_375_);
if (lean_obj_tag(v_key_377_) == 0)
{
uint64_t v___x_403_; 
v___x_403_ = 1723ULL;
v___y_385_ = v___x_403_;
goto v___jp_384_;
}
else
{
uint64_t v_hash_404_; 
v_hash_404_ = lean_ctor_get_uint64(v_key_377_, sizeof(void*)*2);
v___y_385_ = v_hash_404_;
goto v___jp_384_;
}
v___jp_384_:
{
uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v_fold_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_386_ = 32ULL;
v___x_387_ = lean_uint64_shift_right(v___y_385_, v___x_386_);
v_fold_388_ = lean_uint64_xor(v___y_385_, v___x_387_);
v___x_389_ = 16ULL;
v___x_390_ = lean_uint64_shift_right(v_fold_388_, v___x_389_);
v___x_391_ = lean_uint64_xor(v_fold_388_, v___x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = lean_usize_of_nat(v___x_383_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_sub(v___x_393_, v___x_394_);
v___x_396_ = lean_usize_land(v___x_392_, v___x_395_);
v___x_397_ = lean_array_uget_borrowed(v_x_375_, v___x_396_);
lean_inc(v___x_397_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 2, v___x_397_);
v___x_399_ = v___x_381_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_key_377_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_value_378_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v___x_397_);
v___x_399_ = v_reuseFailAlloc_402_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_array_uset(v_x_375_, v___x_396_, v___x_399_);
v_x_375_ = v___x_400_;
v_x_376_ = v_tail_379_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_406_, lean_object* v_source_407_, lean_object* v_target_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_array_get_size(v_source_407_);
v___x_410_ = lean_nat_dec_lt(v_i_406_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec_ref(v_source_407_);
lean_dec(v_i_406_);
return v_target_408_;
}
else
{
lean_object* v_es_411_; lean_object* v___x_412_; lean_object* v_source_413_; lean_object* v_target_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_es_411_ = lean_array_fget(v_source_407_, v_i_406_);
v___x_412_ = lean_box(0);
v_source_413_ = lean_array_fset(v_source_407_, v_i_406_, v___x_412_);
v_target_414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_408_, v_es_411_);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_i_406_, v___x_415_);
lean_dec(v_i_406_);
v_i_406_ = v___x_416_;
v_source_407_ = v_source_413_;
v_target_408_ = v_target_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_nbuckets_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_419_ = lean_array_get_size(v_data_418_);
v___x_420_ = lean_unsigned_to_nat(2u);
v_nbuckets_421_ = lean_nat_mul(v___x_419_, v___x_420_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_box(0);
v___x_424_ = lean_mk_array(v_nbuckets_421_, v___x_423_);
v___x_425_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_422_, v_data_418_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
else
{
lean_object* v_key_429_; lean_object* v_tail_430_; uint8_t v___x_431_; 
v_key_429_ = lean_ctor_get(v_x_427_, 0);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v___x_431_ = lean_name_eq(v_key_429_, v_a_426_);
if (v___x_431_ == 0)
{
v_x_427_ = v_tail_430_;
goto _start;
}
else
{
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_433_, v_x_434_);
lean_dec(v_x_434_);
lean_dec(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_size_440_; lean_object* v_buckets_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_487_; 
v_size_440_ = lean_ctor_get(v_m_437_, 0);
v_buckets_441_ = lean_ctor_get(v_m_437_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_m_437_);
if (v_isSharedCheck_487_ == 0)
{
v___x_443_ = v_m_437_;
v_isShared_444_ = v_isSharedCheck_487_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_buckets_441_);
lean_inc(v_size_440_);
lean_dec(v_m_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_487_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; uint64_t v___y_447_; 
v___x_445_ = lean_array_get_size(v_buckets_441_);
if (lean_obj_tag(v_a_438_) == 0)
{
uint64_t v___x_485_; 
v___x_485_ = 1723ULL;
v___y_447_ = v___x_485_;
goto v___jp_446_;
}
else
{
uint64_t v_hash_486_; 
v_hash_486_ = lean_ctor_get_uint64(v_a_438_, sizeof(void*)*2);
v___y_447_ = v_hash_486_;
goto v___jp_446_;
}
v___jp_446_:
{
uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v_fold_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v_bkt_459_; uint8_t v___x_460_; 
v___x_448_ = 32ULL;
v___x_449_ = lean_uint64_shift_right(v___y_447_, v___x_448_);
v_fold_450_ = lean_uint64_xor(v___y_447_, v___x_449_);
v___x_451_ = 16ULL;
v___x_452_ = lean_uint64_shift_right(v_fold_450_, v___x_451_);
v___x_453_ = lean_uint64_xor(v_fold_450_, v___x_452_);
v___x_454_ = lean_uint64_to_usize(v___x_453_);
v___x_455_ = lean_usize_of_nat(v___x_445_);
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_sub(v___x_455_, v___x_456_);
v___x_458_ = lean_usize_land(v___x_454_, v___x_457_);
v_bkt_459_ = lean_array_uget_borrowed(v_buckets_441_, v___x_458_);
v___x_460_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_438_, v_bkt_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v_size_x27_462_; lean_object* v___x_463_; lean_object* v_buckets_x27_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v_size_x27_462_ = lean_nat_add(v_size_440_, v___x_461_);
lean_dec(v_size_440_);
lean_inc(v_bkt_459_);
v___x_463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_463_, 0, v_a_438_);
lean_ctor_set(v___x_463_, 1, v_b_439_);
lean_ctor_set(v___x_463_, 2, v_bkt_459_);
v_buckets_x27_464_ = lean_array_uset(v_buckets_441_, v___x_458_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(4u);
v___x_466_ = lean_nat_mul(v_size_x27_462_, v___x_465_);
v___x_467_ = lean_unsigned_to_nat(3u);
v___x_468_ = lean_nat_div(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_array_get_size(v_buckets_x27_464_);
v___x_470_ = lean_nat_dec_le(v___x_468_, v___x_469_);
lean_dec(v___x_468_);
if (v___x_470_ == 0)
{
lean_object* v_val_471_; lean_object* v___x_473_; 
v_val_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_464_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_val_471_);
lean_ctor_set(v___x_443_, 0, v_size_x27_462_);
v___x_473_ = v___x_443_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_size_x27_462_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_val_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
else
{
lean_object* v___x_476_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_buckets_x27_464_);
lean_ctor_set(v___x_443_, 0, v_size_x27_462_);
v___x_476_ = v___x_443_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_size_x27_462_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_buckets_x27_464_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v___x_478_; lean_object* v_buckets_x27_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
lean_inc(v_bkt_459_);
v___x_478_ = lean_box(0);
v_buckets_x27_479_ = lean_array_uset(v_buckets_441_, v___x_458_, v___x_478_);
v___x_480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_438_, v_b_439_, v_bkt_459_);
v___x_481_ = lean_array_uset(v_buckets_x27_479_, v___x_458_, v___x_480_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_481_);
v___x_483_ = v___x_443_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_size_440_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v_ks_492_; lean_object* v_vs_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_517_; 
v_ks_492_ = lean_ctor_get(v_x_488_, 0);
v_vs_493_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_517_ == 0)
{
v___x_495_ = v_x_488_;
v_isShared_496_ = v_isSharedCheck_517_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_vs_493_);
lean_inc(v_ks_492_);
lean_dec(v_x_488_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_517_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_array_get_size(v_ks_492_);
v___x_498_ = lean_nat_dec_lt(v_x_489_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec(v_x_489_);
v___x_499_ = lean_array_push(v_ks_492_, v_x_490_);
v___x_500_ = lean_array_push(v_vs_493_, v_x_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_500_);
lean_ctor_set(v___x_495_, 0, v___x_499_);
v___x_502_ = v___x_495_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
else
{
lean_object* v_k_x27_504_; uint8_t v___x_505_; 
v_k_x27_504_ = lean_array_fget_borrowed(v_ks_492_, v_x_489_);
v___x_505_ = lean_name_eq(v_x_490_, v_k_x27_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_507_; 
if (v_isShared_496_ == 0)
{
v___x_507_ = v___x_495_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_ks_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_vs_493_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_x_489_, v___x_508_);
lean_dec(v_x_489_);
v_x_488_ = v___x_507_;
v_x_489_ = v___x_509_;
goto _start;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_array_fset(v_ks_492_, v_x_489_, v_x_490_);
v___x_513_ = lean_array_fset(v_vs_493_, v_x_489_, v_x_491_);
lean_dec(v_x_489_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_513_);
lean_ctor_set(v___x_495_, 0, v___x_512_);
v___x_515_ = v___x_495_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_518_, lean_object* v_k_519_, lean_object* v_v_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_518_, v___x_521_, v_k_519_, v_v_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_524_, size_t v_x_525_, size_t v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v_es_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v_j_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_es_529_ = lean_ctor_get(v_x_524_, 0);
v___x_530_ = ((size_t)31ULL);
v___x_531_ = lean_usize_land(v_x_525_, v___x_530_);
v_j_532_ = lean_usize_to_nat(v___x_531_);
v___x_533_ = lean_array_get_size(v_es_529_);
v___x_534_ = lean_nat_dec_lt(v_j_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v_j_532_);
lean_dec(v_x_528_);
lean_dec(v_x_527_);
return v_x_524_;
}
else
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_573_; 
lean_inc_ref(v_es_529_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_x_524_, 0);
lean_dec(v_unused_574_);
v___x_536_ = v_x_524_;
v_isShared_537_ = v_isSharedCheck_573_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_x_524_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_573_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_v_538_; lean_object* v___x_539_; lean_object* v_xs_x27_540_; lean_object* v___y_542_; 
v_v_538_ = lean_array_fget(v_es_529_, v_j_532_);
v___x_539_ = lean_box(0);
v_xs_x27_540_ = lean_array_fset(v_es_529_, v_j_532_, v___x_539_);
switch(lean_obj_tag(v_v_538_))
{
case 0:
{
lean_object* v_key_547_; lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_key_547_ = lean_ctor_get(v_v_538_, 0);
v_val_548_ = lean_ctor_get(v_v_538_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_v_538_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v_v_538_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_inc(v_key_547_);
lean_dec(v_v_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
uint8_t v___x_552_; 
v___x_552_ = lean_name_eq(v_x_527_, v_key_547_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_del_object(v___x_550_);
v___x_553_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_547_, v_val_548_, v_x_527_, v_x_528_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___y_542_ = v___x_554_;
goto v___jp_541_;
}
else
{
lean_object* v___x_556_; 
lean_dec(v_val_548_);
lean_dec(v_key_547_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_x_528_);
lean_ctor_set(v___x_550_, 0, v_x_527_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_x_527_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_x_528_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v___y_542_ = v___x_556_;
goto v___jp_541_;
}
}
}
}
case 1:
{
lean_object* v_node_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_571_; 
v_node_559_ = lean_ctor_get(v_v_538_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_v_538_);
if (v_isSharedCheck_571_ == 0)
{
v___x_561_ = v_v_538_;
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_node_559_);
lean_dec(v_v_538_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_usize_shift_right(v_x_525_, v___x_563_);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_x_526_, v___x_565_);
v___x_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_559_, v___x_564_, v___x_566_, v_x_527_, v_x_528_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_567_);
v___x_569_ = v___x_561_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v___y_542_ = v___x_569_;
goto v___jp_541_;
}
}
}
default: 
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_x_527_);
lean_ctor_set(v___x_572_, 1, v_x_528_);
v___y_542_ = v___x_572_;
goto v___jp_541_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_array_fset(v_xs_x27_540_, v_j_532_, v___y_542_);
lean_dec(v_j_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_543_);
v___x_545_ = v___x_536_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
else
{
lean_object* v_ks_575_; lean_object* v_vs_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_596_; 
v_ks_575_ = lean_ctor_get(v_x_524_, 0);
v_vs_576_ = lean_ctor_get(v_x_524_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_596_ == 0)
{
v___x_578_ = v_x_524_;
v_isShared_579_ = v_isSharedCheck_596_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_vs_576_);
lean_inc(v_ks_575_);
lean_dec(v_x_524_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_596_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_ks_575_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_vs_576_);
v___x_581_ = v_reuseFailAlloc_595_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v_newNode_582_; uint8_t v___y_584_; size_t v___x_590_; uint8_t v___x_591_; 
v_newNode_582_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_581_, v_x_527_, v_x_528_);
v___x_590_ = ((size_t)7ULL);
v___x_591_ = lean_usize_dec_le(v___x_590_, v_x_526_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_582_);
v___x_593_ = lean_unsigned_to_nat(4u);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
v___y_584_ = v___x_594_;
goto v___jp_583_;
}
else
{
v___y_584_ = v___x_591_;
goto v___jp_583_;
}
v___jp_583_:
{
if (v___y_584_ == 0)
{
lean_object* v_ks_585_; lean_object* v_vs_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_ks_585_ = lean_ctor_get(v_newNode_582_, 0);
lean_inc_ref(v_ks_585_);
v_vs_586_ = lean_ctor_get(v_newNode_582_, 1);
lean_inc_ref(v_vs_586_);
lean_dec_ref(v_newNode_582_);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_526_, v_ks_585_, v_vs_586_, v___x_587_, v___x_588_);
lean_dec_ref(v_vs_586_);
lean_dec_ref(v_ks_585_);
return v___x_589_;
}
else
{
return v_newNode_582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_597_, lean_object* v_keys_598_, lean_object* v_vals_599_, lean_object* v_i_600_, lean_object* v_entries_601_){
_start:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_array_get_size(v_keys_598_);
v___x_603_ = lean_nat_dec_lt(v_i_600_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec(v_i_600_);
return v_entries_601_;
}
else
{
lean_object* v_k_604_; lean_object* v_v_605_; uint64_t v___y_607_; 
v_k_604_ = lean_array_fget_borrowed(v_keys_598_, v_i_600_);
v_v_605_ = lean_array_fget_borrowed(v_vals_599_, v_i_600_);
if (lean_obj_tag(v_k_604_) == 0)
{
uint64_t v___x_618_; 
v___x_618_ = 1723ULL;
v___y_607_ = v___x_618_;
goto v___jp_606_;
}
else
{
uint64_t v_hash_619_; 
v_hash_619_ = lean_ctor_get_uint64(v_k_604_, sizeof(void*)*2);
v___y_607_ = v_hash_619_;
goto v___jp_606_;
}
v___jp_606_:
{
size_t v_h_608_; size_t v___x_609_; lean_object* v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v_h_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_h_608_ = lean_uint64_to_usize(v___y_607_);
v___x_609_ = ((size_t)5ULL);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_sub(v_depth_597_, v___x_611_);
v___x_613_ = lean_usize_mul(v___x_609_, v___x_612_);
v_h_614_ = lean_usize_shift_right(v_h_608_, v___x_613_);
v___x_615_ = lean_nat_add(v_i_600_, v___x_610_);
lean_dec(v_i_600_);
lean_inc(v_v_605_);
lean_inc(v_k_604_);
v___x_616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_601_, v_h_614_, v_depth_597_, v_k_604_, v_v_605_);
v_i_600_ = v___x_615_;
v_entries_601_ = v___x_616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_620_, lean_object* v_keys_621_, lean_object* v_vals_622_, lean_object* v_i_623_, lean_object* v_entries_624_){
_start:
{
size_t v_depth_boxed_625_; lean_object* v_res_626_; 
v_depth_boxed_625_ = lean_unbox_usize(v_depth_620_);
lean_dec(v_depth_620_);
v_res_626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_625_, v_keys_621_, v_vals_622_, v_i_623_, v_entries_624_);
lean_dec_ref(v_vals_622_);
lean_dec_ref(v_keys_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_1420__boxed_632_; size_t v_x_1421__boxed_633_; lean_object* v_res_634_; 
v_x_1420__boxed_632_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_x_1421__boxed_633_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_res_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_627_, v_x_1420__boxed_632_, v_x_1421__boxed_633_, v_x_630_, v_x_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
uint64_t v___y_639_; 
if (lean_obj_tag(v_x_636_) == 0)
{
uint64_t v___x_643_; 
v___x_643_ = 1723ULL;
v___y_639_ = v___x_643_;
goto v___jp_638_;
}
else
{
uint64_t v_hash_644_; 
v_hash_644_ = lean_ctor_get_uint64(v_x_636_, sizeof(void*)*2);
v___y_639_ = v_hash_644_;
goto v___jp_638_;
}
v___jp_638_:
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_uint64_to_usize(v___y_639_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_635_, v___x_640_, v___x_641_, v_x_636_, v_x_637_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
uint8_t v_stage_u2081_648_; 
v_stage_u2081_648_ = lean_ctor_get_uint8(v_x_645_, sizeof(void*)*2);
if (v_stage_u2081_648_ == 0)
{
lean_object* v_map_u2081_649_; lean_object* v_map_u2082_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_map_u2081_649_ = lean_ctor_get(v_x_645_, 0);
v_map_u2082_650_ = lean_ctor_get(v_x_645_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v_x_645_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_map_u2082_650_);
lean_inc(v_map_u2081_649_);
lean_dec(v_x_645_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_650_, v_x_646_, v_x_647_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_map_u2081_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_654_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*2, v_stage_u2081_648_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_object* v_map_u2081_659_; lean_object* v_map_u2082_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_map_u2081_659_ = lean_ctor_get(v_x_645_, 0);
v_map_u2082_660_ = lean_ctor_get(v_x_645_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v_x_645_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_map_u2082_660_);
lean_inc(v_map_u2081_659_);
lean_dec(v_x_645_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_659_, v_x_646_, v_x_647_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_map_u2082_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_667_, sizeof(void*)*2, v_stage_u2081_648_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(32u);
v___x_670_ = lean_mk_empty_array_with_capacity(v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = ((size_t)5ULL);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_unsigned_to_nat(32u);
v___x_675_ = lean_mk_empty_array_with_capacity(v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_677_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_673_);
lean_ctor_set(v___x_677_, 3, v___x_673_);
lean_ctor_set_usize(v___x_677_, 4, v___x_672_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_678_, lean_object* v_ns_679_, lean_object* v_b_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_678_, v_ns_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_683_ = l_Lean_PersistentArray_push___redArg(v___x_682_, v_b_680_);
v___x_684_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_678_, v_ns_679_, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_val_685_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_681_, 1);
v___x_686_ = l_Lean_PersistentArray_push___redArg(v_val_685_, v_b_680_);
v___x_687_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_678_, v_ns_679_, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_688_, lean_object* v_scopedEntries_689_, lean_object* v_ns_690_, lean_object* v_b_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_689_, v_ns_690_, v_b_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_697_, v_x_698_, v_x_699_);
lean_dec(v_x_699_);
lean_dec_ref(v_x_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_702_, v_x_703_, v_x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_710_, v_x_711_, v_x_712_);
lean_dec(v_x_712_);
lean_dec_ref(v_x_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_714_, lean_object* v_m_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_715_, v_a_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_718_, lean_object* v_m_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_718_, v_m_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_m_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_723_, v_x_724_, v_x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_727_, lean_object* v_m_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_728_, v_a_729_, v_b_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, size_t v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_733_, v_x_734_, v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_737_, lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
size_t v_x_1725__boxed_741_; lean_object* v_res_742_; 
v_x_1725__boxed_741_ = lean_unbox_usize(v_x_739_);
lean_dec(v_x_739_);
v_res_742_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_737_, v_x_738_, v_x_1725__boxed_741_, v_x_740_);
lean_dec(v_x_740_);
lean_dec_ref(v_x_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_743_, lean_object* v_a_744_, lean_object* v_x_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_747_, lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_747_, v_a_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec(v_a_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, size_t v_x_753_, size_t v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_752_, v_x_753_, v_x_754_, v_x_755_, v_x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_1741__boxed_764_; size_t v_x_1742__boxed_765_; lean_object* v_res_766_; 
v_x_1741__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_x_1742__boxed_765_ = lean_unbox_usize(v_x_761_);
lean_dec(v_x_761_);
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_758_, v_x_759_, v_x_1741__boxed_764_, v_x_1742__boxed_765_, v_x_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_767_, lean_object* v_a_768_, lean_object* v_x_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_771_, lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_771_, v_a_772_, v_x_773_);
lean_dec(v_x_773_);
lean_dec(v_a_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_776_, lean_object* v_data_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_779_, lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_780_, v_b_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_784_, lean_object* v_keys_785_, lean_object* v_vals_786_, lean_object* v_heq_787_, lean_object* v_i_788_, lean_object* v_k_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_785_, v_vals_786_, v_i_788_, v_k_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_791_, lean_object* v_keys_792_, lean_object* v_vals_793_, lean_object* v_heq_794_, lean_object* v_i_795_, lean_object* v_k_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_791_, v_keys_792_, v_vals_793_, v_heq_794_, v_i_795_, v_k_796_);
lean_dec(v_k_796_);
lean_dec_ref(v_vals_793_);
lean_dec_ref(v_keys_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_798_, lean_object* v_n_799_, lean_object* v_k_800_, lean_object* v_v_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_799_, v_k_800_, v_v_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_803_, size_t v_depth_804_, lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_heq_807_, lean_object* v_i_808_, lean_object* v_entries_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_804_, v_keys_805_, v_vals_806_, v_i_808_, v_entries_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_811_, lean_object* v_depth_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_heq_815_, lean_object* v_i_816_, lean_object* v_entries_817_){
_start:
{
size_t v_depth_boxed_818_; lean_object* v_res_819_; 
v_depth_boxed_818_ = lean_unbox_usize(v_depth_812_);
lean_dec(v_depth_812_);
v_res_819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_811_, v_depth_boxed_818_, v_keys_813_, v_vals_814_, v_heq_815_, v_i_816_, v_entries_817_);
lean_dec_ref(v_vals_814_);
lean_dec_ref(v_keys_813_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_820_, lean_object* v_i_821_, lean_object* v_source_822_, lean_object* v_target_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_821_, v_source_822_, v_target_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_826_, v_x_827_, v_x_828_, v_x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_835_, lean_object* v_as_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_a_843_; uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v_descr_835_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_839_);
return v___x_848_;
}
else
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_889_; 
v_fst_849_ = lean_ctor_get(v_b_839_, 0);
v_snd_850_ = lean_ctor_get(v_b_839_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_b_839_);
if (v_isSharedCheck_889_ == 0)
{
v___x_852_ = v_b_839_;
v_isShared_853_ = v_isSharedCheck_889_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_b_839_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_889_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_a_854_; 
v_a_854_ = lean_array_uget_borrowed(v_as_836_, v_i_838_);
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_ofOLeanEntry_856_; lean_object* v_addEntry_857_; lean_object* v___x_858_; 
v_a_855_ = lean_ctor_get(v_a_854_, 0);
v_ofOLeanEntry_856_ = lean_ctor_get(v_descr_835_, 2);
v_addEntry_857_ = lean_ctor_get(v_descr_835_, 4);
lean_inc_ref(v_ofOLeanEntry_856_);
lean_inc_ref(v___y_840_);
lean_inc(v_a_855_);
lean_inc(v_fst_849_);
v___x_858_ = lean_apply_4(v_ofOLeanEntry_856_, v_fst_849_, v_a_855_, v___y_840_, lean_box(0));
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
lean_inc(v_addEntry_857_);
v___x_860_ = lean_apply_2(v_addEntry_857_, v_fst_849_, v_a_859_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_860_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_snd_850_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v_a_843_ = v___x_862_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_fst_849_);
lean_dec_ref(v_descr_835_);
v_a_864_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_858_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v_ofOLeanEntry_874_; lean_object* v___x_875_; 
v_a_872_ = lean_ctor_get(v_a_854_, 0);
v_a_873_ = lean_ctor_get(v_a_854_, 1);
v_ofOLeanEntry_874_ = lean_ctor_get(v_descr_835_, 2);
lean_inc_ref(v_ofOLeanEntry_874_);
lean_inc_ref(v___y_840_);
lean_inc(v_a_873_);
lean_inc(v_fst_849_);
v___x_875_ = lean_apply_4(v_ofOLeanEntry_874_, v_fst_849_, v_a_873_, v___y_840_, lean_box(0));
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
lean_inc(v_a_872_);
v___x_877_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_850_, v_a_872_, v_a_876_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_877_);
v___x_879_ = v___x_852_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
v_a_843_ = v___x_879_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_fst_849_);
lean_dec_ref(v_descr_835_);
v_a_881_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_875_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_875_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
v___jp_842_:
{
size_t v___x_844_; size_t v___x_845_; 
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_838_, v___x_844_);
v_i_838_ = v___x_845_;
v_b_839_ = v_a_843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_890_, lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_898_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_890_, v_as_891_, v_sz_boxed_897_, v_i_boxed_898_, v_b_894_, v___y_895_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_as_891_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_900_, lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec_ref(v_descr_900_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_b_904_);
return v___x_908_;
}
else
{
lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_934_; 
v_fst_909_ = lean_ctor_get(v_b_904_, 0);
v_snd_910_ = lean_ctor_get(v_b_904_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_b_904_);
if (v_isSharedCheck_934_ == 0)
{
v___x_912_ = v_b_904_;
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_inc(v_fst_909_);
lean_dec(v_b_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_a_914_; lean_object* v___x_916_; 
v_a_914_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
if (v_isShared_913_ == 0)
{
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_909_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_snd_910_);
v___x_916_ = v_reuseFailAlloc_933_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
size_t v_sz_917_; size_t v___x_918_; lean_object* v___x_919_; 
v_sz_917_ = lean_array_size(v_a_914_);
v___x_918_ = ((size_t)0ULL);
lean_inc_ref(v_descr_900_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_900_, v_a_914_, v_sz_917_, v___x_918_, v___x_916_, v___y_905_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v_fst_921_ = lean_ctor_get(v_a_920_, 0);
v_snd_922_ = lean_ctor_get(v_a_920_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_920_);
if (v_isSharedCheck_932_ == 0)
{
v___x_924_ = v_a_920_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snd_922_);
lean_inc(v_fst_921_);
lean_dec(v_a_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_snd_922_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
size_t v___x_928_; size_t v___x_929_; 
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_903_, v___x_928_);
v_i_903_ = v___x_929_;
v_b_904_ = v___x_927_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_900_);
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_935_, lean_object* v_as_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_943_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_935_, v_as_936_, v_sz_boxed_942_, v_i_boxed_943_, v_b_939_, v___y_940_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v_as_936_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_945_, lean_object* v_as_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_mkInitial_949_; lean_object* v_finalizeImport_950_; lean_object* v___x_951_; 
v_mkInitial_949_ = lean_ctor_get(v_descr_945_, 1);
v_finalizeImport_950_ = lean_ctor_get(v_descr_945_, 5);
lean_inc(v_finalizeImport_950_);
lean_inc_ref(v_mkInitial_949_);
v___x_951_ = lean_apply_1(v_mkInitial_949_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; size_t v_sz_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = 1;
v___x_954_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_a_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v_sz_956_ = lean_array_size(v_as_946_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_945_, v_as_946_, v_sz_956_, v___x_957_, v___x_955_, v_a_947_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_980_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_980_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_980_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_fst_963_; lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_979_; 
v_fst_963_ = lean_ctor_get(v_a_959_, 0);
v_snd_964_ = lean_ctor_get(v_a_959_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_979_ == 0)
{
v___x_966_ = v_a_959_;
v_isShared_967_ = v_isSharedCheck_979_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_inc(v_fst_963_);
lean_dec(v_a_959_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_979_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_968_ = lean_apply_1(v_finalizeImport_950_, v_fst_963_);
v___x_969_ = l_Lean_NameSet_empty;
v___x_970_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*2, v___x_953_);
v___x_971_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 1);
lean_ctor_set(v___x_966_, 1, v___x_971_);
lean_ctor_set(v___x_966_, 0, v___x_970_);
v___x_973_ = v___x_966_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_978_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_snd_964_);
lean_ctor_set(v___x_974_, 2, v___x_971_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_974_);
v___x_976_ = v___x_961_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_finalizeImport_950_);
v_a_981_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_958_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_958_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_finalizeImport_950_);
lean_dec_ref(v_descr_945_);
v_a_989_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_951_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_951_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_997_, lean_object* v_as_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_997_, v_as_998_, v_a_999_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_as_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_00_u03c3_1004_, lean_object* v_descr_1005_, lean_object* v_as_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1005_, v_as_1006_, v_a_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_00_u03c3_1012_, lean_object* v_descr_1013_, lean_object* v_as_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1010_, v_00_u03b2_1011_, v_00_u03c3_1012_, v_descr_1013_, v_as_1014_, v_a_1015_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_as_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03c3_1019_, lean_object* v_00_u03b2_1020_, lean_object* v_descr_1021_, lean_object* v_as_1022_, size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1021_, v_as_1022_, v_sz_1023_, v_i_1024_, v_b_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03c3_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_descr_1032_, lean_object* v_as_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
size_t v_sz_boxed_1039_; size_t v_i_boxed_1040_; lean_object* v_res_1041_; 
v_sz_boxed_1039_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1029_, v_00_u03c3_1030_, v_00_u03b2_1031_, v_descr_1032_, v_as_1033_, v_sz_boxed_1039_, v_i_boxed_1040_, v_b_1036_, v___y_1037_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v_as_1033_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03c3_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_descr_1045_, lean_object* v_as_1046_, size_t v_sz_1047_, size_t v_i_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1045_, v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1053_, lean_object* v_00_u03c3_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_descr_1056_, lean_object* v_as_1057_, lean_object* v_sz_1058_, lean_object* v_i_1059_, lean_object* v_b_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1058_);
lean_dec(v_sz_1058_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1053_, v_00_u03c3_1054_, v_00_u03b2_1055_, v_descr_1056_, v_as_1057_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1060_, v___y_1061_);
lean_dec_ref(v___y_1061_);
lean_dec_ref(v_as_1057_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1066_, lean_object* v_descr_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
if (lean_obj_tag(v_a_1069_) == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_a_1068_);
lean_dec_ref(v_descr_1067_);
v___x_1071_ = l_List_reverse___redArg(v_a_1070_);
return v___x_1071_;
}
else
{
lean_object* v_head_1072_; lean_object* v_tail_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1098_; 
v_head_1072_ = lean_ctor_get(v_a_1069_, 0);
v_tail_1073_ = lean_ctor_get(v_a_1069_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_a_1069_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1075_ = v_a_1069_;
v_isShared_1076_ = v_isSharedCheck_1098_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_tail_1073_);
lean_inc(v_head_1072_);
lean_dec(v_a_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1098_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; lean_object* v_state_1083_; lean_object* v_activeScopes_1084_; uint8_t v_delimitsLocal_1085_; uint8_t v___x_1086_; 
v_state_1083_ = lean_ctor_get(v_head_1072_, 0);
v_activeScopes_1084_ = lean_ctor_get(v_head_1072_, 1);
v_delimitsLocal_1085_ = lean_ctor_get_uint8(v_head_1072_, sizeof(void*)*2);
v___x_1086_ = l_Lean_NameSet_contains(v_activeScopes_1084_, v_a_1066_);
if (v___x_1086_ == 0)
{
v___y_1078_ = v_head_1072_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1095_; 
lean_inc(v_activeScopes_1084_);
lean_inc(v_state_1083_);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_head_1072_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1096_ = lean_ctor_get(v_head_1072_, 1);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_head_1072_, 0);
lean_dec(v_unused_1097_);
v___x_1088_ = v_head_1072_;
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_head_1072_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_addEntry_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_addEntry_1090_ = lean_ctor_get(v_descr_1067_, 4);
lean_inc(v_addEntry_1090_);
lean_inc(v_a_1068_);
v___x_1091_ = lean_apply_2(v_addEntry_1090_, v_state_1083_, v_a_1068_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_activeScopes_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1094_, sizeof(void*)*2, v_delimitsLocal_1085_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v___y_1078_ = v___x_1093_;
goto v___jp_1077_;
}
}
}
v___jp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_a_1070_);
lean_ctor_set(v___x_1075_, 0, v___y_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___y_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1070_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_a_1069_ = v_tail_1073_;
v_a_1070_ = v___x_1080_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1099_, lean_object* v_descr_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1099_, v_descr_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
if (lean_obj_tag(v_a_1107_) == 0)
{
lean_object* v___x_1109_; 
lean_dec(v_a_1106_);
lean_dec_ref(v_descr_1105_);
v___x_1109_ = l_List_reverse___redArg(v_a_1108_);
return v___x_1109_;
}
else
{
lean_object* v_head_1110_; lean_object* v_tail_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1131_; 
v_head_1110_ = lean_ctor_get(v_a_1107_, 0);
v_tail_1111_ = lean_ctor_get(v_a_1107_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1113_ = v_a_1107_;
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_tail_1111_);
lean_inc(v_head_1110_);
lean_dec(v_a_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_addEntry_1115_; lean_object* v_state_1116_; lean_object* v_activeScopes_1117_; uint8_t v_delimitsLocal_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1130_; 
v_addEntry_1115_ = lean_ctor_get(v_descr_1105_, 4);
v_state_1116_ = lean_ctor_get(v_head_1110_, 0);
v_activeScopes_1117_ = lean_ctor_get(v_head_1110_, 1);
v_delimitsLocal_1118_ = lean_ctor_get_uint8(v_head_1110_, sizeof(void*)*2);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_head_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1120_ = v_head_1110_;
v_isShared_1121_ = v_isSharedCheck_1130_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_activeScopes_1117_);
lean_inc(v_state_1116_);
lean_dec(v_head_1110_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1130_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_inc(v_addEntry_1115_);
lean_inc(v_a_1106_);
v___x_1122_ = lean_apply_2(v_addEntry_1115_, v_state_1116_, v_a_1106_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_activeScopes_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*2, v_delimitsLocal_1118_);
v___x_1124_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v_a_1108_);
lean_ctor_set(v___x_1113_, 0, v___x_1124_);
v___x_1126_ = v___x_1113_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1108_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v_a_1107_ = v_tail_1111_;
v_a_1108_ = v___x_1126_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1132_, lean_object* v_s_1133_, lean_object* v_e_1134_){
_start:
{
if (lean_obj_tag(v_e_1134_) == 0)
{
lean_object* v_stateStack_1135_; lean_object* v_scopedEntries_1136_; lean_object* v_newEntries_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1157_; 
v_stateStack_1135_ = lean_ctor_get(v_s_1133_, 0);
v_scopedEntries_1136_ = lean_ctor_get(v_s_1133_, 1);
v_newEntries_1137_ = lean_ctor_get(v_s_1133_, 2);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_s_1133_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1139_ = v_s_1133_;
v_isShared_1140_ = v_isSharedCheck_1157_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_newEntries_1137_);
lean_inc(v_scopedEntries_1136_);
lean_inc(v_stateStack_1135_);
lean_dec(v_s_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1157_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1156_; 
v_a_1141_ = lean_ctor_get(v_e_1134_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_e_1134_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1143_ = v_e_1134_;
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_e_1134_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_toOLeanEntry_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_toOLeanEntry_1145_ = lean_ctor_get(v_descr_1132_, 3);
lean_inc(v_toOLeanEntry_1145_);
v___x_1146_ = lean_box(0);
lean_inc(v_a_1141_);
v___x_1147_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1132_, v_a_1141_, v_stateStack_1135_, v___x_1146_);
v___x_1148_ = lean_apply_1(v_toOLeanEntry_1145_, v_a_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1148_);
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v_newEntries_1137_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 2, v___x_1151_);
lean_ctor_set(v___x_1139_, 0, v___x_1147_);
v___x_1153_ = v___x_1139_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_scopedEntries_1136_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1158_; lean_object* v_scopedEntries_1159_; lean_object* v_newEntries_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1182_; 
v_stateStack_1158_ = lean_ctor_get(v_s_1133_, 0);
v_scopedEntries_1159_ = lean_ctor_get(v_s_1133_, 1);
v_newEntries_1160_ = lean_ctor_get(v_s_1133_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_s_1133_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1162_ = v_s_1133_;
v_isShared_1163_ = v_isSharedCheck_1182_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_newEntries_1160_);
lean_inc(v_scopedEntries_1159_);
lean_inc(v_stateStack_1158_);
lean_dec(v_s_1133_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1182_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1181_; 
v_a_1164_ = lean_ctor_get(v_e_1134_, 0);
v_a_1165_ = lean_ctor_get(v_e_1134_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_e_1134_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1167_ = v_e_1134_;
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_inc(v_a_1164_);
lean_dec(v_e_1134_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1181_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_toOLeanEntry_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v_toOLeanEntry_1169_ = lean_ctor_get(v_descr_1132_, 3);
lean_inc(v_toOLeanEntry_1169_);
v___x_1170_ = lean_box(0);
lean_inc_n(v_a_1165_, 2);
v___x_1171_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1164_, v_descr_1132_, v_a_1165_, v_stateStack_1158_, v___x_1170_);
lean_inc(v_a_1164_);
v___x_1172_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1159_, v_a_1164_, v_a_1165_);
v___x_1173_ = lean_apply_1(v_toOLeanEntry_1169_, v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1173_);
v___x_1175_ = v___x_1167_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1164_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_newEntries_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 2, v___x_1176_);
lean_ctor_set(v___x_1162_, 1, v___x_1172_);
lean_ctor_set(v___x_1162_, 0, v___x_1171_);
v___x_1178_ = v___x_1162_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_00_u03c3_1185_, lean_object* v_descr_1186_, lean_object* v_s_1187_, lean_object* v_e_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1186_, v_s_1187_, v_e_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_00_u03b1_1192_, lean_object* v_descr_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1198_, lean_object* v_a_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_00_u03b1_1201_, lean_object* v_descr_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1199_, v_descr_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1207_, lean_object* v_a_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_00_u03b1_1210_, lean_object* v_descr_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1207_, v_a_1208_, v_00_u03b2_1209_, v_00_u03b1_1210_, v_descr_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1208_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1216_, lean_object* v_env_1217_, lean_object* v_as_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v_a_1223_; uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v_env_1217_);
lean_dec_ref(v_descr_1216_);
return v_b_1221_;
}
else
{
lean_object* v_snd_1228_; lean_object* v_fst_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1329_; 
v_snd_1228_ = lean_ctor_get(v_b_1221_, 1);
v_fst_1229_ = lean_ctor_get(v_b_1221_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_b_1221_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1231_ = v_b_1221_;
v_isShared_1232_ = v_isSharedCheck_1329_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snd_1228_);
lean_inc(v_fst_1229_);
lean_dec(v_b_1221_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1329_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1328_; 
v_fst_1233_ = lean_ctor_get(v_snd_1228_, 0);
v_snd_1234_ = lean_ctor_get(v_snd_1228_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_snd_1228_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1236_ = v_snd_1228_;
v_isShared_1237_ = v_isSharedCheck_1328_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1233_);
lean_dec(v_snd_1228_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1328_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_a_1238_; 
v_a_1238_ = lean_array_uget(v_as_1218_, v_i_1220_);
if (lean_obj_tag(v_a_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1288_; 
v_a_1239_ = lean_ctor_get(v_a_1238_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1241_ = v_a_1238_;
v_isShared_1242_ = v_isSharedCheck_1288_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v_a_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1288_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_exportEntry_x3f_1243_; lean_object* v___x_1244_; lean_object* v_exported_1245_; lean_object* v_server_1246_; lean_object* v_private_1247_; lean_object* v___y_1249_; lean_object* v_server_1250_; lean_object* v_exported_1269_; 
v_exportEntry_x3f_1243_ = lean_ctor_get(v_descr_1216_, 6);
lean_inc_ref(v_exportEntry_x3f_1243_);
lean_inc_ref(v_env_1217_);
v___x_1244_ = lean_apply_2(v_exportEntry_x3f_1243_, v_env_1217_, v_a_1239_);
v_exported_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_exported_1245_);
v_server_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_server_1246_);
v_private_1247_ = lean_ctor_get(v___x_1244_, 2);
lean_inc(v_private_1247_);
lean_dec_ref(v___x_1244_);
if (lean_obj_tag(v_exported_1245_) == 1)
{
lean_object* v_val_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_val_1279_ = lean_ctor_get(v_exported_1245_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_exported_1245_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v_exported_1245_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_val_1279_);
lean_dec(v_exported_1245_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 0);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1279_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_array_push(v_fst_1229_, v___x_1284_);
v_exported_1269_ = v___x_1285_;
goto v___jp_1268_;
}
}
}
else
{
lean_dec(v_exported_1245_);
v_exported_1269_ = v_fst_1229_;
goto v___jp_1268_;
}
v___jp_1248_:
{
if (lean_obj_tag(v_private_1247_) == 1)
{
lean_object* v_val_1251_; lean_object* v___x_1253_; 
v_val_1251_ = lean_ctor_get(v_private_1247_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v_private_1247_, 1);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_val_1251_);
v___x_1253_ = v___x_1241_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1251_);
v___x_1253_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_array_push(v_snd_1234_, v___x_1253_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___x_1254_);
lean_ctor_set(v___x_1236_, 0, v_server_1250_);
v___x_1256_ = v___x_1236_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_server_1250_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1256_);
lean_ctor_set(v___x_1231_, 0, v___y_1249_);
v___x_1258_ = v___x_1231_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___y_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_a_1223_ = v___x_1258_;
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v_private_1247_);
lean_del_object(v___x_1241_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_server_1250_);
v___x_1263_ = v___x_1236_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_server_1250_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_snd_1234_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1263_);
lean_ctor_set(v___x_1231_, 0, v___y_1249_);
v___x_1265_ = v___x_1231_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___y_1249_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v_a_1223_ = v___x_1265_;
goto v___jp_1222_;
}
}
}
}
v___jp_1268_:
{
if (lean_obj_tag(v_server_1246_) == 1)
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_val_1270_ = lean_ctor_get(v_server_1246_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_server_1246_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v_server_1246_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v_server_1246_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 0);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_val_1270_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_array_push(v_fst_1233_, v___x_1275_);
v___y_1249_ = v_exported_1269_;
v_server_1250_ = v___x_1276_;
goto v___jp_1248_;
}
}
}
else
{
lean_dec(v_server_1246_);
v___y_1249_ = v_exported_1269_;
v_server_1250_ = v_fst_1233_;
goto v___jp_1248_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1327_; 
v_a_1289_ = lean_ctor_get(v_a_1238_, 0);
v_a_1290_ = lean_ctor_get(v_a_1238_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1292_ = v_a_1238_;
v_isShared_1293_ = v_isSharedCheck_1327_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_inc(v_a_1289_);
lean_dec(v_a_1238_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1327_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_exportEntry_x3f_1294_; lean_object* v___x_1295_; lean_object* v_exported_1296_; lean_object* v_server_1297_; lean_object* v_private_1298_; lean_object* v___y_1300_; lean_object* v_server_1301_; lean_object* v_exported_1320_; 
v_exportEntry_x3f_1294_ = lean_ctor_get(v_descr_1216_, 6);
lean_inc_ref(v_exportEntry_x3f_1294_);
lean_inc_ref(v_env_1217_);
v___x_1295_ = lean_apply_2(v_exportEntry_x3f_1294_, v_env_1217_, v_a_1290_);
v_exported_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_exported_1296_);
v_server_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_server_1297_);
v_private_1298_ = lean_ctor_get(v___x_1295_, 2);
lean_inc(v_private_1298_);
lean_dec_ref(v___x_1295_);
if (lean_obj_tag(v_exported_1296_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_val_1324_ = lean_ctor_get(v_exported_1296_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v_exported_1296_, 1);
lean_inc(v_a_1289_);
v___x_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_a_1289_);
lean_ctor_set(v___x_1325_, 1, v_val_1324_);
v___x_1326_ = lean_array_push(v_fst_1229_, v___x_1325_);
v_exported_1320_ = v___x_1326_;
goto v___jp_1319_;
}
else
{
lean_dec(v_exported_1296_);
v_exported_1320_ = v_fst_1229_;
goto v___jp_1319_;
}
v___jp_1299_:
{
if (lean_obj_tag(v_private_1298_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
v_val_1302_ = lean_ctor_get(v_private_1298_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_private_1298_, 1);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v_val_1302_);
v___x_1304_ = v___x_1292_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_array_push(v_snd_1234_, v___x_1304_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v___x_1305_);
lean_ctor_set(v___x_1236_, 0, v_server_1301_);
v___x_1307_ = v___x_1236_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_server_1301_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1307_);
lean_ctor_set(v___x_1231_, 0, v___y_1300_);
v___x_1309_ = v___x_1231_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___y_1300_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v_a_1223_ = v___x_1309_;
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v___x_1314_; 
lean_dec(v_private_1298_);
lean_del_object(v___x_1292_);
lean_dec(v_a_1289_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_server_1301_);
v___x_1314_ = v___x_1236_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_server_1301_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_snd_1234_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1314_);
lean_ctor_set(v___x_1231_, 0, v___y_1300_);
v___x_1316_ = v___x_1231_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___y_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_a_1223_ = v___x_1316_;
goto v___jp_1222_;
}
}
}
}
v___jp_1319_:
{
if (lean_obj_tag(v_server_1297_) == 1)
{
lean_object* v_val_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_val_1321_ = lean_ctor_get(v_server_1297_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v_server_1297_, 1);
lean_inc(v_a_1289_);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_a_1289_);
lean_ctor_set(v___x_1322_, 1, v_val_1321_);
v___x_1323_ = lean_array_push(v_fst_1233_, v___x_1322_);
v___y_1300_ = v_exported_1320_;
v_server_1301_ = v___x_1323_;
goto v___jp_1299_;
}
else
{
lean_dec(v_server_1297_);
v___y_1300_ = v_exported_1320_;
v_server_1301_ = v_fst_1233_;
goto v___jp_1299_;
}
}
}
}
}
}
}
v___jp_1222_:
{
size_t v___x_1224_; size_t v___x_1225_; 
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_add(v_i_1220_, v___x_1224_);
v_i_1220_ = v___x_1225_;
v_b_1221_ = v_a_1223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1330_, lean_object* v_env_1331_, lean_object* v_as_1332_, lean_object* v_sz_1333_, lean_object* v_i_1334_, lean_object* v_b_1335_){
_start:
{
size_t v_sz_boxed_1336_; size_t v_i_boxed_1337_; lean_object* v_res_1338_; 
v_sz_boxed_1336_ = lean_unbox_usize(v_sz_1333_);
lean_dec(v_sz_1333_);
v_i_boxed_1337_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_res_1338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1330_, v_env_1331_, v_as_1332_, v_sz_boxed_1336_, v_i_boxed_1337_, v_b_1335_);
lean_dec_ref(v_as_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1346_, lean_object* v_env_1347_, lean_object* v_s_1348_){
_start:
{
lean_object* v_newEntries_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1366_; 
v_newEntries_1349_ = lean_ctor_get(v_s_1348_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_s_1348_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; 
v_unused_1367_ = lean_ctor_get(v_s_1348_, 1);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_s_1348_, 0);
lean_dec(v_unused_1368_);
v___x_1351_ = v_s_1348_;
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_newEntries_1349_);
lean_dec(v_s_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v_snd_1359_; lean_object* v_fst_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; 
v___x_1353_ = lean_array_mk(v_newEntries_1349_);
v___x_1354_ = l_Array_reverse___redArg(v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1356_ = lean_array_size(v___x_1354_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1346_, v_env_1347_, v___x_1354_, v_sz_1356_, v___x_1357_, v___x_1355_);
lean_dec_ref(v___x_1354_);
v_snd_1359_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_snd_1359_);
v_fst_1360_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_fst_1360_);
lean_dec_ref(v___x_1358_);
v_fst_1361_ = lean_ctor_get(v_snd_1359_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v_snd_1359_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_snd_1359_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 2, v_snd_1362_);
lean_ctor_set(v___x_1351_, 1, v_fst_1361_);
lean_ctor_set(v___x_1351_, 0, v_fst_1360_);
v___x_1364_ = v___x_1351_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1360_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_snd_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_00_u03c3_1371_, lean_object* v_descr_1372_, lean_object* v_env_1373_, lean_object* v_s_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1372_, v_env_1373_, v_s_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_00_u03c3_1378_, lean_object* v_descr_1379_, lean_object* v_env_1380_, lean_object* v_as_1381_, size_t v_sz_1382_, size_t v_i_1383_, lean_object* v_b_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1379_, v_env_1380_, v_as_1381_, v_sz_1382_, v_i_1383_, v_b_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_00_u03c3_1388_, lean_object* v_descr_1389_, lean_object* v_env_1390_, lean_object* v_as_1391_, lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_b_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1386_, v_00_u03b2_1387_, v_00_u03c3_1388_, v_descr_1389_, v_env_1390_, v_as_1391_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1394_);
lean_dec_ref(v_as_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1403_, v___y_1404_);
lean_dec_ref(v___y_1404_);
lean_dec_ref(v_x_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1407_, lean_object* v_x_1408_){
_start:
{
lean_inc_ref(v_s_1407_);
return v_s_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1409_, v_x_1410_);
lean_dec_ref(v_x_1410_);
lean_dec_ref(v_s_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1417_, v_x_1418_);
lean_dec_ref(v_x_1418_);
lean_dec_ref(v_x_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1422_);
lean_dec_ref(v_x_1422_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1429_; lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___f_1429_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1430_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1431_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1432_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1435_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___x_1433_);
lean_ctor_set(v___x_1435_, 2, v___f_1432_);
lean_ctor_set(v___x_1435_, 3, v___f_1431_);
lean_ctor_set(v___x_1435_, 4, v___f_1430_);
lean_ctor_set(v___x_1435_, 5, v___f_1429_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1436_){
_start:
{
lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___f_1437_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1438_, 0, v_inst_1436_);
v___f_1439_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1440_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1443_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1444_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1441_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v___f_1437_);
lean_ctor_set(v___x_1444_, 3, v___f_1438_);
lean_ctor_set(v___x_1444_, 4, v___f_1439_);
lean_ctor_set(v___x_1444_, 5, v___x_1443_);
lean_ctor_set(v___x_1444_, 6, v___f_1440_);
v___x_1445_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_00_u03c3_1449_, lean_object* v_inst_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1454_, lean_object* v_inst_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1463_ = lean_st_mk_ref(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1470_){
_start:
{
lean_object* v_newEntries_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_newEntries_1471_ = lean_ctor_get(v_s_1470_, 2);
v___x_1472_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1473_ = l_List_lengthTR___redArg(v_newEntries_1471_);
v___x_1474_ = l_Nat_reprFast(v___x_1473_);
v___x_1475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1472_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1477_);
lean_dec_ref(v_s_1477_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1481_);
lean_dec_ref(v_x_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1485_){
_start:
{
lean_object* v_name_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_name_1487_ = lean_ctor_get(v_descr_1485_, 0);
v___f_1488_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1489_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1485_, 4);
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, lean_box(0));
lean_closure_set(v___x_1490_, 2, lean_box(0));
lean_closure_set(v___x_1490_, 3, v_descr_1485_);
v___x_1491_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1491_, 0, lean_box(0));
lean_closure_set(v___x_1491_, 1, lean_box(0));
lean_closure_set(v___x_1491_, 2, lean_box(0));
lean_closure_set(v___x_1491_, 3, v_descr_1485_);
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, lean_box(0));
lean_closure_set(v___x_1492_, 3, v_descr_1485_);
v___x_1493_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1493_, 0, lean_box(0));
lean_closure_set(v___x_1493_, 1, lean_box(0));
lean_closure_set(v___x_1493_, 2, lean_box(0));
lean_closure_set(v___x_1493_, 3, v_descr_1485_);
v___x_1494_ = lean_box(2);
v___x_1495_ = lean_box(0);
lean_inc(v_name_1487_);
v___x_1496_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1496_, 0, v_name_1487_);
lean_ctor_set(v___x_1496_, 1, v___x_1490_);
lean_ctor_set(v___x_1496_, 2, v___x_1491_);
lean_ctor_set(v___x_1496_, 3, v___x_1492_);
lean_ctor_set(v___x_1496_, 4, v___x_1493_);
lean_ctor_set(v___x_1496_, 5, v___f_1488_);
lean_ctor_set(v___x_1496_, 6, v___x_1494_);
lean_ctor_set(v___x_1496_, 7, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___f_1489_);
v___x_1498_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1511_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1511_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1511_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1503_ = l_Lean_scopedEnvExtensionsRef;
v___x_1504_ = lean_st_ref_take(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_descr_1485_);
lean_ctor_set(v___x_1505_, 1, v_a_1499_);
lean_inc_ref(v___x_1505_);
v___x_1506_ = lean_array_push(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_st_ref_set(v___x_1503_, v___x_1506_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1505_);
v___x_1509_ = v___x_1501_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1505_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v_descr_1485_);
v_a_1512_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1498_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1498_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_00_u03c3_1525_, lean_object* v_descr_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_00_u03b2_1530_, lean_object* v_00_u03c3_1531_, lean_object* v_descr_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1529_, v_00_u03b2_1530_, v_00_u03c3_1531_, v_descr_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1535_){
_start:
{
lean_object* v_stateStack_1536_; 
v_stateStack_1536_ = lean_ctor_get(v_s_1535_, 0);
if (lean_obj_tag(v_stateStack_1536_) == 0)
{
return v_s_1535_;
}
else
{
lean_object* v_head_1537_; lean_object* v_scopedEntries_1538_; lean_object* v_newEntries_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1557_; 
lean_inc_ref(v_stateStack_1536_);
v_head_1537_ = lean_ctor_get(v_stateStack_1536_, 0);
lean_inc(v_head_1537_);
v_scopedEntries_1538_ = lean_ctor_get(v_s_1535_, 1);
v_newEntries_1539_ = lean_ctor_get(v_s_1535_, 2);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_s_1535_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_s_1535_, 0);
lean_dec(v_unused_1558_);
v___x_1541_ = v_s_1535_;
v_isShared_1542_ = v_isSharedCheck_1557_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_newEntries_1539_);
lean_inc(v_scopedEntries_1538_);
lean_dec(v_s_1535_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1557_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_state_1543_; lean_object* v_activeScopes_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1556_; 
v_state_1543_ = lean_ctor_get(v_head_1537_, 0);
v_activeScopes_1544_ = lean_ctor_get(v_head_1537_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_head_1537_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1546_ = v_head_1537_;
v_isShared_1547_ = v_isSharedCheck_1556_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_activeScopes_1544_);
lean_inc(v_state_1543_);
lean_dec(v_head_1537_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1556_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint8_t v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = 1;
if (v_isShared_1547_ == 0)
{
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_state_1543_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_activeScopes_1544_);
v___x_1550_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*2, v___x_1548_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_stateStack_1536_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1551_);
v___x_1553_ = v___x_1541_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_scopedEntries_1538_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_newEntries_1539_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1560_, lean_object* v_env_1561_){
_start:
{
lean_object* v_ext_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_ext_1562_ = lean_ctor_get(v_ext_1560_, 1);
lean_inc_ref(v_ext_1562_);
lean_dec_ref(v_ext_1560_);
v___f_1563_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1564_ = lean_box(1);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1562_, v_env_1561_, v___f_1563_, v___x_1564_, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_00_u03c3_1569_, lean_object* v_ext_1570_, lean_object* v_env_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1570_, v_env_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1573_){
_start:
{
lean_object* v_stateStack_1574_; 
v_stateStack_1574_ = lean_ctor_get(v_s_1573_, 0);
if (lean_obj_tag(v_stateStack_1574_) == 1)
{
lean_object* v_tail_1575_; 
v_tail_1575_ = lean_ctor_get(v_stateStack_1574_, 1);
if (lean_obj_tag(v_tail_1575_) == 1)
{
lean_object* v_scopedEntries_1576_; lean_object* v_newEntries_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_inc_ref(v_tail_1575_);
v_scopedEntries_1576_ = lean_ctor_get(v_s_1573_, 1);
v_newEntries_1577_ = lean_ctor_get(v_s_1573_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_s_1573_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_s_1573_, 0);
lean_dec(v_unused_1585_);
v___x_1579_ = v_s_1573_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_newEntries_1577_);
lean_inc(v_scopedEntries_1576_);
lean_dec(v_s_1573_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_tail_1575_);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_tail_1575_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_scopedEntries_1576_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_newEntries_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
return v_s_1573_;
}
}
else
{
return v_s_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1587_, lean_object* v_env_1588_){
_start:
{
lean_object* v_ext_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_ext_1589_ = lean_ctor_get(v_ext_1587_, 1);
lean_inc_ref(v_ext_1589_);
lean_dec_ref(v_ext_1587_);
v___f_1590_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1591_ = lean_box(1);
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1589_, v_env_1588_, v___f_1590_, v___x_1591_, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_00_u03c3_1596_, lean_object* v_ext_1597_, lean_object* v_env_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1597_, v_env_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_zero_1602_; uint8_t v_isZero_1603_; 
v_zero_1602_ = lean_unsigned_to_nat(0u);
v_isZero_1603_ = lean_nat_dec_eq(v_a_1600_, v_zero_1602_);
if (v_isZero_1603_ == 1)
{
return v_a_1601_;
}
else
{
if (lean_obj_tag(v_a_1601_) == 0)
{
return v_a_1601_;
}
else
{
lean_object* v_head_1604_; lean_object* v_tail_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1624_; 
v_head_1604_ = lean_ctor_get(v_a_1601_, 0);
v_tail_1605_ = lean_ctor_get(v_a_1601_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_a_1601_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1607_ = v_a_1601_;
v_isShared_1608_ = v_isSharedCheck_1624_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_tail_1605_);
lean_inc(v_head_1604_);
lean_dec(v_a_1601_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1624_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_state_1609_; lean_object* v_activeScopes_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1623_; 
v_state_1609_ = lean_ctor_get(v_head_1604_, 0);
v_activeScopes_1610_ = lean_ctor_get(v_head_1604_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_head_1604_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1612_ = v_head_1604_;
v_isShared_1613_ = v_isSharedCheck_1623_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_activeScopes_1610_);
lean_inc(v_state_1609_);
lean_dec(v_head_1604_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1623_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_one_1614_; lean_object* v_n_1615_; lean_object* v___x_1617_; 
v_one_1614_ = lean_unsigned_to_nat(1u);
v_n_1615_ = lean_nat_sub(v_a_1600_, v_one_1614_);
if (v_isShared_1613_ == 0)
{
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_state_1609_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_activeScopes_1610_);
v___x_1617_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*2, v_isZero_1603_);
v___x_1618_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1615_, v_tail_1605_);
lean_dec(v_n_1615_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 1, v___x_1618_);
lean_ctor_set(v___x_1607_, 0, v___x_1617_);
v___x_1620_ = v___x_1607_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1625_, v_a_1626_);
lean_dec(v_a_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1629_, v_a_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1636_, lean_object* v_s_1637_){
_start:
{
lean_object* v_stateStack_1638_; lean_object* v_scopedEntries_1639_; lean_object* v_newEntries_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_stateStack_1638_ = lean_ctor_get(v_s_1637_, 0);
v_scopedEntries_1639_ = lean_ctor_get(v_s_1637_, 1);
v_newEntries_1640_ = lean_ctor_get(v_s_1637_, 2);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_s_1637_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v_s_1637_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_newEntries_1640_);
lean_inc(v_scopedEntries_1639_);
lean_inc(v_stateStack_1638_);
lean_dec(v_s_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1636_, v_stateStack_1638_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_scopedEntries_1639_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_newEntries_1640_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1649_, lean_object* v_s_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1649_, v_s_1650_);
lean_dec(v_depth_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1652_, lean_object* v_env_1653_, lean_object* v_depth_1654_){
_start:
{
lean_object* v_ext_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_ext_1655_ = lean_ctor_get(v_ext_1652_, 1);
lean_inc_ref(v_ext_1655_);
lean_dec_ref(v_ext_1652_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1656_, 0, v_depth_1654_);
v___x_1657_ = lean_box(1);
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1655_, v_env_1653_, v___f_1656_, v___x_1657_, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_00_u03c3_1662_, lean_object* v_ext_1663_, lean_object* v_env_1664_, lean_object* v_depth_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1663_, v_env_1664_, v_depth_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1667_, lean_object* v_env_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v_ext_1670_; lean_object* v_toEnvExtension_1671_; lean_object* v_asyncMode_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_ext_1670_ = lean_ctor_get(v_ext_1667_, 1);
lean_inc_ref(v_ext_1670_);
lean_dec_ref(v_ext_1667_);
v_toEnvExtension_1671_ = lean_ctor_get(v_ext_1670_, 0);
v_asyncMode_1672_ = lean_ctor_get(v_toEnvExtension_1671_, 2);
lean_inc(v_asyncMode_1672_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_b_1669_);
v___x_1674_ = lean_box(0);
v___x_1675_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1670_, v_env_1668_, v___x_1673_, v_asyncMode_1672_, v___x_1674_);
lean_dec(v_asyncMode_1672_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1676_, lean_object* v_00_u03b2_1677_, lean_object* v_00_u03c3_1678_, lean_object* v_ext_1679_, lean_object* v_env_1680_, lean_object* v_b_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1679_, v_env_1680_, v_b_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1683_, lean_object* v_env_1684_, lean_object* v_namespaceName_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v_ext_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1698_; 
v_ext_1687_ = lean_ctor_get(v_ext_1683_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_ext_1683_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_ext_1683_, 0);
lean_dec(v_unused_1699_);
v___x_1689_ = v_ext_1683_;
v_isShared_1690_ = v_isSharedCheck_1698_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_ext_1687_);
lean_dec(v_ext_1683_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1698_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_toEnvExtension_1691_; lean_object* v_asyncMode_1692_; lean_object* v___x_1694_; 
v_toEnvExtension_1691_ = lean_ctor_get(v_ext_1687_, 0);
v_asyncMode_1692_ = lean_ctor_get(v_toEnvExtension_1691_, 2);
lean_inc(v_asyncMode_1692_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 1);
lean_ctor_set(v___x_1689_, 1, v_b_1686_);
lean_ctor_set(v___x_1689_, 0, v_namespaceName_1685_);
v___x_1694_ = v___x_1689_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_namespaceName_1685_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_b_1686_);
v___x_1694_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_box(0);
v___x_1696_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1687_, v_env_1684_, v___x_1694_, v_asyncMode_1692_, v___x_1695_);
lean_dec(v_asyncMode_1692_);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_00_u03c3_1702_, lean_object* v_ext_1703_, lean_object* v_env_1704_, lean_object* v_namespaceName_1705_, lean_object* v_b_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1703_, v_env_1704_, v_namespaceName_1705_, v_b_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1708_, lean_object* v_states_1709_, lean_object* v_b_1710_){
_start:
{
if (lean_obj_tag(v_states_1709_) == 0)
{
lean_dec(v_b_1710_);
lean_dec_ref(v_ext_1708_);
return v_states_1709_;
}
else
{
lean_object* v_descr_1711_; lean_object* v_head_1712_; lean_object* v_tail_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1736_; 
v_descr_1711_ = lean_ctor_get(v_ext_1708_, 0);
v_head_1712_ = lean_ctor_get(v_states_1709_, 0);
v_tail_1713_ = lean_ctor_get(v_states_1709_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_states_1709_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1715_ = v_states_1709_;
v_isShared_1716_ = v_isSharedCheck_1736_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_tail_1713_);
lean_inc(v_head_1712_);
lean_dec(v_states_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1736_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_addEntry_1717_; lean_object* v_state_1718_; lean_object* v_activeScopes_1719_; uint8_t v_delimitsLocal_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1735_; 
v_addEntry_1717_ = lean_ctor_get(v_descr_1711_, 4);
v_state_1718_ = lean_ctor_get(v_head_1712_, 0);
v_activeScopes_1719_ = lean_ctor_get(v_head_1712_, 1);
v_delimitsLocal_1720_ = lean_ctor_get_uint8(v_head_1712_, sizeof(void*)*2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_head_1712_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1722_ = v_head_1712_;
v_isShared_1723_ = v_isSharedCheck_1735_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_activeScopes_1719_);
lean_inc(v_state_1718_);
lean_dec(v_head_1712_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1735_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v_top_1726_; 
lean_inc(v_addEntry_1717_);
lean_inc(v_b_1710_);
v___x_1724_ = lean_apply_2(v_addEntry_1717_, v_state_1718_, v_b_1710_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v_top_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_activeScopes_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2, v_delimitsLocal_1720_);
v_top_1726_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
if (v_delimitsLocal_1720_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_stateStackModify___redArg(v_ext_1708_, v_tail_1713_, v_b_1710_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1727_);
lean_ctor_set(v___x_1715_, 0, v_top_1726_);
v___x_1729_ = v___x_1715_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_top_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v_b_1710_);
lean_dec_ref(v_ext_1708_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v_top_1726_);
v___x_1732_ = v___x_1715_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_top_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_tail_1713_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_00_u03c3_1739_, lean_object* v_ext_1740_, lean_object* v_states_1741_, lean_object* v_b_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_stateStackModify___redArg(v_ext_1740_, v_states_1741_, v_b_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1744_, lean_object* v_b_1745_, lean_object* v_s_1746_){
_start:
{
lean_object* v_stateStack_1747_; lean_object* v_scopedEntries_1748_; lean_object* v_newEntries_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
v_stateStack_1747_ = lean_ctor_get(v_s_1746_, 0);
v_scopedEntries_1748_ = lean_ctor_get(v_s_1746_, 1);
v_newEntries_1749_ = lean_ctor_get(v_s_1746_, 2);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_s_1746_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v_s_1746_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_newEntries_1749_);
lean_inc(v_scopedEntries_1748_);
lean_inc(v_stateStack_1747_);
lean_dec(v_s_1746_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_stateStackModify___redArg(v_ext_1744_, v_stateStack_1747_, v_b_1745_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_scopedEntries_1748_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_newEntries_1749_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1758_, lean_object* v_env_1759_, lean_object* v_b_1760_){
_start:
{
lean_object* v_ext_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_ext_1761_ = lean_ctor_get(v_ext_1758_, 1);
lean_inc_ref(v_ext_1761_);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1762_, 0, v_ext_1758_);
lean_closure_set(v___f_1762_, 1, v_b_1760_);
v___x_1763_ = lean_box(1);
v___x_1764_ = lean_box(0);
v___x_1765_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1761_, v_env_1759_, v___f_1762_, v___x_1763_, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_00_u03c3_1768_, lean_object* v_ext_1769_, lean_object* v_env_1770_, lean_object* v_b_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1769_, v_env_1770_, v_b_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1773_, lean_object* v_ext_1774_, lean_object* v_b_1775_, uint8_t v_kind_1776_, lean_object* v_namespaceName_1777_){
_start:
{
switch(v_kind_1776_)
{
case 0:
{
lean_object* v___x_1778_; 
lean_dec(v_namespaceName_1777_);
v___x_1778_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1774_, v_env_1773_, v_b_1775_);
return v___x_1778_;
}
case 1:
{
lean_object* v___x_1779_; 
lean_dec(v_namespaceName_1777_);
v___x_1779_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1774_, v_env_1773_, v_b_1775_);
return v___x_1779_;
}
default: 
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1774_, v_env_1773_, v_namespaceName_1777_, v_b_1775_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1781_, lean_object* v_ext_1782_, lean_object* v_b_1783_, lean_object* v_kind_1784_, lean_object* v_namespaceName_1785_){
_start:
{
uint8_t v_kind_boxed_1786_; lean_object* v_res_1787_; 
v_kind_boxed_1786_ = lean_unbox(v_kind_1784_);
v_res_1787_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1781_, v_ext_1782_, v_b_1783_, v_kind_boxed_1786_, v_namespaceName_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1788_, lean_object* v_00_u03b2_1789_, lean_object* v_00_u03c3_1790_, lean_object* v_env_1791_, lean_object* v_ext_1792_, lean_object* v_b_1793_, uint8_t v_kind_1794_, lean_object* v_namespaceName_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1791_, v_ext_1792_, v_b_1793_, v_kind_1794_, v_namespaceName_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b2_1798_, lean_object* v_00_u03c3_1799_, lean_object* v_env_1800_, lean_object* v_ext_1801_, lean_object* v_b_1802_, lean_object* v_kind_1803_, lean_object* v_namespaceName_1804_){
_start:
{
uint8_t v_kind_boxed_1805_; lean_object* v_res_1806_; 
v_kind_boxed_1805_ = lean_unbox(v_kind_1803_);
v_res_1806_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1797_, v_00_u03b2_1798_, v_00_u03c3_1799_, v_env_1800_, v_ext_1801_, v_b_1802_, v_kind_boxed_1805_, v_namespaceName_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1807_, lean_object* v_b_1808_, uint8_t v_kind_1809_, lean_object* v_ns_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1811_, v_ext_1807_, v_b_1808_, v_kind_1809_, v_ns_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1813_, lean_object* v_b_1814_, lean_object* v_kind_1815_, lean_object* v_ns_1816_, lean_object* v_x_1817_){
_start:
{
uint8_t v_kind_boxed_1818_; lean_object* v_res_1819_; 
v_kind_boxed_1818_ = lean_unbox(v_kind_1815_);
v_res_1819_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1813_, v_b_1814_, v_kind_boxed_1818_, v_ns_1816_, v_x_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1820_, lean_object* v_ext_1821_, lean_object* v_b_1822_, uint8_t v_kind_1823_, lean_object* v_ns_1824_){
_start:
{
lean_object* v_modifyEnv_1825_; lean_object* v___x_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; 
v_modifyEnv_1825_ = lean_ctor_get(v_inst_1820_, 1);
lean_inc(v_modifyEnv_1825_);
lean_dec_ref(v_inst_1820_);
v___x_1826_ = lean_box(v_kind_1823_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1827_, 0, v_ext_1821_);
lean_closure_set(v___f_1827_, 1, v_b_1822_);
lean_closure_set(v___f_1827_, 2, v___x_1826_);
lean_closure_set(v___f_1827_, 3, v_ns_1824_);
v___x_1828_ = lean_apply_1(v_modifyEnv_1825_, v___f_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1829_, lean_object* v_ext_1830_, lean_object* v_b_1831_, lean_object* v_kind_1832_, lean_object* v_ns_1833_){
_start:
{
uint8_t v_kind_boxed_1834_; lean_object* v_res_1835_; 
v_kind_boxed_1834_ = lean_unbox(v_kind_1832_);
v_res_1835_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1829_, v_ext_1830_, v_b_1831_, v_kind_boxed_1834_, v_ns_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_ext_1839_, lean_object* v_b_1840_, uint8_t v_kind_1841_){
_start:
{
lean_object* v_toBind_1842_; lean_object* v_getCurrNamespace_1843_; lean_object* v___x_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; 
v_toBind_1842_ = lean_ctor_get(v_inst_1836_, 1);
lean_inc(v_toBind_1842_);
lean_dec_ref(v_inst_1836_);
v_getCurrNamespace_1843_ = lean_ctor_get(v_inst_1837_, 0);
lean_inc(v_getCurrNamespace_1843_);
lean_dec_ref(v_inst_1837_);
v___x_1844_ = lean_box(v_kind_1841_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1845_, 0, v_inst_1838_);
lean_closure_set(v___f_1845_, 1, v_ext_1839_);
lean_closure_set(v___f_1845_, 2, v_b_1840_);
lean_closure_set(v___f_1845_, 3, v___x_1844_);
v___x_1846_ = lean_apply_4(v_toBind_1842_, lean_box(0), lean_box(0), v_getCurrNamespace_1843_, v___f_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_ext_1850_, lean_object* v_b_1851_, lean_object* v_kind_1852_){
_start:
{
uint8_t v_kind_boxed_1853_; lean_object* v_res_1854_; 
v_kind_boxed_1853_ = lean_unbox(v_kind_1852_);
v_res_1854_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1847_, v_inst_1848_, v_inst_1849_, v_ext_1850_, v_b_1851_, v_kind_boxed_1853_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1855_, lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_00_u03c3_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_ext_1862_, lean_object* v_b_1863_, uint8_t v_kind_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1859_, v_inst_1860_, v_inst_1861_, v_ext_1862_, v_b_1863_, v_kind_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1866_, lean_object* v_00_u03b1_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_00_u03c3_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_ext_1873_, lean_object* v_b_1874_, lean_object* v_kind_1875_){
_start:
{
uint8_t v_kind_boxed_1876_; lean_object* v_res_1877_; 
v_kind_boxed_1876_ = lean_unbox(v_kind_1875_);
v_res_1877_ = l_Lean_ScopedEnvExtension_add(v_m_1866_, v_00_u03b1_1867_, v_00_u03b2_1868_, v_00_u03c3_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_ext_1873_, v_b_1874_, v_kind_boxed_1876_);
return v_res_1877_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1881_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1882_ = lean_unsigned_to_nat(16u);
v___x_1883_ = lean_unsigned_to_nat(209u);
v___x_1884_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1885_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1886_ = l_mkPanicMessageWithDecl(v___x_1885_, v___x_1884_, v___x_1883_, v___x_1882_, v___x_1881_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1887_, lean_object* v_ext_1888_, lean_object* v_env_1889_, lean_object* v_asyncMode_1890_){
_start:
{
lean_object* v_ext_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_stateStack_1895_; 
v_ext_1891_ = lean_ctor_get(v_ext_1888_, 1);
v___x_1892_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1893_ = lean_box(0);
v___x_1894_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1892_, v_ext_1891_, v_env_1889_, v_asyncMode_1890_, v___x_1893_);
v_stateStack_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_stateStack_1895_);
lean_dec(v___x_1894_);
if (lean_obj_tag(v_stateStack_1895_) == 1)
{
lean_object* v_head_1896_; lean_object* v_state_1897_; 
v_head_1896_ = lean_ctor_get(v_stateStack_1895_, 0);
lean_inc(v_head_1896_);
lean_dec_ref_known(v_stateStack_1895_, 2);
v_state_1897_ = lean_ctor_get(v_head_1896_, 0);
lean_inc(v_state_1897_);
lean_dec(v_head_1896_);
return v_state_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_stateStack_1895_);
v___x_1898_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1899_ = l_panic___redArg(v_inst_1887_, v___x_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1900_, lean_object* v_ext_1901_, lean_object* v_env_1902_, lean_object* v_asyncMode_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1900_, v_ext_1901_, v_env_1902_, v_asyncMode_1903_);
lean_dec(v_asyncMode_1903_);
lean_dec_ref(v_ext_1901_);
lean_dec(v_inst_1900_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1905_, lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_inst_1908_, lean_object* v_ext_1909_, lean_object* v_env_1910_, lean_object* v_asyncMode_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1908_, v_ext_1909_, v_env_1910_, v_asyncMode_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1913_, lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_inst_1916_, lean_object* v_ext_1917_, lean_object* v_env_1918_, lean_object* v_asyncMode_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1913_, v_00_u03b1_1914_, v_00_u03b2_1915_, v_inst_1916_, v_ext_1917_, v_env_1918_, v_asyncMode_1919_);
lean_dec(v_asyncMode_1919_);
lean_dec_ref(v_ext_1917_);
lean_dec(v_inst_1916_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1921_, lean_object* v_as_1922_, size_t v_sz_1923_, size_t v_i_1924_, lean_object* v_b_1925_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_lt(v_i_1924_, v_sz_1923_);
if (v___x_1926_ == 0)
{
lean_dec_ref(v_ext_1921_);
return v_b_1925_;
}
else
{
lean_object* v_descr_1927_; lean_object* v_snd_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1942_; 
v_descr_1927_ = lean_ctor_get(v_ext_1921_, 0);
v_snd_1928_ = lean_ctor_get(v_b_1925_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_b_1925_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_b_1925_, 0);
lean_dec(v_unused_1943_);
v___x_1930_ = v_b_1925_;
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snd_1928_);
lean_dec(v_b_1925_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_addEntry_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; lean_object* v_state_1935_; lean_object* v___x_1937_; 
v_addEntry_1932_ = lean_ctor_get(v_descr_1927_, 4);
v___x_1933_ = lean_box(0);
v_a_1934_ = lean_array_uget_borrowed(v_as_1922_, v_i_1924_);
lean_inc(v_addEntry_1932_);
lean_inc(v_a_1934_);
v_state_1935_ = lean_apply_2(v_addEntry_1932_, v_snd_1928_, v_a_1934_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_state_1935_);
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_state_1935_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
size_t v___x_1938_; size_t v___x_1939_; 
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_add(v_i_1924_, v___x_1938_);
v_i_1924_ = v___x_1939_;
v_b_1925_ = v___x_1937_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1944_, v_as_1945_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1948_);
lean_dec_ref(v_as_1945_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1952_, lean_object* v_as_1953_, size_t v_sz_1954_, size_t v_i_1955_, lean_object* v_b_1956_){
_start:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_usize_dec_lt(v_i_1955_, v_sz_1954_);
if (v___x_1957_ == 0)
{
lean_dec_ref(v_ext_1952_);
return v_b_1956_;
}
else
{
lean_object* v_descr_1958_; lean_object* v_snd_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1973_; 
v_descr_1958_ = lean_ctor_get(v_ext_1952_, 0);
v_snd_1959_ = lean_ctor_get(v_b_1956_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_b_1956_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_b_1956_, 0);
lean_dec(v_unused_1974_);
v___x_1961_ = v_b_1956_;
v_isShared_1962_ = v_isSharedCheck_1973_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_snd_1959_);
lean_dec(v_b_1956_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1973_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_addEntry_1963_; lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v_state_1966_; lean_object* v___x_1968_; 
v_addEntry_1963_ = lean_ctor_get(v_descr_1958_, 4);
v___x_1964_ = lean_box(0);
v_a_1965_ = lean_array_uget_borrowed(v_as_1953_, v_i_1955_);
lean_inc(v_addEntry_1963_);
lean_inc(v_a_1965_);
v_state_1966_ = lean_apply_2(v_addEntry_1963_, v_snd_1959_, v_a_1965_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 1, v_state_1966_);
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1968_ = v___x_1961_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_state_1966_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1955_, v___x_1969_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1952_, v_as_1953_, v_sz_1954_, v___x_1970_, v___x_1968_);
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1975_, lean_object* v_as_1976_, lean_object* v_sz_1977_, lean_object* v_i_1978_, lean_object* v_b_1979_){
_start:
{
size_t v_sz_boxed_1980_; size_t v_i_boxed_1981_; lean_object* v_res_1982_; 
v_sz_boxed_1980_ = lean_unbox_usize(v_sz_1977_);
lean_dec(v_sz_1977_);
v_i_boxed_1981_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1975_, v_as_1976_, v_sz_boxed_1980_, v_i_boxed_1981_, v_b_1979_);
lean_dec_ref(v_as_1976_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1983_, lean_object* v_ext_1984_, lean_object* v_n_1985_, lean_object* v_b_1986_){
_start:
{
if (lean_obj_tag(v_n_1985_) == 0)
{
lean_object* v_cs_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; size_t v_sz_1990_; size_t v___x_1991_; lean_object* v___x_1992_; lean_object* v_fst_1993_; 
v_cs_1987_ = lean_ctor_get(v_n_1985_, 0);
v___x_1988_ = lean_box(0);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_b_1986_);
v_sz_1990_ = lean_array_size(v_cs_1987_);
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1983_, v_ext_1984_, v_cs_1987_, v_sz_1990_, v___x_1991_, v___x_1989_);
v_fst_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_fst_1993_);
if (lean_obj_tag(v_fst_1993_) == 0)
{
lean_object* v_snd_1994_; lean_object* v___x_1995_; 
v_snd_1994_ = lean_ctor_get(v___x_1992_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v___x_1992_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_snd_1994_);
return v___x_1995_;
}
else
{
lean_object* v_val_1996_; 
lean_dec_ref(v___x_1992_);
v_val_1996_ = lean_ctor_get(v_fst_1993_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v_fst_1993_, 1);
return v_val_1996_;
}
}
else
{
lean_object* v_vs_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; size_t v_sz_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v_fst_2003_; 
v_vs_1997_ = lean_ctor_get(v_n_1985_, 0);
v___x_1998_ = lean_box(0);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v_b_1986_);
v_sz_2000_ = lean_array_size(v_vs_1997_);
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1984_, v_vs_1997_, v_sz_2000_, v___x_2001_, v___x_1999_);
v_fst_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_fst_2003_);
if (lean_obj_tag(v_fst_2003_) == 0)
{
lean_object* v_snd_2004_; lean_object* v___x_2005_; 
v_snd_2004_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_snd_2004_);
lean_dec_ref(v___x_2002_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_snd_2004_);
return v___x_2005_;
}
else
{
lean_object* v_val_2006_; 
lean_dec_ref(v___x_2002_);
v_val_2006_ = lean_ctor_get(v_fst_2003_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v_fst_2003_, 1);
return v_val_2006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2007_, lean_object* v_ext_2008_, lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v_ext_2008_);
return v_b_2012_;
}
else
{
lean_object* v_snd_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2032_; 
v_snd_2014_ = lean_ctor_get(v_b_2012_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_b_2012_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_b_2012_, 0);
lean_dec(v_unused_2033_);
v___x_2016_ = v_b_2012_;
v_isShared_2017_ = v_isSharedCheck_2032_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_snd_2014_);
lean_dec(v_b_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2032_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
lean_inc(v_snd_2014_);
lean_inc_ref(v_ext_2008_);
v___x_2019_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2007_, v_ext_2008_, v_a_2018_, v_snd_2014_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec_ref(v_ext_2008_);
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2020_);
v___x_2022_ = v___x_2016_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2014_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec(v_snd_2014_);
v_a_2024_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2025_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v_a_2024_);
lean_ctor_set(v___x_2016_, 0, v___x_2025_);
v___x_2027_ = v___x_2016_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_a_2024_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
size_t v___x_2028_; size_t v___x_2029_; 
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2011_, v___x_2028_);
v_i_2011_ = v___x_2029_;
v_b_2012_ = v___x_2027_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2034_, lean_object* v_ext_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_){
_start:
{
size_t v_sz_boxed_2040_; size_t v_i_boxed_2041_; lean_object* v_res_2042_; 
v_sz_boxed_2040_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2041_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2034_, v_ext_2035_, v_as_2036_, v_sz_boxed_2040_, v_i_boxed_2041_, v_b_2039_);
lean_dec_ref(v_as_2036_);
lean_dec(v_init_2034_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2043_, lean_object* v_ext_2044_, lean_object* v_n_2045_, lean_object* v_b_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2043_, v_ext_2044_, v_n_2045_, v_b_2046_);
lean_dec_ref(v_n_2045_);
lean_dec(v_init_2043_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2048_, lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v_ext_2048_);
return v_b_2052_;
}
else
{
lean_object* v_descr_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2069_; 
v_descr_2054_ = lean_ctor_get(v_ext_2048_, 0);
v_snd_2055_ = lean_ctor_get(v_b_2052_, 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_b_2052_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v_b_2052_, 0);
lean_dec(v_unused_2070_);
v___x_2057_ = v_b_2052_;
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_dec(v_b_2052_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_addEntry_2059_; lean_object* v___x_2060_; lean_object* v_a_2061_; lean_object* v_state_2062_; lean_object* v___x_2064_; 
v_addEntry_2059_ = lean_ctor_get(v_descr_2054_, 4);
v___x_2060_ = lean_box(0);
v_a_2061_ = lean_array_uget_borrowed(v_as_2049_, v_i_2051_);
lean_inc(v_addEntry_2059_);
lean_inc(v_a_2061_);
v_state_2062_ = lean_apply_2(v_addEntry_2059_, v_snd_2055_, v_a_2061_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_state_2062_);
lean_ctor_set(v___x_2057_, 0, v___x_2060_);
v___x_2064_ = v___x_2057_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_state_2062_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
size_t v___x_2065_; size_t v___x_2066_; 
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_add(v_i_2051_, v___x_2065_);
v_i_2051_ = v___x_2066_;
v_b_2052_ = v___x_2064_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2071_, lean_object* v_as_2072_, lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_b_2075_){
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2071_, v_as_2072_, v_sz_boxed_2076_, v_i_boxed_2077_, v_b_2075_);
lean_dec_ref(v_as_2072_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2079_, lean_object* v_as_2080_, size_t v_sz_2081_, size_t v_i_2082_, lean_object* v_b_2083_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2082_, v_sz_2081_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v_ext_2079_);
return v_b_2083_;
}
else
{
lean_object* v_descr_2085_; lean_object* v_snd_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2100_; 
v_descr_2085_ = lean_ctor_get(v_ext_2079_, 0);
v_snd_2086_ = lean_ctor_get(v_b_2083_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_b_2083_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v_b_2083_, 0);
lean_dec(v_unused_2101_);
v___x_2088_ = v_b_2083_;
v_isShared_2089_ = v_isSharedCheck_2100_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snd_2086_);
lean_dec(v_b_2083_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2100_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_addEntry_2090_; lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v_state_2093_; lean_object* v___x_2095_; 
v_addEntry_2090_ = lean_ctor_get(v_descr_2085_, 4);
v___x_2091_ = lean_box(0);
v_a_2092_ = lean_array_uget_borrowed(v_as_2080_, v_i_2082_);
lean_inc(v_addEntry_2090_);
lean_inc(v_a_2092_);
v_state_2093_ = lean_apply_2(v_addEntry_2090_, v_snd_2086_, v_a_2092_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v_state_2093_);
lean_ctor_set(v___x_2088_, 0, v___x_2091_);
v___x_2095_ = v___x_2088_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_state_2093_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = ((size_t)1ULL);
v___x_2097_ = lean_usize_add(v_i_2082_, v___x_2096_);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2079_, v_as_2080_, v_sz_2081_, v___x_2097_, v___x_2095_);
return v___x_2098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2102_, lean_object* v_as_2103_, lean_object* v_sz_2104_, lean_object* v_i_2105_, lean_object* v_b_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2104_);
lean_dec(v_sz_2104_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2102_, v_as_2103_, v_sz_boxed_2107_, v_i_boxed_2108_, v_b_2106_);
lean_dec_ref(v_as_2103_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2110_, lean_object* v_t_2111_, lean_object* v_init_2112_){
_start:
{
lean_object* v_root_2113_; lean_object* v_tail_2114_; lean_object* v___x_2115_; 
v_root_2113_ = lean_ctor_get(v_t_2111_, 0);
v_tail_2114_ = lean_ctor_get(v_t_2111_, 1);
lean_inc_ref(v_ext_2110_);
lean_inc(v_init_2112_);
v___x_2115_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2112_, v_ext_2110_, v_root_2113_, v_init_2112_);
lean_dec(v_init_2112_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
lean_dec_ref(v_ext_2110_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
return v_a_2116_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; lean_object* v_fst_2123_; 
v_a_2117_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_a_2117_);
v_sz_2120_ = lean_array_size(v_tail_2114_);
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2110_, v_tail_2114_, v_sz_2120_, v___x_2121_, v___x_2119_);
v_fst_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_fst_2123_);
if (lean_obj_tag(v_fst_2123_) == 0)
{
lean_object* v_snd_2124_; 
v_snd_2124_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_snd_2124_);
lean_dec_ref(v___x_2122_);
return v_snd_2124_;
}
else
{
lean_object* v_val_2125_; 
lean_dec_ref(v___x_2122_);
v_val_2125_ = lean_ctor_get(v_fst_2123_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_fst_2123_, 1);
return v_val_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2126_, lean_object* v_t_2127_, lean_object* v_init_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2126_, v_t_2127_, v_init_2128_);
lean_dec_ref(v_t_2127_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2130_, lean_object* v_ext_2131_, lean_object* v_s_2132_){
_start:
{
lean_object* v_stateStack_2133_; 
v_stateStack_2133_ = lean_ctor_get(v_s_2132_, 0);
lean_inc(v_stateStack_2133_);
if (lean_obj_tag(v_stateStack_2133_) == 1)
{
lean_object* v_scopedEntries_2134_; lean_object* v_newEntries_2135_; lean_object* v_head_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2166_; 
v_scopedEntries_2134_ = lean_ctor_get(v_s_2132_, 1);
v_newEntries_2135_ = lean_ctor_get(v_s_2132_, 2);
v_head_2136_ = lean_ctor_get(v_stateStack_2133_, 0);
v_tail_2137_ = lean_ctor_get(v_stateStack_2133_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_stateStack_2133_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2139_ = v_stateStack_2133_;
v_isShared_2140_ = v_isSharedCheck_2166_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_head_2136_);
lean_dec(v_stateStack_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2166_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___y_2142_; lean_object* v_state_2147_; lean_object* v_activeScopes_2148_; uint8_t v_delimitsLocal_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2165_; 
v_state_2147_ = lean_ctor_get(v_head_2136_, 0);
v_activeScopes_2148_ = lean_ctor_get(v_head_2136_, 1);
v_delimitsLocal_2149_ = lean_ctor_get_uint8(v_head_2136_, sizeof(void*)*2);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_head_2136_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2151_ = v_head_2136_;
v_isShared_2152_ = v_isSharedCheck_2165_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_activeScopes_2148_);
lean_inc(v_state_2147_);
lean_dec(v_head_2136_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2165_;
goto v_resetjp_2150_;
}
v___jp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___y_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___y_2142_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_tail_2137_);
v___x_2144_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; 
v___x_2145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_scopedEntries_2134_);
lean_ctor_set(v___x_2145_, 2, v_newEntries_2135_);
return v___x_2145_;
}
}
v_resetjp_2150_:
{
uint8_t v___x_2153_; 
v___x_2153_ = l_Lean_NameSet_contains(v_activeScopes_2148_, v_namespaceName_2130_);
if (v___x_2153_ == 0)
{
lean_object* v_activeScopes_2154_; lean_object* v___x_2155_; 
lean_inc(v_newEntries_2135_);
lean_inc_ref(v_scopedEntries_2134_);
lean_dec_ref(v_s_2132_);
lean_inc(v_namespaceName_2130_);
v_activeScopes_2154_ = l_Lean_NameSet_insert(v_activeScopes_2148_, v_namespaceName_2130_);
v___x_2155_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2134_, v_namespaceName_2130_);
lean_dec(v_namespaceName_2130_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2157_; 
lean_dec_ref(v_ext_2131_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_activeScopes_2154_);
v___x_2157_ = v___x_2151_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_state_2147_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_activeScopes_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*2, v_delimitsLocal_2149_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v___y_2142_ = v___x_2157_;
goto v___jp_2141_;
}
}
else
{
lean_object* v_val_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v_val_2159_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2160_ = 1;
v___x_2161_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2131_, v_val_2159_, v_state_2147_);
lean_dec(v_val_2159_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_activeScopes_2154_);
lean_ctor_set(v___x_2151_, 0, v___x_2161_);
v___x_2163_ = v___x_2151_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_activeScopes_2154_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*2, v___x_2160_);
v___y_2142_ = v___x_2163_;
goto v___jp_2141_;
}
}
}
else
{
lean_del_object(v___x_2151_);
lean_dec(v_activeScopes_2148_);
lean_dec(v_state_2147_);
lean_del_object(v___x_2139_);
lean_dec(v_tail_2137_);
lean_dec_ref(v_ext_2131_);
lean_dec(v_namespaceName_2130_);
return v_s_2132_;
}
}
}
}
else
{
lean_dec(v_stateStack_2133_);
lean_dec_ref(v_ext_2131_);
lean_dec(v_namespaceName_2130_);
return v_s_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2167_, lean_object* v_env_2168_, lean_object* v_namespaceName_2169_){
_start:
{
lean_object* v_ext_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_ext_2170_ = lean_ctor_get(v_ext_2167_, 1);
lean_inc_ref(v_ext_2170_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2171_, 0, v_namespaceName_2169_);
lean_closure_set(v___f_2171_, 1, v_ext_2167_);
v___x_2172_ = lean_box(1);
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2170_, v_env_2168_, v___f_2171_, v___x_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_00_u03c3_2177_, lean_object* v_ext_2178_, lean_object* v_env_2179_, lean_object* v_namespaceName_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2178_, v_env_2179_, v_namespaceName_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2182_, lean_object* v_00_u03c3_2183_, lean_object* v_00_u03b1_2184_, lean_object* v_ext_2185_, lean_object* v_t_2186_, lean_object* v_init_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2185_, v_t_2186_, v_init_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2189_, lean_object* v_00_u03c3_2190_, lean_object* v_00_u03b1_2191_, lean_object* v_ext_2192_, lean_object* v_t_2193_, lean_object* v_init_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2189_, v_00_u03c3_2190_, v_00_u03b1_2191_, v_ext_2192_, v_t_2193_, v_init_2194_);
lean_dec_ref(v_t_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2196_, lean_object* v_00_u03c3_2197_, lean_object* v_init_2198_, lean_object* v_00_u03b1_2199_, lean_object* v_ext_2200_, lean_object* v_n_2201_, lean_object* v_b_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2198_, v_ext_2200_, v_n_2201_, v_b_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2204_, lean_object* v_00_u03c3_2205_, lean_object* v_init_2206_, lean_object* v_00_u03b1_2207_, lean_object* v_ext_2208_, lean_object* v_n_2209_, lean_object* v_b_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2204_, v_00_u03c3_2205_, v_init_2206_, v_00_u03b1_2207_, v_ext_2208_, v_n_2209_, v_b_2210_);
lean_dec_ref(v_n_2209_);
lean_dec(v_init_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2212_, lean_object* v_00_u03c3_2213_, lean_object* v_00_u03b1_2214_, lean_object* v_ext_2215_, lean_object* v_as_2216_, size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_b_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2215_, v_as_2216_, v_sz_2217_, v_i_2218_, v_b_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_00_u03c3_2222_, lean_object* v_00_u03b1_2223_, lean_object* v_ext_2224_, lean_object* v_as_2225_, lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_b_2228_){
_start:
{
size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; lean_object* v_res_2231_; 
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2221_, v_00_u03c3_2222_, v_00_u03b1_2223_, v_ext_2224_, v_as_2225_, v_sz_boxed_2229_, v_i_boxed_2230_, v_b_2228_);
lean_dec_ref(v_as_2225_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2232_, lean_object* v_00_u03c3_2233_, lean_object* v_init_2234_, lean_object* v_00_u03b1_2235_, lean_object* v_ext_2236_, lean_object* v_as_2237_, size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_b_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2234_, v_ext_2236_, v_as_2237_, v_sz_2238_, v_i_2239_, v_b_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_00_u03c3_2243_, lean_object* v_init_2244_, lean_object* v_00_u03b1_2245_, lean_object* v_ext_2246_, lean_object* v_as_2247_, lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_b_2250_){
_start:
{
size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2242_, v_00_u03c3_2243_, v_init_2244_, v_00_u03b1_2245_, v_ext_2246_, v_as_2247_, v_sz_boxed_2251_, v_i_boxed_2252_, v_b_2250_);
lean_dec_ref(v_as_2247_);
lean_dec(v_init_2244_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2254_, lean_object* v_00_u03c3_2255_, lean_object* v_00_u03b1_2256_, lean_object* v_ext_2257_, lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_b_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2257_, v_as_2258_, v_sz_2259_, v_i_2260_, v_b_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2263_, lean_object* v_00_u03c3_2264_, lean_object* v_00_u03b1_2265_, lean_object* v_ext_2266_, lean_object* v_as_2267_, lean_object* v_sz_2268_, lean_object* v_i_2269_, lean_object* v_b_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2268_);
lean_dec(v_sz_2268_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2263_, v_00_u03c3_2264_, v_00_u03b1_2265_, v_ext_2266_, v_as_2267_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2270_);
lean_dec_ref(v_as_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2274_, lean_object* v_00_u03c3_2275_, lean_object* v_00_u03b1_2276_, lean_object* v_ext_2277_, lean_object* v_as_2278_, size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2277_, v_as_2278_, v_sz_2279_, v_i_2280_, v_b_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2283_, lean_object* v_00_u03c3_2284_, lean_object* v_00_u03b1_2285_, lean_object* v_ext_2286_, lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_){
_start:
{
size_t v_sz_boxed_2291_; size_t v_i_boxed_2292_; lean_object* v_res_2293_; 
v_sz_boxed_2291_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2292_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2283_, v_00_u03c3_2284_, v_00_u03b1_2285_, v_ext_2286_, v_as_2287_, v_sz_boxed_2291_, v_i_boxed_2292_, v_b_2290_);
lean_dec_ref(v_as_2287_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2294_, lean_object* v_00_u03c3_2295_, lean_object* v_00_u03b1_2296_, lean_object* v_ext_2297_, lean_object* v_as_2298_, size_t v_sz_2299_, size_t v_i_2300_, lean_object* v_b_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2297_, v_as_2298_, v_sz_2299_, v_i_2300_, v_b_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2303_, lean_object* v_00_u03c3_2304_, lean_object* v_00_u03b1_2305_, lean_object* v_ext_2306_, lean_object* v_as_2307_, lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_b_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2303_, v_00_u03c3_2304_, v_00_u03b1_2305_, v_ext_2306_, v_as_2307_, v_sz_boxed_2311_, v_i_boxed_2312_, v_b_2310_);
lean_dec_ref(v_as_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2314_, lean_object* v_s_2315_){
_start:
{
lean_object* v_stateStack_2316_; 
v_stateStack_2316_ = lean_ctor_get(v_s_2315_, 0);
lean_inc(v_stateStack_2316_);
if (lean_obj_tag(v_stateStack_2316_) == 1)
{
lean_object* v_head_2317_; lean_object* v_scopedEntries_2318_; lean_object* v_newEntries_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2346_; 
v_head_2317_ = lean_ctor_get(v_stateStack_2316_, 0);
lean_inc(v_head_2317_);
v_scopedEntries_2318_ = lean_ctor_get(v_s_2315_, 1);
v_newEntries_2319_ = lean_ctor_get(v_s_2315_, 2);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_s_2315_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_s_2315_, 0);
lean_dec(v_unused_2347_);
v___x_2321_ = v_s_2315_;
v_isShared_2322_ = v_isSharedCheck_2346_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_newEntries_2319_);
lean_inc(v_scopedEntries_2318_);
lean_dec(v_s_2315_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2346_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_tail_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2344_; 
v_tail_2323_ = lean_ctor_get(v_stateStack_2316_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_stateStack_2316_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_stateStack_2316_, 0);
lean_dec(v_unused_2345_);
v___x_2325_ = v_stateStack_2316_;
v_isShared_2326_ = v_isSharedCheck_2344_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_tail_2323_);
lean_dec(v_stateStack_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2344_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_state_2327_; lean_object* v_activeScopes_2328_; uint8_t v_delimitsLocal_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2343_; 
v_state_2327_ = lean_ctor_get(v_head_2317_, 0);
v_activeScopes_2328_ = lean_ctor_get(v_head_2317_, 1);
v_delimitsLocal_2329_ = lean_ctor_get_uint8(v_head_2317_, sizeof(void*)*2);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_head_2317_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2331_ = v_head_2317_;
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_activeScopes_2328_);
lean_inc(v_state_2327_);
lean_dec(v_head_2317_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_apply_1(v_f_2314_, v_state_2327_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_activeScopes_2328_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, sizeof(void*)*2, v_delimitsLocal_2329_);
v___x_2335_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2335_);
v___x_2337_ = v___x_2325_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_tail_2323_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2337_);
v___x_2339_ = v___x_2321_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_scopedEntries_2318_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_newEntries_2319_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2316_);
lean_dec(v_f_2314_);
return v_s_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2348_, lean_object* v_env_2349_, lean_object* v_f_2350_){
_start:
{
lean_object* v_ext_2351_; lean_object* v_toEnvExtension_2352_; lean_object* v_asyncMode_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_ext_2351_ = lean_ctor_get(v_ext_2348_, 1);
lean_inc_ref(v_ext_2351_);
lean_dec_ref(v_ext_2348_);
v_toEnvExtension_2352_ = lean_ctor_get(v_ext_2351_, 0);
v_asyncMode_2353_ = lean_ctor_get(v_toEnvExtension_2352_, 2);
lean_inc(v_asyncMode_2353_);
v___f_2354_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2354_, 0, v_f_2350_);
v___x_2355_ = lean_box(0);
v___x_2356_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2351_, v_env_2349_, v___f_2354_, v_asyncMode_2353_, v___x_2355_);
lean_dec(v_asyncMode_2353_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2357_, lean_object* v_00_u03b2_2358_, lean_object* v_00_u03c3_2359_, lean_object* v_ext_2360_, lean_object* v_env_2361_, lean_object* v_f_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2360_, v_env_2361_, v_f_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2364_, lean_object* v_____s_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_apply_2(v_toPure_2364_, lean_box(0), v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2368_, lean_object* v_toPure_2369_, lean_object* v_r_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2368_);
v___x_2372_ = lean_apply_2(v_toPure_2369_, lean_box(0), v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2373_, lean_object* v_toBind_2374_, lean_object* v___f_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_modifyEnv_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_modifyEnv_2379_ = lean_ctor_get(v_inst_2373_, 1);
lean_inc(v_modifyEnv_2379_);
lean_dec_ref(v_inst_2373_);
v___x_2380_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2380_, 0, lean_box(0));
lean_closure_set(v___x_2380_, 1, lean_box(0));
lean_closure_set(v___x_2380_, 2, lean_box(0));
lean_closure_set(v___x_2380_, 3, v_a_2376_);
v___x_2381_ = lean_apply_1(v_modifyEnv_2379_, v___x_2380_);
v___x_2382_ = lean_apply_4(v_toBind_2374_, lean_box(0), lean_box(0), v___x_2381_, v___f_2375_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2383_, lean_object* v_inst_2384_, lean_object* v_toBind_2385_, lean_object* v_inst_2386_, lean_object* v___f_2387_, lean_object* v_____do__lift_2388_){
_start:
{
lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; size_t v_sz_2392_; size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2389_ = lean_box(0);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2390_, 0, v___x_2389_);
lean_closure_set(v___f_2390_, 1, v_toPure_2383_);
lean_inc(v_toBind_2385_);
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2391_, 0, v_inst_2384_);
lean_closure_set(v___f_2391_, 1, v_toBind_2385_);
lean_closure_set(v___f_2391_, 2, v___f_2390_);
v_sz_2392_ = lean_array_size(v_____do__lift_2388_);
v___x_2393_ = ((size_t)0ULL);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2386_, v_____do__lift_2388_, v___f_2391_, v_sz_2392_, v___x_2393_, v___x_2389_);
v___x_2395_ = lean_apply_4(v_toBind_2385_, lean_box(0), lean_box(0), v___x_2394_, v___f_2387_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = l_Lean_scopedEnvExtensionsRef;
v___x_2397_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2397_, 0, lean_box(0));
lean_closure_set(v___x_2397_, 1, lean_box(0));
lean_closure_set(v___x_2397_, 2, v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_){
_start:
{
lean_object* v_toApplicative_2401_; lean_object* v_toBind_2402_; lean_object* v_toPure_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; 
v_toApplicative_2401_ = lean_ctor_get(v_inst_2398_, 0);
v_toBind_2402_ = lean_ctor_get(v_inst_2398_, 1);
lean_inc_n(v_toBind_2402_, 2);
v_toPure_2403_ = lean_ctor_get(v_toApplicative_2401_, 1);
lean_inc_n(v_toPure_2403_, 2);
v___x_2404_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2405_ = lean_apply_2(v_inst_2400_, lean_box(0), v___x_2404_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2406_, 0, v_toPure_2403_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2407_, 0, v_toPure_2403_);
lean_closure_set(v___f_2407_, 1, v_inst_2399_);
lean_closure_set(v___f_2407_, 2, v_toBind_2402_);
lean_closure_set(v___f_2407_, 3, v_inst_2398_);
lean_closure_set(v___f_2407_, 4, v___f_2406_);
v___x_2408_ = lean_apply_4(v_toBind_2402_, lean_box(0), lean_box(0), v___x_2405_, v___f_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_pushScope___redArg(v_inst_2410_, v_inst_2411_, v_inst_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2414_, lean_object* v_toBind_2415_, lean_object* v___f_2416_, lean_object* v_a_2417_, lean_object* v_x_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_modifyEnv_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_modifyEnv_2420_ = lean_ctor_get(v_inst_2414_, 1);
lean_inc(v_modifyEnv_2420_);
lean_dec_ref(v_inst_2414_);
v___x_2421_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2421_, 0, lean_box(0));
lean_closure_set(v___x_2421_, 1, lean_box(0));
lean_closure_set(v___x_2421_, 2, lean_box(0));
lean_closure_set(v___x_2421_, 3, v_a_2417_);
v___x_2422_ = lean_apply_1(v_modifyEnv_2420_, v___x_2421_);
v___x_2423_ = lean_apply_4(v_toBind_2415_, lean_box(0), lean_box(0), v___x_2422_, v___f_2416_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2424_, lean_object* v_inst_2425_, lean_object* v_toBind_2426_, lean_object* v_inst_2427_, lean_object* v___f_2428_, lean_object* v_____do__lift_2429_){
_start:
{
lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; size_t v_sz_2433_; size_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2430_ = lean_box(0);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2431_, 0, v___x_2430_);
lean_closure_set(v___f_2431_, 1, v_toPure_2424_);
lean_inc(v_toBind_2426_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2432_, 0, v_inst_2425_);
lean_closure_set(v___f_2432_, 1, v_toBind_2426_);
lean_closure_set(v___f_2432_, 2, v___f_2431_);
v_sz_2433_ = lean_array_size(v_____do__lift_2429_);
v___x_2434_ = ((size_t)0ULL);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2427_, v_____do__lift_2429_, v___f_2432_, v_sz_2433_, v___x_2434_, v___x_2430_);
v___x_2436_ = lean_apply_4(v_toBind_2426_, lean_box(0), lean_box(0), v___x_2435_, v___f_2428_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_){
_start:
{
lean_object* v_toApplicative_2440_; lean_object* v_toBind_2441_; lean_object* v_toPure_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; 
v_toApplicative_2440_ = lean_ctor_get(v_inst_2437_, 0);
v_toBind_2441_ = lean_ctor_get(v_inst_2437_, 1);
lean_inc_n(v_toBind_2441_, 2);
v_toPure_2442_ = lean_ctor_get(v_toApplicative_2440_, 1);
lean_inc_n(v_toPure_2442_, 2);
v___x_2443_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2444_ = lean_apply_2(v_inst_2439_, lean_box(0), v___x_2443_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2445_, 0, v_toPure_2442_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2446_, 0, v_toPure_2442_);
lean_closure_set(v___f_2446_, 1, v_inst_2438_);
lean_closure_set(v___f_2446_, 2, v_toBind_2441_);
lean_closure_set(v___f_2446_, 3, v_inst_2437_);
lean_closure_set(v___f_2446_, 4, v___f_2445_);
v___x_2447_ = lean_apply_4(v_toBind_2441_, lean_box(0), lean_box(0), v___x_2444_, v___f_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_popScope___redArg(v_inst_2449_, v_inst_2450_, v_inst_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2453_, lean_object* v_depth_2454_, lean_object* v_x_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2453_, v_x_2455_, v_depth_2454_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2457_, lean_object* v_depth_2458_, lean_object* v_toBind_2459_, lean_object* v___f_2460_, lean_object* v_a_2461_, lean_object* v_x_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_modifyEnv_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_modifyEnv_2464_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc(v_modifyEnv_2464_);
lean_dec_ref(v_inst_2457_);
v___f_2465_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2465_, 0, v_a_2461_);
lean_closure_set(v___f_2465_, 1, v_depth_2458_);
v___x_2466_ = lean_apply_1(v_modifyEnv_2464_, v___f_2465_);
v___x_2467_ = lean_apply_4(v_toBind_2459_, lean_box(0), lean_box(0), v___x_2466_, v___f_2460_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2468_, lean_object* v_inst_2469_, lean_object* v_depth_2470_, lean_object* v_toBind_2471_, lean_object* v_inst_2472_, lean_object* v___f_2473_, lean_object* v_____do__lift_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; size_t v_sz_2478_; size_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2475_ = lean_box(0);
v___f_2476_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2476_, 0, v___x_2475_);
lean_closure_set(v___f_2476_, 1, v_toPure_2468_);
lean_inc(v_toBind_2471_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2477_, 0, v_inst_2469_);
lean_closure_set(v___f_2477_, 1, v_depth_2470_);
lean_closure_set(v___f_2477_, 2, v_toBind_2471_);
lean_closure_set(v___f_2477_, 3, v___f_2476_);
v_sz_2478_ = lean_array_size(v_____do__lift_2474_);
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2472_, v_____do__lift_2474_, v___f_2477_, v_sz_2478_, v___x_2479_, v___x_2475_);
v___x_2481_ = lean_apply_4(v_toBind_2471_, lean_box(0), lean_box(0), v___x_2480_, v___f_2473_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_depth_2485_){
_start:
{
lean_object* v_toApplicative_2486_; lean_object* v_toBind_2487_; lean_object* v_toPure_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v_toApplicative_2486_ = lean_ctor_get(v_inst_2482_, 0);
v_toBind_2487_ = lean_ctor_get(v_inst_2482_, 1);
lean_inc_n(v_toBind_2487_, 2);
v_toPure_2488_ = lean_ctor_get(v_toApplicative_2486_, 1);
lean_inc_n(v_toPure_2488_, 2);
v___x_2489_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2490_ = lean_apply_2(v_inst_2484_, lean_box(0), v___x_2489_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2491_, 0, v_toPure_2488_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2492_, 0, v_toPure_2488_);
lean_closure_set(v___f_2492_, 1, v_inst_2483_);
lean_closure_set(v___f_2492_, 2, v_depth_2485_);
lean_closure_set(v___f_2492_, 3, v_toBind_2487_);
lean_closure_set(v___f_2492_, 4, v_inst_2482_);
lean_closure_set(v___f_2492_, 5, v___f_2491_);
v___x_2493_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v___x_2490_, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_depth_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_setDelimitsLocal___redArg(v_inst_2495_, v_inst_2496_, v_inst_2497_, v_depth_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2500_, lean_object* v_namespaceName_2501_, lean_object* v_x_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2500_, v_x_2502_, v_namespaceName_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2504_, lean_object* v_namespaceName_2505_, lean_object* v_toBind_2506_, lean_object* v___f_2507_, lean_object* v_a_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_modifyEnv_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_modifyEnv_2511_ = lean_ctor_get(v_inst_2504_, 1);
lean_inc(v_modifyEnv_2511_);
lean_dec_ref(v_inst_2504_);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2512_, 0, v_a_2508_);
lean_closure_set(v___f_2512_, 1, v_namespaceName_2505_);
v___x_2513_ = lean_apply_1(v_modifyEnv_2511_, v___f_2512_);
v___x_2514_ = lean_apply_4(v_toBind_2506_, lean_box(0), lean_box(0), v___x_2513_, v___f_2507_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2515_, lean_object* v_inst_2516_, lean_object* v_namespaceName_2517_, lean_object* v_toBind_2518_, lean_object* v_inst_2519_, lean_object* v___f_2520_, lean_object* v_____do__lift_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; size_t v_sz_2525_; size_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2522_ = lean_box(0);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2523_, 0, v___x_2522_);
lean_closure_set(v___f_2523_, 1, v_toPure_2515_);
lean_inc(v_toBind_2518_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2524_, 0, v_inst_2516_);
lean_closure_set(v___f_2524_, 1, v_namespaceName_2517_);
lean_closure_set(v___f_2524_, 2, v_toBind_2518_);
lean_closure_set(v___f_2524_, 3, v___f_2523_);
v_sz_2525_ = lean_array_size(v_____do__lift_2521_);
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2519_, v_____do__lift_2521_, v___f_2524_, v_sz_2525_, v___x_2526_, v___x_2522_);
v___x_2528_ = lean_apply_4(v_toBind_2518_, lean_box(0), lean_box(0), v___x_2527_, v___f_2520_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_namespaceName_2532_){
_start:
{
lean_object* v_toApplicative_2533_; lean_object* v_toBind_2534_; lean_object* v_toPure_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; 
v_toApplicative_2533_ = lean_ctor_get(v_inst_2529_, 0);
v_toBind_2534_ = lean_ctor_get(v_inst_2529_, 1);
lean_inc_n(v_toBind_2534_, 2);
v_toPure_2535_ = lean_ctor_get(v_toApplicative_2533_, 1);
lean_inc_n(v_toPure_2535_, 2);
v___x_2536_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2537_ = lean_apply_2(v_inst_2531_, lean_box(0), v___x_2536_);
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2538_, 0, v_toPure_2535_);
v___f_2539_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2539_, 0, v_toPure_2535_);
lean_closure_set(v___f_2539_, 1, v_inst_2530_);
lean_closure_set(v___f_2539_, 2, v_namespaceName_2532_);
lean_closure_set(v___f_2539_, 3, v_toBind_2534_);
lean_closure_set(v___f_2539_, 4, v_inst_2529_);
lean_closure_set(v___f_2539_, 5, v___f_2538_);
v___x_2540_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2537_, v___f_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_namespaceName_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_activateScoped___redArg(v_inst_2542_, v_inst_2543_, v_inst_2544_, v_namespaceName_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2548_){
_start:
{
lean_inc(v___y_2548_);
return v___y_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2549_);
lean_dec(v___y_2549_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2551_, lean_object* v_a_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_a_2552_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2556_, lean_object* v_a_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2556_, v_a_2557_, v___y_2558_);
lean_dec_ref(v___y_2558_);
lean_dec(v_x_2556_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_initial_2561_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2569_){
_start:
{
lean_object* v_name_2571_; lean_object* v_addEntry_2572_; lean_object* v_initial_2573_; lean_object* v_finalizeImport_2574_; lean_object* v_exportEntry_x3f_2575_; lean_object* v___f_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_name_2571_ = lean_ctor_get(v_descr_2569_, 0);
lean_inc(v_name_2571_);
v_addEntry_2572_ = lean_ctor_get(v_descr_2569_, 1);
lean_inc(v_addEntry_2572_);
v_initial_2573_ = lean_ctor_get(v_descr_2569_, 2);
lean_inc(v_initial_2573_);
v_finalizeImport_2574_ = lean_ctor_get(v_descr_2569_, 3);
lean_inc(v_finalizeImport_2574_);
v_exportEntry_x3f_2575_ = lean_ctor_get(v_descr_2569_, 4);
lean_inc_ref(v_exportEntry_x3f_2575_);
lean_dec_ref(v_descr_2569_);
v___f_2576_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2577_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2578_, 0, v_initial_2573_);
v___x_2579_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2579_, 0, v_name_2571_);
lean_ctor_set(v___x_2579_, 1, v___f_2578_);
lean_ctor_set(v___x_2579_, 2, v___f_2577_);
lean_ctor_set(v___x_2579_, 3, v___f_2576_);
lean_ctor_set(v___x_2579_, 4, v_addEntry_2572_);
lean_ctor_set(v___x_2579_, 5, v_finalizeImport_2574_);
lean_ctor_set(v___x_2579_, 6, v_exportEntry_x3f_2575_);
v___x_2580_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03c3_2585_, lean_object* v_descr_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2589_, lean_object* v_00_u03c3_2590_, lean_object* v_descr_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2589_, v_00_u03c3_2590_, v_descr_2591_);
return v_res_2593_;
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
