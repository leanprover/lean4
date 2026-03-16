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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0();
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value;
static const lean_closure_object l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3 = (const lean_object*)&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_value;
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_array_object l_Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_scopedEnvExtensionsRef;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_12_);
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
lean_dec_ref(v_t_12_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object* v_a_64_){
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
v___x_69_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0);
v___x_70_ = lean_box(0);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_s_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0();
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_x_172_, v___y_173_, v___y_174_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec(v_x_172_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_inst_177_, lean_object* v_x_178_){
_start:
{
lean_inc(v_inst_177_);
return v_inst_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_inst_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_inst_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec(v_inst_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_s_182_, lean_object* v_x_183_){
_start:
{
lean_inc(v_s_182_);
return v_s_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_s_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_s_184_, v_x_185_);
lean_dec(v_x_185_);
lean_dec(v_s_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4(uint8_t v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___y_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4___boxed(lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
uint8_t v_x_156__boxed_192_; lean_object* v_res_193_; 
v_x_156__boxed_192_ = lean_unbox(v_x_190_);
v_res_193_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__4(v_x_156__boxed_192_, v___y_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___f_200_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_201_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_202_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_202_, 0, v_inst_199_);
v___f_203_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___f_204_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3));
v___x_205_ = lean_box(0);
v___x_206_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_207_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___f_200_);
lean_ctor_set(v___x_207_, 2, v___f_201_);
lean_ctor_set(v___x_207_, 3, v___f_202_);
lean_ctor_set(v___x_207_, 4, v___f_203_);
lean_ctor_set(v___x_207_, 5, v___x_206_);
lean_ctor_set(v___x_207_, 6, v___f_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_00_u03c3_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_213_){
_start:
{
lean_object* v_mkInitial_215_; lean_object* v___x_216_; 
v_mkInitial_215_ = lean_ctor_get(v_descr_213_, 1);
lean_inc_ref(v_mkInitial_215_);
lean_dec_ref(v_descr_213_);
v___x_216_ = lean_apply_1(v_mkInitial_215_, lean_box(0));
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_231_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_231_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_221_ = l_Lean_NameSet_empty;
v___x_222_ = 1;
v___x_223_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_223_, 0, v_a_217_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*2, v___x_222_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
lean_ctor_set(v___x_227_, 2, v___x_224_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_227_);
v___x_229_ = v___x_219_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_216_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_216_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_00_u03c3_245_, lean_object* v_descr_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_00_u03c3_251_, lean_object* v_descr_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_249_, v_00_u03b2_250_, v_00_u03c3_251_, v_descr_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_255_, lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v_key_258_; lean_object* v_value_259_; lean_object* v_tail_260_; uint8_t v___x_261_; 
v_key_258_ = lean_ctor_get(v_x_256_, 0);
v_value_259_ = lean_ctor_get(v_x_256_, 1);
v_tail_260_ = lean_ctor_get(v_x_256_, 2);
v___x_261_ = lean_name_eq(v_key_258_, v_a_255_);
if (v___x_261_ == 0)
{
v_x_256_ = v_tail_260_;
goto _start;
}
else
{
lean_object* v___x_263_; 
lean_inc(v_value_259_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_value_259_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec(v_a_264_);
return v_res_266_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_267_; uint64_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1723u);
v___x_268_ = lean_uint64_of_nat(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_buckets_271_; lean_object* v___x_272_; uint64_t v___y_274_; 
v_buckets_271_ = lean_ctor_get(v_m_269_, 1);
v___x_272_ = lean_array_get_size(v_buckets_271_);
if (lean_obj_tag(v_a_270_) == 0)
{
uint64_t v___x_288_; 
v___x_288_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_274_ = v___x_288_;
goto v___jp_273_;
}
else
{
uint64_t v_hash_289_; 
v_hash_289_ = lean_ctor_get_uint64(v_a_270_, sizeof(void*)*2);
v___y_274_ = v_hash_289_;
goto v___jp_273_;
}
v___jp_273_:
{
uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v_fold_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_275_ = 32ULL;
v___x_276_ = lean_uint64_shift_right(v___y_274_, v___x_275_);
v_fold_277_ = lean_uint64_xor(v___y_274_, v___x_276_);
v___x_278_ = 16ULL;
v___x_279_ = lean_uint64_shift_right(v_fold_277_, v___x_278_);
v___x_280_ = lean_uint64_xor(v_fold_277_, v___x_279_);
v___x_281_ = lean_uint64_to_usize(v___x_280_);
v___x_282_ = lean_usize_of_nat(v___x_272_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_land(v___x_281_, v___x_284_);
v___x_286_ = lean_array_uget_borrowed(v_buckets_271_, v___x_285_);
v___x_287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_270_, v___x_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_m_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_293_, lean_object* v_vals_294_, lean_object* v_i_295_, lean_object* v_k_296_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_keys_293_);
v___x_298_ = lean_nat_dec_lt(v_i_295_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_i_295_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
else
{
lean_object* v_k_x27_300_; uint8_t v___x_301_; 
v_k_x27_300_ = lean_array_fget_borrowed(v_keys_293_, v_i_295_);
v___x_301_ = lean_name_eq(v_k_296_, v_k_x27_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_i_295_, v___x_302_);
lean_dec(v_i_295_);
v_i_295_ = v___x_303_;
goto _start;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_array_fget_borrowed(v_vals_294_, v_i_295_);
lean_dec(v_i_295_);
lean_inc(v___x_305_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_307_, lean_object* v_vals_308_, lean_object* v_i_309_, lean_object* v_k_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_307_, v_vals_308_, v_i_309_, v_k_310_);
lean_dec(v_k_310_);
lean_dec_ref(v_vals_308_);
lean_dec_ref(v_keys_307_);
return v_res_311_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; 
v___x_312_ = ((size_t)5ULL);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_shift_left(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_317_ = lean_usize_sub(v___x_316_, v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_318_, size_t v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v_es_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_342_; 
v_es_321_ = lean_ctor_get(v_x_318_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_342_ == 0)
{
v___x_323_ = v_x_318_;
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_es_321_);
lean_dec(v_x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v_j_329_; lean_object* v___x_330_; 
v___x_325_ = lean_box(2);
v___x_326_ = ((size_t)5ULL);
v___x_327_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_328_ = lean_usize_land(v_x_319_, v___x_327_);
v_j_329_ = lean_usize_to_nat(v___x_328_);
v___x_330_ = lean_array_get(v___x_325_, v_es_321_, v_j_329_);
lean_dec(v_j_329_);
lean_dec_ref(v_es_321_);
switch(lean_obj_tag(v___x_330_))
{
case 0:
{
lean_object* v_key_331_; lean_object* v_val_332_; uint8_t v___x_333_; 
v_key_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_key_331_);
v_val_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_val_332_);
lean_dec_ref(v___x_330_);
v___x_333_ = lean_name_eq(v_x_320_, v_key_331_);
lean_dec(v_key_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_val_332_);
lean_del_object(v___x_323_);
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v___x_336_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 1);
lean_ctor_set(v___x_323_, 0, v_val_332_);
v___x_336_ = v___x_323_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_val_332_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
case 1:
{
lean_object* v_node_338_; size_t v___x_339_; 
lean_del_object(v___x_323_);
v_node_338_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_node_338_);
lean_dec_ref(v___x_330_);
v___x_339_ = lean_usize_shift_right(v_x_319_, v___x_326_);
v_x_318_ = v_node_338_;
v_x_319_ = v___x_339_;
goto _start;
}
default: 
{
lean_object* v___x_341_; 
lean_del_object(v___x_323_);
v___x_341_ = lean_box(0);
return v___x_341_;
}
}
}
}
else
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_ks_343_ = lean_ctor_get(v_x_318_, 0);
lean_inc_ref(v_ks_343_);
v_vs_344_ = lean_ctor_get(v_x_318_, 1);
lean_inc_ref(v_vs_344_);
lean_dec_ref(v_x_318_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_343_, v_vs_344_, v___x_345_, v_x_320_);
lean_dec_ref(v_vs_344_);
lean_dec_ref(v_ks_343_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_1076__boxed_350_; lean_object* v_res_351_; 
v_x_1076__boxed_350_ = lean_unbox_usize(v_x_348_);
lean_dec(v_x_348_);
v_res_351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_347_, v_x_1076__boxed_350_, v_x_349_);
lean_dec(v_x_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
uint64_t v___y_355_; 
if (lean_obj_tag(v_x_353_) == 0)
{
uint64_t v___x_358_; 
v___x_358_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_355_ = v___x_358_;
goto v___jp_354_;
}
else
{
uint64_t v_hash_359_; 
v_hash_359_ = lean_ctor_get_uint64(v_x_353_, sizeof(void*)*2);
v___y_355_ = v_hash_359_;
goto v___jp_354_;
}
v___jp_354_:
{
size_t v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_uint64_to_usize(v___y_355_);
v___x_357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_352_, v___x_356_, v_x_353_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_360_, v_x_361_);
lean_dec(v_x_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_stage_u2081_365_; 
v_stage_u2081_365_ = lean_ctor_get_uint8(v_x_363_, sizeof(void*)*2);
if (v_stage_u2081_365_ == 0)
{
lean_object* v_map_u2081_366_; lean_object* v_map_u2082_367_; lean_object* v___x_368_; 
v_map_u2081_366_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_map_u2081_366_);
v_map_u2082_367_ = lean_ctor_get(v_x_363_, 1);
lean_inc_ref(v_map_u2082_367_);
lean_dec_ref(v_x_363_);
v___x_368_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_367_, v_x_364_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_366_, v_x_364_);
lean_dec_ref(v_map_u2081_366_);
return v___x_369_;
}
else
{
lean_dec_ref(v_map_u2081_366_);
return v___x_368_;
}
}
else
{
lean_object* v_map_u2081_370_; lean_object* v___x_371_; 
v_map_u2081_370_ = lean_ctor_get(v_x_363_, 0);
lean_inc_ref(v_map_u2081_370_);
lean_dec_ref(v_x_363_);
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_370_, v_x_364_);
lean_dec_ref(v_map_u2081_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_372_, v_x_373_);
lean_dec(v_x_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_375_, lean_object* v_b_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_dec(v_b_376_);
lean_dec(v_a_375_);
return v_x_377_;
}
else
{
lean_object* v_key_378_; lean_object* v_value_379_; lean_object* v_tail_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
v_key_378_ = lean_ctor_get(v_x_377_, 0);
v_value_379_ = lean_ctor_get(v_x_377_, 1);
v_tail_380_ = lean_ctor_get(v_x_377_, 2);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_392_ == 0)
{
v___x_382_ = v_x_377_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_tail_380_);
lean_inc(v_value_379_);
lean_inc(v_key_378_);
lean_dec(v_x_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_name_eq(v_key_378_, v_a_375_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_375_, v_b_376_, v_tail_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_key_378_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_value_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v___x_390_; 
lean_dec(v_value_379_);
lean_dec(v_key_378_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v_b_376_);
lean_ctor_set(v___x_382_, 0, v_a_375_);
v___x_390_ = v___x_382_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_375_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_b_376_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_tail_380_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
return v_x_393_;
}
else
{
lean_object* v_key_395_; lean_object* v_value_396_; lean_object* v_tail_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_423_; 
v_key_395_ = lean_ctor_get(v_x_394_, 0);
v_value_396_ = lean_ctor_get(v_x_394_, 1);
v_tail_397_ = lean_ctor_get(v_x_394_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_423_ == 0)
{
v___x_399_ = v_x_394_;
v_isShared_400_ = v_isSharedCheck_423_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_tail_397_);
lean_inc(v_value_396_);
lean_inc(v_key_395_);
lean_dec(v_x_394_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_423_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; uint64_t v___y_403_; 
v___x_401_ = lean_array_get_size(v_x_393_);
if (lean_obj_tag(v_key_395_) == 0)
{
uint64_t v___x_421_; 
v___x_421_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_403_ = v___x_421_;
goto v___jp_402_;
}
else
{
uint64_t v_hash_422_; 
v_hash_422_ = lean_ctor_get_uint64(v_key_395_, sizeof(void*)*2);
v___y_403_ = v_hash_422_;
goto v___jp_402_;
}
v___jp_402_:
{
uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v_fold_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_404_ = 32ULL;
v___x_405_ = lean_uint64_shift_right(v___y_403_, v___x_404_);
v_fold_406_ = lean_uint64_xor(v___y_403_, v___x_405_);
v___x_407_ = 16ULL;
v___x_408_ = lean_uint64_shift_right(v_fold_406_, v___x_407_);
v___x_409_ = lean_uint64_xor(v_fold_406_, v___x_408_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = lean_usize_of_nat(v___x_401_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v___x_411_, v___x_412_);
v___x_414_ = lean_usize_land(v___x_410_, v___x_413_);
v___x_415_ = lean_array_uget_borrowed(v_x_393_, v___x_414_);
lean_inc(v___x_415_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 2, v___x_415_);
v___x_417_ = v___x_399_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_key_395_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_value_396_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_415_);
v___x_417_ = v_reuseFailAlloc_420_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; 
v___x_418_ = lean_array_uset(v_x_393_, v___x_414_, v___x_417_);
v_x_393_ = v___x_418_;
v_x_394_ = v_tail_397_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_424_, lean_object* v_source_425_, lean_object* v_target_426_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_array_get_size(v_source_425_);
v___x_428_ = lean_nat_dec_lt(v_i_424_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_source_425_);
lean_dec(v_i_424_);
return v_target_426_;
}
else
{
lean_object* v_es_429_; lean_object* v___x_430_; lean_object* v_source_431_; lean_object* v_target_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_es_429_ = lean_array_fget(v_source_425_, v_i_424_);
v___x_430_ = lean_box(0);
v_source_431_ = lean_array_fset(v_source_425_, v_i_424_, v___x_430_);
v_target_432_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_426_, v_es_429_);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_i_424_, v___x_433_);
lean_dec(v_i_424_);
v_i_424_ = v___x_434_;
v_source_425_ = v_source_431_;
v_target_426_ = v_target_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_nbuckets_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_437_ = lean_array_get_size(v_data_436_);
v___x_438_ = lean_unsigned_to_nat(2u);
v_nbuckets_439_ = lean_nat_mul(v___x_437_, v___x_438_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_box(0);
v___x_442_ = lean_mk_array(v_nbuckets_439_, v___x_441_);
v___x_443_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_440_, v_data_436_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
uint8_t v___x_446_; 
v___x_446_ = 0;
return v___x_446_;
}
else
{
lean_object* v_key_447_; lean_object* v_tail_448_; uint8_t v___x_449_; 
v_key_447_ = lean_ctor_get(v_x_445_, 0);
v_tail_448_ = lean_ctor_get(v_x_445_, 2);
v___x_449_ = lean_name_eq(v_key_447_, v_a_444_);
if (v___x_449_ == 0)
{
v_x_445_ = v_tail_448_;
goto _start;
}
else
{
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec(v_a_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_size_458_; lean_object* v_buckets_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_505_; 
v_size_458_ = lean_ctor_get(v_m_455_, 0);
v_buckets_459_ = lean_ctor_get(v_m_455_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_m_455_);
if (v_isSharedCheck_505_ == 0)
{
v___x_461_ = v_m_455_;
v_isShared_462_ = v_isSharedCheck_505_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_buckets_459_);
lean_inc(v_size_458_);
lean_dec(v_m_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_505_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; uint64_t v___y_465_; 
v___x_463_ = lean_array_get_size(v_buckets_459_);
if (lean_obj_tag(v_a_456_) == 0)
{
uint64_t v___x_503_; 
v___x_503_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_465_ = v___x_503_;
goto v___jp_464_;
}
else
{
uint64_t v_hash_504_; 
v_hash_504_ = lean_ctor_get_uint64(v_a_456_, sizeof(void*)*2);
v___y_465_ = v_hash_504_;
goto v___jp_464_;
}
v___jp_464_:
{
uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v_fold_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v_bkt_477_; uint8_t v___x_478_; 
v___x_466_ = 32ULL;
v___x_467_ = lean_uint64_shift_right(v___y_465_, v___x_466_);
v_fold_468_ = lean_uint64_xor(v___y_465_, v___x_467_);
v___x_469_ = 16ULL;
v___x_470_ = lean_uint64_shift_right(v_fold_468_, v___x_469_);
v___x_471_ = lean_uint64_xor(v_fold_468_, v___x_470_);
v___x_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = lean_usize_of_nat(v___x_463_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_sub(v___x_473_, v___x_474_);
v___x_476_ = lean_usize_land(v___x_472_, v___x_475_);
v_bkt_477_ = lean_array_uget_borrowed(v_buckets_459_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_456_, v_bkt_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_size_x27_480_; lean_object* v___x_481_; lean_object* v_buckets_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v_size_x27_480_ = lean_nat_add(v_size_458_, v___x_479_);
lean_dec(v_size_458_);
lean_inc(v_bkt_477_);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v_a_456_);
lean_ctor_set(v___x_481_, 1, v_b_457_);
lean_ctor_set(v___x_481_, 2, v_bkt_477_);
v_buckets_x27_482_ = lean_array_uset(v_buckets_459_, v___x_476_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(4u);
v___x_484_ = lean_nat_mul(v_size_x27_480_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = lean_nat_div(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_array_get_size(v_buckets_x27_482_);
v___x_488_ = lean_nat_dec_le(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v_val_489_; lean_object* v___x_491_; 
v_val_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_482_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_val_489_);
lean_ctor_set(v___x_461_, 0, v_size_x27_480_);
v___x_491_ = v___x_461_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_val_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v___x_494_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_buckets_x27_482_);
lean_ctor_set(v___x_461_, 0, v_size_x27_480_);
v___x_494_ = v___x_461_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_buckets_x27_482_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v___x_496_; lean_object* v_buckets_x27_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
lean_inc(v_bkt_477_);
v___x_496_ = lean_box(0);
v_buckets_x27_497_ = lean_array_uset(v_buckets_459_, v___x_476_, v___x_496_);
v___x_498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_456_, v_b_457_, v_bkt_477_);
v___x_499_ = lean_array_uset(v_buckets_x27_497_, v___x_476_, v___x_498_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_499_);
v___x_501_ = v___x_461_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_size_458_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_ks_510_; lean_object* v_vs_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_535_; 
v_ks_510_ = lean_ctor_get(v_x_506_, 0);
v_vs_511_ = lean_ctor_get(v_x_506_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_535_ == 0)
{
v___x_513_ = v_x_506_;
v_isShared_514_ = v_isSharedCheck_535_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_vs_511_);
lean_inc(v_ks_510_);
lean_dec(v_x_506_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_535_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_ks_510_);
v___x_516_ = lean_nat_dec_lt(v_x_507_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec(v_x_507_);
v___x_517_ = lean_array_push(v_ks_510_, v_x_508_);
v___x_518_ = lean_array_push(v_vs_511_, v_x_509_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_518_);
lean_ctor_set(v___x_513_, 0, v___x_517_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v_k_x27_522_; uint8_t v___x_523_; 
v_k_x27_522_ = lean_array_fget_borrowed(v_ks_510_, v_x_507_);
v___x_523_ = lean_name_eq(v_x_508_, v_k_x27_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_525_; 
if (v_isShared_514_ == 0)
{
v___x_525_ = v___x_513_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_ks_510_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_vs_511_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_x_507_, v___x_526_);
lean_dec(v_x_507_);
v_x_506_ = v___x_525_;
v_x_507_ = v___x_527_;
goto _start;
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = lean_array_fset(v_ks_510_, v_x_507_, v_x_508_);
v___x_531_ = lean_array_fset(v_vs_511_, v_x_507_, v_x_509_);
lean_dec(v_x_507_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_531_);
lean_ctor_set(v___x_513_, 0, v___x_530_);
v___x_533_ = v___x_513_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_536_, lean_object* v_k_537_, lean_object* v_v_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_536_, v___x_539_, v_k_537_, v_v_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_542_, size_t v_x_543_, size_t v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
lean_object* v_es_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v_j_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_es_547_ = lean_ctor_get(v_x_542_, 0);
v___x_548_ = ((size_t)5ULL);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_551_ = lean_usize_land(v_x_543_, v___x_550_);
v_j_552_ = lean_usize_to_nat(v___x_551_);
v___x_553_ = lean_array_get_size(v_es_547_);
v___x_554_ = lean_nat_dec_lt(v_j_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec(v_j_552_);
lean_dec(v_x_546_);
lean_dec(v_x_545_);
return v_x_542_;
}
else
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_591_; 
lean_inc_ref(v_es_547_);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_x_542_, 0);
lean_dec(v_unused_592_);
v___x_556_ = v_x_542_;
v_isShared_557_ = v_isSharedCheck_591_;
goto v_resetjp_555_;
}
else
{
lean_dec(v_x_542_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_591_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_v_558_; lean_object* v___x_559_; lean_object* v_xs_x27_560_; lean_object* v___y_562_; 
v_v_558_ = lean_array_fget(v_es_547_, v_j_552_);
v___x_559_ = lean_box(0);
v_xs_x27_560_ = lean_array_fset(v_es_547_, v_j_552_, v___x_559_);
switch(lean_obj_tag(v_v_558_))
{
case 0:
{
lean_object* v_key_567_; lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_578_; 
v_key_567_ = lean_ctor_get(v_v_558_, 0);
v_val_568_ = lean_ctor_get(v_v_558_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_v_558_);
if (v_isSharedCheck_578_ == 0)
{
v___x_570_ = v_v_558_;
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_inc(v_key_567_);
lean_dec(v_v_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_name_eq(v_x_545_, v_key_567_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_del_object(v___x_570_);
v___x_573_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_567_, v_val_568_, v_x_545_, v_x_546_);
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___y_562_ = v___x_574_;
goto v___jp_561_;
}
else
{
lean_object* v___x_576_; 
lean_dec(v_val_568_);
lean_dec(v_key_567_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_x_546_);
lean_ctor_set(v___x_570_, 0, v_x_545_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_x_545_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_x_546_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v___y_562_ = v___x_576_;
goto v___jp_561_;
}
}
}
}
case 1:
{
lean_object* v_node_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v_node_579_ = lean_ctor_get(v_v_558_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_v_558_);
if (v_isSharedCheck_589_ == 0)
{
v___x_581_ = v_v_558_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_node_579_);
lean_dec(v_v_558_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_583_ = lean_usize_shift_right(v_x_543_, v___x_548_);
v___x_584_ = lean_usize_add(v_x_544_, v___x_549_);
v___x_585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_579_, v___x_583_, v___x_584_, v_x_545_, v_x_546_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_585_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v___y_562_ = v___x_587_;
goto v___jp_561_;
}
}
}
default: 
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_x_545_);
lean_ctor_set(v___x_590_, 1, v_x_546_);
v___y_562_ = v___x_590_;
goto v___jp_561_;
}
}
v___jp_561_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_array_fset(v_xs_x27_560_, v_j_552_, v___y_562_);
lean_dec(v_j_552_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_563_);
v___x_565_ = v___x_556_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
else
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_614_; 
v_ks_593_ = lean_ctor_get(v_x_542_, 0);
v_vs_594_ = lean_ctor_get(v_x_542_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_614_ == 0)
{
v___x_596_ = v_x_542_;
v_isShared_597_ = v_isSharedCheck_614_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_vs_594_);
lean_inc(v_ks_593_);
lean_dec(v_x_542_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_614_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_ks_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_vs_594_);
v___x_599_ = v_reuseFailAlloc_613_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v_newNode_600_; uint8_t v___y_602_; size_t v___x_608_; uint8_t v___x_609_; 
v_newNode_600_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_599_, v_x_545_, v_x_546_);
v___x_608_ = ((size_t)7ULL);
v___x_609_ = lean_usize_dec_le(v___x_608_, v_x_544_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_600_);
v___x_611_ = lean_unsigned_to_nat(4u);
v___x_612_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
v___y_602_ = v___x_612_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___x_609_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v_ks_603_; lean_object* v_vs_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_ks_603_ = lean_ctor_get(v_newNode_600_, 0);
lean_inc_ref(v_ks_603_);
v_vs_604_ = lean_ctor_get(v_newNode_600_, 1);
lean_inc_ref(v_vs_604_);
lean_dec_ref(v_newNode_600_);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_607_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_544_, v_ks_603_, v_vs_604_, v___x_605_, v___x_606_);
lean_dec_ref(v_vs_604_);
lean_dec_ref(v_ks_603_);
return v___x_607_;
}
else
{
return v_newNode_600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_615_, lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_i_618_, lean_object* v_entries_619_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_array_get_size(v_keys_616_);
v___x_621_ = lean_nat_dec_lt(v_i_618_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v_i_618_);
return v_entries_619_;
}
else
{
lean_object* v_k_622_; lean_object* v_v_623_; uint64_t v___y_625_; 
v_k_622_ = lean_array_fget_borrowed(v_keys_616_, v_i_618_);
v_v_623_ = lean_array_fget_borrowed(v_vals_617_, v_i_618_);
if (lean_obj_tag(v_k_622_) == 0)
{
uint64_t v___x_636_; 
v___x_636_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_625_ = v___x_636_;
goto v___jp_624_;
}
else
{
uint64_t v_hash_637_; 
v_hash_637_ = lean_ctor_get_uint64(v_k_622_, sizeof(void*)*2);
v___y_625_ = v_hash_637_;
goto v___jp_624_;
}
v___jp_624_:
{
size_t v_h_626_; size_t v___x_627_; lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v_h_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_h_626_ = lean_uint64_to_usize(v___y_625_);
v___x_627_ = ((size_t)5ULL);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_sub(v_depth_615_, v___x_629_);
v___x_631_ = lean_usize_mul(v___x_627_, v___x_630_);
v_h_632_ = lean_usize_shift_right(v_h_626_, v___x_631_);
v___x_633_ = lean_nat_add(v_i_618_, v___x_628_);
lean_dec(v_i_618_);
lean_inc(v_v_623_);
lean_inc(v_k_622_);
v___x_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_619_, v_h_632_, v_depth_615_, v_k_622_, v_v_623_);
v_i_618_ = v___x_633_;
v_entries_619_ = v___x_634_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_638_, lean_object* v_keys_639_, lean_object* v_vals_640_, lean_object* v_i_641_, lean_object* v_entries_642_){
_start:
{
size_t v_depth_boxed_643_; lean_object* v_res_644_; 
v_depth_boxed_643_ = lean_unbox_usize(v_depth_638_);
lean_dec(v_depth_638_);
v_res_644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_643_, v_keys_639_, v_vals_640_, v_i_641_, v_entries_642_);
lean_dec_ref(v_vals_640_);
lean_dec_ref(v_keys_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
size_t v_x_1486__boxed_650_; size_t v_x_1487__boxed_651_; lean_object* v_res_652_; 
v_x_1486__boxed_650_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_x_1487__boxed_651_ = lean_unbox_usize(v_x_647_);
lean_dec(v_x_647_);
v_res_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_645_, v_x_1486__boxed_650_, v_x_1487__boxed_651_, v_x_648_, v_x_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
uint64_t v___y_657_; 
if (lean_obj_tag(v_x_654_) == 0)
{
uint64_t v___x_661_; 
v___x_661_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_657_ = v___x_661_;
goto v___jp_656_;
}
else
{
uint64_t v_hash_662_; 
v_hash_662_ = lean_ctor_get_uint64(v_x_654_, sizeof(void*)*2);
v___y_657_ = v_hash_662_;
goto v___jp_656_;
}
v___jp_656_:
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_uint64_to_usize(v___y_657_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_653_, v___x_658_, v___x_659_, v_x_654_, v_x_655_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint8_t v_stage_u2081_666_; 
v_stage_u2081_666_ = lean_ctor_get_uint8(v_x_663_, sizeof(void*)*2);
if (v_stage_u2081_666_ == 0)
{
lean_object* v_map_u2081_667_; lean_object* v_map_u2082_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_map_u2081_667_ = lean_ctor_get(v_x_663_, 0);
v_map_u2082_668_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_676_ == 0)
{
v___x_670_ = v_x_663_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_map_u2082_668_);
lean_inc(v_map_u2081_667_);
lean_dec(v_x_663_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_668_, v_x_664_, v_x_665_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_map_u2081_667_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*2, v_stage_u2081_666_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_map_u2081_677_; lean_object* v_map_u2082_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_map_u2081_677_ = lean_ctor_get(v_x_663_, 0);
v_map_u2082_678_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_x_663_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_map_u2082_678_);
lean_inc(v_map_u2081_677_);
lean_dec(v_x_663_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_677_, v_x_664_, v_x_665_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_map_u2082_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*2, v_stage_u2081_666_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_unsigned_to_nat(32u);
v___x_688_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = ((size_t)5ULL);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_unsigned_to_nat(32u);
v___x_693_ = lean_mk_empty_array_with_capacity(v___x_692_);
v___x_694_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_691_);
lean_ctor_set(v___x_695_, 3, v___x_691_);
lean_ctor_set_usize(v___x_695_, 4, v___x_690_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_696_, lean_object* v_ns_697_, lean_object* v_b_698_){
_start:
{
lean_object* v___x_699_; 
lean_inc_ref(v_scopedEntries_696_);
v___x_699_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_696_, v_ns_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_701_ = l_Lean_PersistentArray_push___redArg(v___x_700_, v_b_698_);
v___x_702_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_696_, v_ns_697_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_val_703_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v___x_699_);
v___x_704_ = l_Lean_PersistentArray_push___redArg(v_val_703_, v_b_698_);
v___x_705_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_696_, v_ns_697_, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_706_, lean_object* v_scopedEntries_707_, lean_object* v_ns_708_, lean_object* v_b_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_707_, v_ns_708_, v_b_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_715_, v_x_716_, v_x_717_);
lean_dec(v_x_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_720_, v_x_721_, v_x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_728_, v_x_729_, v_x_730_);
lean_dec(v_x_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_733_, v_a_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_736_, v_m_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_m_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_741_, v_x_742_, v_x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_746_, v_a_747_, v_b_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, size_t v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_751_, v_x_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
size_t v_x_1794__boxed_759_; lean_object* v_res_760_; 
v_x_1794__boxed_759_ = lean_unbox_usize(v_x_757_);
lean_dec(v_x_757_);
v_res_760_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_755_, v_x_756_, v_x_1794__boxed_759_, v_x_758_);
lean_dec(v_x_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_761_, lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_765_, v_a_766_, v_x_767_);
lean_dec(v_x_767_);
lean_dec(v_a_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, size_t v_x_771_, size_t v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_770_, v_x_771_, v_x_772_, v_x_773_, v_x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
size_t v_x_1810__boxed_782_; size_t v_x_1811__boxed_783_; lean_object* v_res_784_; 
v_x_1810__boxed_782_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_x_1811__boxed_783_ = lean_unbox_usize(v_x_779_);
lean_dec(v_x_779_);
v_res_784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_776_, v_x_777_, v_x_1810__boxed_782_, v_x_1811__boxed_783_, v_x_780_, v_x_781_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_785_, lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_786_, v_x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_789_, lean_object* v_a_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_789_, v_a_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec(v_a_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_794_, lean_object* v_data_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_797_, lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_798_, v_b_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_802_, lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_heq_805_, lean_object* v_i_806_, lean_object* v_k_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_803_, v_vals_804_, v_i_806_, v_k_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_809_, lean_object* v_keys_810_, lean_object* v_vals_811_, lean_object* v_heq_812_, lean_object* v_i_813_, lean_object* v_k_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_809_, v_keys_810_, v_vals_811_, v_heq_812_, v_i_813_, v_k_814_);
lean_dec(v_k_814_);
lean_dec_ref(v_vals_811_);
lean_dec_ref(v_keys_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_816_, lean_object* v_n_817_, lean_object* v_k_818_, lean_object* v_v_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_817_, v_k_818_, v_v_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_821_, size_t v_depth_822_, lean_object* v_keys_823_, lean_object* v_vals_824_, lean_object* v_heq_825_, lean_object* v_i_826_, lean_object* v_entries_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_822_, v_keys_823_, v_vals_824_, v_i_826_, v_entries_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_829_, lean_object* v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_heq_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
size_t v_depth_boxed_836_; lean_object* v_res_837_; 
v_depth_boxed_836_ = lean_unbox_usize(v_depth_830_);
lean_dec(v_depth_830_);
v_res_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_829_, v_depth_boxed_836_, v_keys_831_, v_vals_832_, v_heq_833_, v_i_834_, v_entries_835_);
lean_dec_ref(v_vals_832_);
lean_dec_ref(v_keys_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_838_, lean_object* v_i_839_, lean_object* v_source_840_, lean_object* v_target_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_839_, v_source_840_, v_target_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_844_, v_x_845_, v_x_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_853_, lean_object* v_as_854_, size_t v_sz_855_, size_t v_i_856_, lean_object* v_b_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_a_861_; uint8_t v___x_865_; 
v___x_865_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
lean_dec_ref(v___y_858_);
lean_dec_ref(v_descr_853_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v_b_857_);
return v___x_866_;
}
else
{
lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_907_; 
v_fst_867_ = lean_ctor_get(v_b_857_, 0);
v_snd_868_ = lean_ctor_get(v_b_857_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_b_857_);
if (v_isSharedCheck_907_ == 0)
{
v___x_870_ = v_b_857_;
v_isShared_871_ = v_isSharedCheck_907_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_snd_868_);
lean_inc(v_fst_867_);
lean_dec(v_b_857_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_907_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_a_872_; 
v_a_872_ = lean_array_uget_borrowed(v_as_854_, v_i_856_);
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v_a_873_; lean_object* v_ofOLeanEntry_874_; lean_object* v_addEntry_875_; lean_object* v___x_876_; 
v_a_873_ = lean_ctor_get(v_a_872_, 0);
v_ofOLeanEntry_874_ = lean_ctor_get(v_descr_853_, 2);
v_addEntry_875_ = lean_ctor_get(v_descr_853_, 4);
lean_inc_ref(v_ofOLeanEntry_874_);
lean_inc_ref(v___y_858_);
lean_inc(v_a_873_);
lean_inc(v_fst_867_);
v___x_876_ = lean_apply_4(v_ofOLeanEntry_874_, v_fst_867_, v_a_873_, v___y_858_, lean_box(0));
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_876_);
lean_inc(v_addEntry_875_);
v___x_878_ = lean_apply_2(v_addEntry_875_, v_fst_867_, v_a_877_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_878_);
v___x_880_ = v___x_870_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_868_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
v_a_861_ = v___x_880_;
goto v___jp_860_;
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_870_);
lean_dec(v_snd_868_);
lean_dec(v_fst_867_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_descr_853_);
v_a_882_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_876_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_876_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v_a_891_; lean_object* v_ofOLeanEntry_892_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v_a_872_, 0);
v_a_891_ = lean_ctor_get(v_a_872_, 1);
v_ofOLeanEntry_892_ = lean_ctor_get(v_descr_853_, 2);
lean_inc_ref(v_ofOLeanEntry_892_);
lean_inc_ref(v___y_858_);
lean_inc(v_a_891_);
lean_inc(v_fst_867_);
v___x_893_ = lean_apply_4(v_ofOLeanEntry_892_, v_fst_867_, v_a_891_, v___y_858_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
lean_inc(v_a_890_);
v___x_895_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_868_, v_a_890_, v_a_894_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_895_);
v___x_897_ = v___x_870_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
v_a_861_ = v___x_897_;
goto v___jp_860_;
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_870_);
lean_dec(v_snd_868_);
lean_dec(v_fst_867_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_descr_853_);
v_a_899_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_893_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_893_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
v___jp_860_:
{
size_t v___x_862_; size_t v___x_863_; 
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_856_, v___x_862_);
v_i_856_ = v___x_863_;
v_b_857_ = v_a_861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_908_, lean_object* v_as_909_, lean_object* v_sz_910_, lean_object* v_i_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
size_t v_sz_boxed_915_; size_t v_i_boxed_916_; lean_object* v_res_917_; 
v_sz_boxed_915_ = lean_unbox_usize(v_sz_910_);
lean_dec(v_sz_910_);
v_i_boxed_916_ = lean_unbox_usize(v_i_911_);
lean_dec(v_i_911_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_908_, v_as_909_, v_sz_boxed_915_, v_i_boxed_916_, v_b_912_, v___y_913_);
lean_dec_ref(v_as_909_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_918_, lean_object* v_as_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_b_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec_ref(v___y_923_);
lean_dec_ref(v_descr_918_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_b_922_);
return v___x_926_;
}
else
{
lean_object* v_fst_927_; lean_object* v_snd_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_952_; 
v_fst_927_ = lean_ctor_get(v_b_922_, 0);
v_snd_928_ = lean_ctor_get(v_b_922_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_b_922_);
if (v_isSharedCheck_952_ == 0)
{
v___x_930_ = v_b_922_;
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snd_928_);
lean_inc(v_fst_927_);
lean_dec(v_b_922_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_a_932_; lean_object* v___x_934_; 
v_a_932_ = lean_array_uget_borrowed(v_as_919_, v_i_921_);
if (v_isShared_931_ == 0)
{
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_fst_927_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_snd_928_);
v___x_934_ = v_reuseFailAlloc_951_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
size_t v_sz_935_; size_t v___x_936_; lean_object* v___x_937_; 
v_sz_935_ = lean_array_size(v_a_932_);
v___x_936_ = ((size_t)0ULL);
lean_inc_ref(v___y_923_);
lean_inc_ref(v_descr_918_);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_918_, v_a_932_, v_sz_935_, v___x_936_, v___x_934_, v___y_923_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
v_fst_939_ = lean_ctor_get(v_a_938_, 0);
v_snd_940_ = lean_ctor_get(v_a_938_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v_a_938_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_939_);
lean_dec(v_a_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_fst_939_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_snd_940_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_921_, v___x_946_);
v_i_921_ = v___x_947_;
v_b_922_ = v___x_945_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___y_923_);
lean_dec_ref(v_descr_918_);
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_953_, lean_object* v_as_954_, lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_961_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_953_, v_as_954_, v_sz_boxed_960_, v_i_boxed_961_, v_b_957_, v___y_958_);
lean_dec_ref(v_as_954_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_963_, lean_object* v_as_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_mkInitial_967_; lean_object* v_finalizeImport_968_; lean_object* v___x_969_; 
v_mkInitial_967_ = lean_ctor_get(v_descr_963_, 1);
v_finalizeImport_968_ = lean_ctor_get(v_descr_963_, 5);
lean_inc(v_finalizeImport_968_);
lean_inc_ref(v_mkInitial_967_);
v___x_969_ = lean_apply_1(v_mkInitial_967_, lean_box(0));
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; size_t v_sz_974_; size_t v___x_975_; lean_object* v___x_976_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = 1;
v___x_972_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_a_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v_sz_974_ = lean_array_size(v_as_964_);
v___x_975_ = ((size_t)0ULL);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_963_, v_as_964_, v_sz_974_, v___x_975_, v___x_973_, v_a_965_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_998_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_998_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_998_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_998_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_997_; 
v_fst_981_ = lean_ctor_get(v_a_977_, 0);
v_snd_982_ = lean_ctor_get(v_a_977_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_977_);
if (v_isSharedCheck_997_ == 0)
{
v___x_984_ = v_a_977_;
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v_a_977_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_986_ = lean_apply_1(v_finalizeImport_968_, v_fst_981_);
v___x_987_ = l_Lean_NameSet_empty;
v___x_988_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*2, v___x_971_);
v___x_989_ = lean_box(0);
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 1);
lean_ctor_set(v___x_984_, 1, v___x_989_);
lean_ctor_set(v___x_984_, 0, v___x_988_);
v___x_991_ = v___x_984_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_996_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_snd_982_);
lean_ctor_set(v___x_992_, 2, v___x_989_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_992_);
v___x_994_ = v___x_979_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
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
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_finalizeImport_968_);
v_a_999_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_976_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_976_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_finalizeImport_968_);
lean_dec_ref(v_a_965_);
lean_dec_ref(v_descr_963_);
v_a_1007_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_969_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_969_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1015_, lean_object* v_as_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1015_, v_as_1016_, v_a_1017_);
lean_dec_ref(v_as_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_00_u03c3_1022_, lean_object* v_descr_1023_, lean_object* v_as_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1023_, v_as_1024_, v_a_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_00_u03c3_1030_, lean_object* v_descr_1031_, lean_object* v_as_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1028_, v_00_u03b2_1029_, v_00_u03c3_1030_, v_descr_1031_, v_as_1032_, v_a_1033_);
lean_dec_ref(v_as_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03c3_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_descr_1039_, lean_object* v_as_1040_, size_t v_sz_1041_, size_t v_i_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1039_, v_as_1040_, v_sz_1041_, v_i_1042_, v_b_1043_, v___y_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03c3_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_descr_1050_, lean_object* v_as_1051_, lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1047_, v_00_u03c3_1048_, v_00_u03b2_1049_, v_descr_1050_, v_as_1051_, v_sz_boxed_1057_, v_i_boxed_1058_, v_b_1054_, v___y_1055_);
lean_dec_ref(v_as_1051_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1060_, lean_object* v_00_u03c3_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_descr_1063_, lean_object* v_as_1064_, size_t v_sz_1065_, size_t v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1063_, v_as_1064_, v_sz_1065_, v_i_1066_, v_b_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03c3_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_descr_1074_, lean_object* v_as_1075_, lean_object* v_sz_1076_, lean_object* v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
size_t v_sz_boxed_1081_; size_t v_i_boxed_1082_; lean_object* v_res_1083_; 
v_sz_boxed_1081_ = lean_unbox_usize(v_sz_1076_);
lean_dec(v_sz_1076_);
v_i_boxed_1082_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_res_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1071_, v_00_u03c3_1072_, v_00_u03b2_1073_, v_descr_1074_, v_as_1075_, v_sz_boxed_1081_, v_i_boxed_1082_, v_b_1078_, v___y_1079_);
lean_dec_ref(v_as_1075_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1084_, lean_object* v_descr_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
if (lean_obj_tag(v_a_1087_) == 0)
{
lean_object* v___x_1089_; 
lean_dec(v_a_1086_);
lean_dec_ref(v_descr_1085_);
v___x_1089_ = l_List_reverse___redArg(v_a_1088_);
return v___x_1089_;
}
else
{
lean_object* v_head_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1116_; 
v_head_1090_ = lean_ctor_get(v_a_1087_, 0);
v_tail_1091_ = lean_ctor_get(v_a_1087_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1093_ = v_a_1087_;
v_isShared_1094_ = v_isSharedCheck_1116_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_head_1090_);
lean_dec(v_a_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1116_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___y_1096_; lean_object* v_state_1101_; lean_object* v_activeScopes_1102_; uint8_t v_delimitsLocal_1103_; uint8_t v___x_1104_; 
v_state_1101_ = lean_ctor_get(v_head_1090_, 0);
v_activeScopes_1102_ = lean_ctor_get(v_head_1090_, 1);
v_delimitsLocal_1103_ = lean_ctor_get_uint8(v_head_1090_, sizeof(void*)*2);
v___x_1104_ = l_Lean_NameSet_contains(v_activeScopes_1102_, v_a_1084_);
if (v___x_1104_ == 0)
{
v___y_1096_ = v_head_1090_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1113_; 
lean_inc(v_activeScopes_1102_);
lean_inc(v_state_1101_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_head_1090_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1114_ = lean_ctor_get(v_head_1090_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_head_1090_, 0);
lean_dec(v_unused_1115_);
v___x_1106_ = v_head_1090_;
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v_head_1090_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_addEntry_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v_addEntry_1108_ = lean_ctor_get(v_descr_1085_, 4);
lean_inc(v_addEntry_1108_);
lean_inc(v_a_1086_);
v___x_1109_ = lean_apply_2(v_addEntry_1108_, v_state_1101_, v_a_1086_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_activeScopes_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*2, v_delimitsLocal_1103_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v___y_1096_ = v___x_1111_;
goto v___jp_1095_;
}
}
}
v___jp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_a_1088_);
lean_ctor_set(v___x_1093_, 0, v___y_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___y_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_a_1088_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v_a_1087_ = v_tail_1091_;
v_a_1088_ = v___x_1098_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1117_, lean_object* v_descr_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1117_, v_descr_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
if (lean_obj_tag(v_a_1125_) == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_descr_1123_);
v___x_1127_ = l_List_reverse___redArg(v_a_1126_);
return v___x_1127_;
}
else
{
lean_object* v_head_1128_; lean_object* v_tail_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1149_; 
v_head_1128_ = lean_ctor_get(v_a_1125_, 0);
v_tail_1129_ = lean_ctor_get(v_a_1125_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1131_ = v_a_1125_;
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_tail_1129_);
lean_inc(v_head_1128_);
lean_dec(v_a_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_addEntry_1133_; lean_object* v_state_1134_; lean_object* v_activeScopes_1135_; uint8_t v_delimitsLocal_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
v_addEntry_1133_ = lean_ctor_get(v_descr_1123_, 4);
v_state_1134_ = lean_ctor_get(v_head_1128_, 0);
v_activeScopes_1135_ = lean_ctor_get(v_head_1128_, 1);
v_delimitsLocal_1136_ = lean_ctor_get_uint8(v_head_1128_, sizeof(void*)*2);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_head_1128_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1138_ = v_head_1128_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_activeScopes_1135_);
lean_inc(v_state_1134_);
lean_dec(v_head_1128_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
lean_inc(v_addEntry_1133_);
lean_inc(v_a_1124_);
v___x_1140_ = lean_apply_2(v_addEntry_1133_, v_state_1134_, v_a_1124_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_activeScopes_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*2, v_delimitsLocal_1136_);
v___x_1142_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_a_1126_);
lean_ctor_set(v___x_1131_, 0, v___x_1142_);
v___x_1144_ = v___x_1131_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1126_);
v___x_1144_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
v_a_1125_ = v_tail_1129_;
v_a_1126_ = v___x_1144_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1150_, lean_object* v_s_1151_, lean_object* v_e_1152_){
_start:
{
if (lean_obj_tag(v_e_1152_) == 0)
{
lean_object* v_stateStack_1153_; lean_object* v_scopedEntries_1154_; lean_object* v_newEntries_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1175_; 
v_stateStack_1153_ = lean_ctor_get(v_s_1151_, 0);
v_scopedEntries_1154_ = lean_ctor_get(v_s_1151_, 1);
v_newEntries_1155_ = lean_ctor_get(v_s_1151_, 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_s_1151_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1157_ = v_s_1151_;
v_isShared_1158_ = v_isSharedCheck_1175_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_newEntries_1155_);
lean_inc(v_scopedEntries_1154_);
lean_inc(v_stateStack_1153_);
lean_dec(v_s_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1175_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1174_; 
v_a_1159_ = lean_ctor_get(v_e_1152_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_e_1152_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1161_ = v_e_1152_;
v_isShared_1162_ = v_isSharedCheck_1174_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v_e_1152_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1174_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_toOLeanEntry_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v_toOLeanEntry_1163_ = lean_ctor_get(v_descr_1150_, 3);
lean_inc(v_toOLeanEntry_1163_);
v___x_1164_ = lean_box(0);
lean_inc(v_a_1159_);
v___x_1165_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1150_, v_a_1159_, v_stateStack_1153_, v___x_1164_);
v___x_1166_ = lean_apply_1(v_toOLeanEntry_1163_, v_a_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1166_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_newEntries_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 2, v___x_1169_);
lean_ctor_set(v___x_1157_, 0, v___x_1165_);
v___x_1171_ = v___x_1157_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_scopedEntries_1154_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1176_; lean_object* v_scopedEntries_1177_; lean_object* v_newEntries_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1200_; 
v_stateStack_1176_ = lean_ctor_get(v_s_1151_, 0);
v_scopedEntries_1177_ = lean_ctor_get(v_s_1151_, 1);
v_newEntries_1178_ = lean_ctor_get(v_s_1151_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_s_1151_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1180_ = v_s_1151_;
v_isShared_1181_ = v_isSharedCheck_1200_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_newEntries_1178_);
lean_inc(v_scopedEntries_1177_);
lean_inc(v_stateStack_1176_);
lean_dec(v_s_1151_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1200_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1199_; 
v_a_1182_ = lean_ctor_get(v_e_1152_, 0);
v_a_1183_ = lean_ctor_get(v_e_1152_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_e_1152_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1185_ = v_e_1152_;
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_inc(v_a_1182_);
lean_dec(v_e_1152_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_toOLeanEntry_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v_toOLeanEntry_1187_ = lean_ctor_get(v_descr_1150_, 3);
lean_inc(v_toOLeanEntry_1187_);
v___x_1188_ = lean_box(0);
lean_inc(v_a_1183_);
v___x_1189_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1182_, v_descr_1150_, v_a_1183_, v_stateStack_1176_, v___x_1188_);
lean_inc(v_a_1183_);
lean_inc(v_a_1182_);
v___x_1190_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1177_, v_a_1182_, v_a_1183_);
v___x_1191_ = lean_apply_1(v_toOLeanEntry_1187_, v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1191_);
v___x_1193_ = v___x_1185_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1182_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_newEntries_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 2, v___x_1194_);
lean_ctor_set(v___x_1180_, 1, v___x_1190_);
lean_ctor_set(v___x_1180_, 0, v___x_1189_);
v___x_1196_ = v___x_1180_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_00_u03c3_1203_, lean_object* v_descr_1204_, lean_object* v_s_1205_, lean_object* v_e_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1204_, v_s_1205_, v_e_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_00_u03b1_1210_, lean_object* v_descr_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1216_, lean_object* v_a_1217_, lean_object* v_00_u03b2_1218_, lean_object* v_00_u03b1_1219_, lean_object* v_descr_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1217_, v_descr_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1225_, lean_object* v_a_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_00_u03b1_1228_, lean_object* v_descr_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1225_, v_a_1226_, v_00_u03b2_1227_, v_00_u03b1_1228_, v_descr_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1226_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(lean_object* v_descr_1234_, uint8_t v_level_1235_, lean_object* v_as_1236_, size_t v_i_1237_, size_t v_stop_1238_, lean_object* v_b_1239_){
_start:
{
lean_object* v___y_1241_; uint8_t v___x_1245_; 
v___x_1245_ = lean_usize_dec_eq(v_i_1237_, v_stop_1238_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_array_uget(v_as_1236_, v_i_1237_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_exportEntry_x3f_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_exportEntry_x3f_1251_ = lean_ctor_get(v_descr_1234_, 6);
v___x_1252_ = lean_box(v_level_1235_);
lean_inc_ref(v_exportEntry_x3f_1251_);
v___x_1253_ = lean_apply_2(v_exportEntry_x3f_1251_, v___x_1252_, v_a_1247_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_del_object(v___x_1249_);
v___y_1241_ = v_b_1239_;
goto v___jp_1240_;
}
else
{
lean_object* v_val_1254_; lean_object* v___x_1256_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v___x_1253_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_val_1254_);
v___x_1256_ = v___x_1249_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_val_1254_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_array_push(v_b_1239_, v___x_1256_);
v___y_1241_ = v___x_1257_;
goto v___jp_1240_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1273_; 
v_a_1260_ = lean_ctor_get(v___x_1246_, 0);
v_a_1261_ = lean_ctor_get(v___x_1246_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1263_ = v___x_1246_;
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_inc(v_a_1260_);
lean_dec(v___x_1246_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_exportEntry_x3f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_exportEntry_x3f_1265_ = lean_ctor_get(v_descr_1234_, 6);
v___x_1266_ = lean_box(v_level_1235_);
lean_inc_ref(v_exportEntry_x3f_1265_);
v___x_1267_ = lean_apply_2(v_exportEntry_x3f_1265_, v___x_1266_, v_a_1261_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_del_object(v___x_1263_);
lean_dec(v_a_1260_);
v___y_1241_ = v_b_1239_;
goto v___jp_1240_;
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v___x_1267_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_val_1268_);
v___x_1270_ = v___x_1263_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1260_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_val_1268_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_array_push(v_b_1239_, v___x_1270_);
v___y_1241_ = v___x_1271_;
goto v___jp_1240_;
}
}
}
}
}
else
{
lean_dec_ref(v_descr_1234_);
return v_b_1239_;
}
v___jp_1240_:
{
size_t v___x_1242_; size_t v___x_1243_; 
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_add(v_i_1237_, v___x_1242_);
v_i_1237_ = v___x_1243_;
v_b_1239_ = v___y_1241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg___boxed(lean_object* v_descr_1274_, lean_object* v_level_1275_, lean_object* v_as_1276_, lean_object* v_i_1277_, lean_object* v_stop_1278_, lean_object* v_b_1279_){
_start:
{
uint8_t v_level_boxed_1280_; size_t v_i_boxed_1281_; size_t v_stop_boxed_1282_; lean_object* v_res_1283_; 
v_level_boxed_1280_ = lean_unbox(v_level_1275_);
v_i_boxed_1281_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_stop_boxed_1282_ = lean_unbox_usize(v_stop_1278_);
lean_dec(v_stop_1278_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1274_, v_level_boxed_1280_, v_as_1276_, v_i_boxed_1281_, v_stop_boxed_1282_, v_b_1279_);
lean_dec_ref(v_as_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1286_, uint8_t v_level_1287_, lean_object* v_as_1288_, lean_object* v_start_1289_, lean_object* v_stop_1290_){
_start:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
v___x_1292_ = lean_nat_dec_lt(v_start_1289_, v_stop_1290_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v_descr_1286_);
return v___x_1291_;
}
else
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = lean_array_get_size(v_as_1288_);
v___x_1294_ = lean_nat_dec_le(v_stop_1290_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_lt(v_start_1289_, v___x_1293_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_descr_1286_);
return v___x_1291_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_usize_of_nat(v_start_1289_);
v___x_1297_ = lean_usize_of_nat(v___x_1293_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1286_, v_level_1287_, v_as_1288_, v___x_1296_, v___x_1297_, v___x_1291_);
return v___x_1298_;
}
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_usize_of_nat(v_start_1289_);
v___x_1300_ = lean_usize_of_nat(v_stop_1290_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1286_, v_level_1287_, v_as_1288_, v___x_1299_, v___x_1300_, v___x_1291_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1302_, lean_object* v_level_1303_, lean_object* v_as_1304_, lean_object* v_start_1305_, lean_object* v_stop_1306_){
_start:
{
uint8_t v_level_boxed_1307_; lean_object* v_res_1308_; 
v_level_boxed_1307_ = lean_unbox(v_level_1303_);
v_res_1308_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1302_, v_level_boxed_1307_, v_as_1304_, v_start_1305_, v_stop_1306_);
lean_dec(v_stop_1306_);
lean_dec(v_start_1305_);
lean_dec_ref(v_as_1304_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1309_, uint8_t v_level_1310_, lean_object* v_s_1311_){
_start:
{
lean_object* v_newEntries_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_newEntries_1312_ = lean_ctor_get(v_s_1311_, 2);
lean_inc(v_newEntries_1312_);
lean_dec_ref(v_s_1311_);
v___x_1313_ = lean_array_mk(v_newEntries_1312_);
v___x_1314_ = l_Array_reverse___redArg(v___x_1313_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_array_get_size(v___x_1314_);
v___x_1317_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1309_, v_level_1310_, v___x_1314_, v___x_1315_, v___x_1316_);
lean_dec_ref(v___x_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___boxed(lean_object* v_descr_1318_, lean_object* v_level_1319_, lean_object* v_s_1320_){
_start:
{
uint8_t v_level_boxed_1321_; lean_object* v_res_1322_; 
v_level_boxed_1321_ = lean_unbox(v_level_1319_);
v_res_1322_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1318_, v_level_boxed_1321_, v_s_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_00_u03c3_1325_, lean_object* v_descr_1326_, uint8_t v_level_1327_, lean_object* v_s_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1326_, v_level_1327_, v_s_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_00_u03c3_1332_, lean_object* v_descr_1333_, lean_object* v_level_1334_, lean_object* v_s_1335_){
_start:
{
uint8_t v_level_boxed_1336_; lean_object* v_res_1337_; 
v_level_boxed_1336_ = lean_unbox(v_level_1334_);
v_res_1337_ = l_Lean_ScopedEnvExtension_exportEntriesFn(v_00_u03b1_1330_, v_00_u03b2_1331_, v_00_u03c3_1332_, v_descr_1333_, v_level_boxed_1336_, v_s_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_00_u03c3_1340_, lean_object* v_descr_1341_, uint8_t v_level_1342_, lean_object* v_as_1343_, lean_object* v_start_1344_, lean_object* v_stop_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1341_, v_level_1342_, v_as_1343_, v_start_1344_, v_stop_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_00_u03c3_1349_, lean_object* v_descr_1350_, lean_object* v_level_1351_, lean_object* v_as_1352_, lean_object* v_start_1353_, lean_object* v_stop_1354_){
_start:
{
uint8_t v_level_boxed_1355_; lean_object* v_res_1356_; 
v_level_boxed_1355_ = lean_unbox(v_level_1351_);
v_res_1356_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1347_, v_00_u03b2_1348_, v_00_u03c3_1349_, v_descr_1350_, v_level_boxed_1355_, v_as_1352_, v_start_1353_, v_stop_1354_);
lean_dec(v_stop_1354_);
lean_dec(v_start_1353_);
lean_dec_ref(v_as_1352_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_00_u03c3_1359_, lean_object* v_descr_1360_, uint8_t v_level_1361_, lean_object* v_as_1362_, size_t v_i_1363_, size_t v_stop_1364_, lean_object* v_b_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1360_, v_level_1361_, v_as_1362_, v_i_1363_, v_stop_1364_, v_b_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_00_u03c3_1369_, lean_object* v_descr_1370_, lean_object* v_level_1371_, lean_object* v_as_1372_, lean_object* v_i_1373_, lean_object* v_stop_1374_, lean_object* v_b_1375_){
_start:
{
uint8_t v_level_boxed_1376_; size_t v_i_boxed_1377_; size_t v_stop_boxed_1378_; lean_object* v_res_1379_; 
v_level_boxed_1376_ = lean_unbox(v_level_1371_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_stop_boxed_1378_ = lean_unbox_usize(v_stop_1374_);
lean_dec(v_stop_1374_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(v_00_u03b1_1367_, v_00_u03b2_1368_, v_00_u03c3_1369_, v_descr_1370_, v_level_boxed_1376_, v_as_1372_, v_i_boxed_1377_, v_stop_boxed_1378_, v_b_1375_);
lean_dec_ref(v_as_1372_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5(lean_object* v_x_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5___boxed(lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__5(v_x_1385_, v___y_1386_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v_x_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1389_, lean_object* v_x_1390_){
_start:
{
lean_inc_ref(v_s_1389_);
return v_s_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1391_, v_x_1392_);
lean_dec_ref(v_x_1392_);
lean_dec_ref(v_s_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1394_, lean_object* v_x_1395_, uint8_t v_x_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_x_119__boxed_1401_; lean_object* v_res_1402_; 
v_x_119__boxed_1401_ = lean_unbox(v_x_1400_);
v_res_1402_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1398_, v_x_1399_, v_x_119__boxed_1401_);
lean_dec_ref(v_x_1399_);
lean_dec_ref(v_x_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1405_);
lean_dec_ref(v_x_1405_);
return v_res_1406_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___f_1412_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1413_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1414_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1415_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1418_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___x_1416_);
lean_ctor_set(v___x_1418_, 2, v___f_1415_);
lean_ctor_set(v___x_1418_, 3, v___f_1414_);
lean_ctor_set(v___x_1418_, 4, v___f_1413_);
lean_ctor_set(v___x_1418_, 5, v___f_1412_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1419_){
_start:
{
lean_object* v___f_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___f_1420_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1421_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1422_, 0, v_inst_1419_);
v___f_1423_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___f_1424_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3));
v___x_1425_ = lean_box(0);
v___x_1426_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1427_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___f_1420_);
lean_ctor_set(v___x_1427_, 2, v___f_1421_);
lean_ctor_set(v___x_1427_, 3, v___f_1422_);
lean_ctor_set(v___x_1427_, 4, v___f_1423_);
lean_ctor_set(v___x_1427_, 5, v___x_1426_);
lean_ctor_set(v___x_1427_, 6, v___f_1424_);
v___x_1428_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_a_1430_, lean_object* v_inst_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1431_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1437_, lean_object* v_inst_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1446_ = lean_st_mk_ref(v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_descr_1450_, lean_object* v_x_1451_, lean_object* v_s_1452_, uint8_t v_level_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1450_, v_level_1453_, v_s_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_descr_1455_, lean_object* v_x_1456_, lean_object* v_s_1457_, lean_object* v_level_1458_){
_start:
{
uint8_t v_level_boxed_1459_; lean_object* v_res_1460_; 
v_level_boxed_1459_ = lean_unbox(v_level_1458_);
v_res_1460_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_descr_1455_, v_x_1456_, v_s_1457_, v_level_boxed_1459_);
lean_dec_ref(v_x_1456_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1464_){
_start:
{
lean_object* v_newEntries_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_newEntries_1465_ = lean_ctor_get(v_s_1464_, 2);
v___x_1466_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1467_ = l_List_lengthTR___redArg(v_newEntries_1465_);
v___x_1468_ = l_Nat_reprFast(v___x_1467_);
v___x_1469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1466_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1471_);
lean_dec_ref(v_s_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(lean_object* v_x_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object* v_x_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(v_x_1475_);
lean_dec_ref(v_x_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1479_){
_start:
{
lean_object* v_name_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_name_1481_ = lean_ctor_get(v_descr_1479_, 0);
lean_inc_ref(v_descr_1479_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1482_, 0, v_descr_1479_);
v___f_1483_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1484_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref(v_descr_1479_);
v___x_1485_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1485_, 0, lean_box(0));
lean_closure_set(v___x_1485_, 1, lean_box(0));
lean_closure_set(v___x_1485_, 2, lean_box(0));
lean_closure_set(v___x_1485_, 3, v_descr_1479_);
lean_inc_ref(v_descr_1479_);
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1486_, 0, lean_box(0));
lean_closure_set(v___x_1486_, 1, lean_box(0));
lean_closure_set(v___x_1486_, 2, lean_box(0));
lean_closure_set(v___x_1486_, 3, v_descr_1479_);
lean_inc_ref(v_descr_1479_);
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1487_, 0, lean_box(0));
lean_closure_set(v___x_1487_, 1, lean_box(0));
lean_closure_set(v___x_1487_, 2, lean_box(0));
lean_closure_set(v___x_1487_, 3, v_descr_1479_);
v___x_1488_ = lean_box(2);
v___x_1489_ = lean_box(0);
lean_inc(v_name_1481_);
v___x_1490_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1490_, 0, v_name_1481_);
lean_ctor_set(v___x_1490_, 1, v___x_1485_);
lean_ctor_set(v___x_1490_, 2, v___x_1486_);
lean_ctor_set(v___x_1490_, 3, v___x_1487_);
lean_ctor_set(v___x_1490_, 4, v___f_1482_);
lean_ctor_set(v___x_1490_, 5, v___f_1483_);
lean_ctor_set(v___x_1490_, 6, v___x_1488_);
lean_ctor_set(v___x_1490_, 7, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___f_1484_);
v___x_1492_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1491_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1505_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1497_ = l_Lean_scopedEnvExtensionsRef;
v___x_1498_ = lean_st_ref_take(v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_descr_1479_);
lean_ctor_set(v___x_1499_, 1, v_a_1493_);
lean_inc_ref(v___x_1499_);
v___x_1500_ = lean_array_push(v___x_1498_, v___x_1499_);
v___x_1501_ = lean_st_ref_set(v___x_1497_, v___x_1500_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1499_);
v___x_1503_ = v___x_1495_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1499_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v_descr_1479_);
v_a_1506_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1492_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1492_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1517_, lean_object* v_00_u03b2_1518_, lean_object* v_00_u03c3_1519_, lean_object* v_descr_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_00_u03c3_1525_, lean_object* v_descr_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1523_, v_00_u03b2_1524_, v_00_u03c3_1525_, v_descr_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1529_){
_start:
{
lean_object* v_stateStack_1530_; 
v_stateStack_1530_ = lean_ctor_get(v_s_1529_, 0);
if (lean_obj_tag(v_stateStack_1530_) == 0)
{
return v_s_1529_;
}
else
{
lean_object* v_head_1531_; lean_object* v_scopedEntries_1532_; lean_object* v_newEntries_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1551_; 
lean_inc_ref(v_stateStack_1530_);
v_head_1531_ = lean_ctor_get(v_stateStack_1530_, 0);
lean_inc(v_head_1531_);
v_scopedEntries_1532_ = lean_ctor_get(v_s_1529_, 1);
v_newEntries_1533_ = lean_ctor_get(v_s_1529_, 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_s_1529_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_s_1529_, 0);
lean_dec(v_unused_1552_);
v___x_1535_ = v_s_1529_;
v_isShared_1536_ = v_isSharedCheck_1551_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_newEntries_1533_);
lean_inc(v_scopedEntries_1532_);
lean_dec(v_s_1529_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1551_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_state_1537_; lean_object* v_activeScopes_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1550_; 
v_state_1537_ = lean_ctor_get(v_head_1531_, 0);
v_activeScopes_1538_ = lean_ctor_get(v_head_1531_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_head_1531_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1540_ = v_head_1531_;
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_activeScopes_1538_);
lean_inc(v_state_1537_);
lean_dec(v_head_1531_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = 1;
if (v_isShared_1541_ == 0)
{
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_state_1537_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_activeScopes_1538_);
v___x_1544_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*2, v___x_1542_);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_stateStack_1530_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1545_);
v___x_1547_ = v___x_1535_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_scopedEntries_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_newEntries_1533_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1554_, lean_object* v_env_1555_){
_start:
{
lean_object* v_ext_1556_; lean_object* v___f_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_ext_1556_ = lean_ctor_get(v_ext_1554_, 1);
lean_inc_ref(v_ext_1556_);
lean_dec_ref(v_ext_1554_);
v___f_1557_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1558_ = lean_box(1);
v___x_1559_ = lean_box(0);
v___x_1560_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1556_, v_env_1555_, v___f_1557_, v___x_1558_, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1561_, lean_object* v_00_u03b2_1562_, lean_object* v_00_u03c3_1563_, lean_object* v_ext_1564_, lean_object* v_env_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1564_, v_env_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1567_){
_start:
{
lean_object* v_stateStack_1568_; 
v_stateStack_1568_ = lean_ctor_get(v_s_1567_, 0);
if (lean_obj_tag(v_stateStack_1568_) == 1)
{
lean_object* v_tail_1569_; 
v_tail_1569_ = lean_ctor_get(v_stateStack_1568_, 1);
if (lean_obj_tag(v_tail_1569_) == 1)
{
lean_object* v_scopedEntries_1570_; lean_object* v_newEntries_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_inc_ref(v_tail_1569_);
v_scopedEntries_1570_ = lean_ctor_get(v_s_1567_, 1);
v_newEntries_1571_ = lean_ctor_get(v_s_1567_, 2);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_s_1567_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_s_1567_, 0);
lean_dec(v_unused_1579_);
v___x_1573_ = v_s_1567_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_newEntries_1571_);
lean_inc(v_scopedEntries_1570_);
lean_dec(v_s_1567_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_tail_1569_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_tail_1569_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_scopedEntries_1570_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_newEntries_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
return v_s_1567_;
}
}
else
{
return v_s_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1581_, lean_object* v_env_1582_){
_start:
{
lean_object* v_ext_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_ext_1583_ = lean_ctor_get(v_ext_1581_, 1);
lean_inc_ref(v_ext_1583_);
lean_dec_ref(v_ext_1581_);
v___f_1584_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1585_ = lean_box(1);
v___x_1586_ = lean_box(0);
v___x_1587_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1583_, v_env_1582_, v___f_1584_, v___x_1585_, v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_00_u03c3_1590_, lean_object* v_ext_1591_, lean_object* v_env_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1591_, v_env_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_s_1594_){
_start:
{
lean_object* v_stateStack_1595_; 
v_stateStack_1595_ = lean_ctor_get(v_s_1594_, 0);
lean_inc(v_stateStack_1595_);
if (lean_obj_tag(v_stateStack_1595_) == 0)
{
return v_s_1594_;
}
else
{
lean_object* v_head_1596_; lean_object* v_scopedEntries_1597_; lean_object* v_newEntries_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1624_; 
v_head_1596_ = lean_ctor_get(v_stateStack_1595_, 0);
lean_inc(v_head_1596_);
v_scopedEntries_1597_ = lean_ctor_get(v_s_1594_, 1);
v_newEntries_1598_ = lean_ctor_get(v_s_1594_, 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_s_1594_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_s_1594_, 0);
lean_dec(v_unused_1625_);
v___x_1600_ = v_s_1594_;
v_isShared_1601_ = v_isSharedCheck_1624_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_newEntries_1598_);
lean_inc(v_scopedEntries_1597_);
lean_dec(v_s_1594_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1624_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_tail_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1622_; 
v_tail_1602_ = lean_ctor_get(v_stateStack_1595_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_stateStack_1595_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_stateStack_1595_, 0);
lean_dec(v_unused_1623_);
v___x_1604_ = v_stateStack_1595_;
v_isShared_1605_ = v_isSharedCheck_1622_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_tail_1602_);
lean_dec(v_stateStack_1595_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1622_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_state_1606_; lean_object* v_activeScopes_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1621_; 
v_state_1606_ = lean_ctor_get(v_head_1596_, 0);
v_activeScopes_1607_ = lean_ctor_get(v_head_1596_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_head_1596_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1609_ = v_head_1596_;
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_activeScopes_1607_);
lean_inc(v_state_1606_);
lean_dec(v_head_1596_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
uint8_t v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = 0;
if (v_isShared_1610_ == 0)
{
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_state_1606_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_activeScopes_1607_);
v___x_1613_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*2, v___x_1611_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1613_);
v___x_1615_ = v___x_1604_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_tail_1602_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1615_);
v___x_1617_ = v___x_1600_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_scopedEntries_1597_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_newEntries_1598_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1627_, lean_object* v_env_1628_){
_start:
{
lean_object* v_ext_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_ext_1629_ = lean_ctor_get(v_ext_1627_, 1);
lean_inc_ref(v_ext_1629_);
lean_dec_ref(v_ext_1627_);
v___f_1630_ = ((lean_object*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0));
v___x_1631_ = lean_box(1);
v___x_1632_ = lean_box(0);
v___x_1633_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1629_, v_env_1628_, v___f_1630_, v___x_1631_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_00_u03c3_1636_, lean_object* v_ext_1637_, lean_object* v_env_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1637_, v_env_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1640_, lean_object* v_env_1641_, lean_object* v_b_1642_){
_start:
{
lean_object* v_ext_1643_; lean_object* v_toEnvExtension_1644_; lean_object* v_asyncMode_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_ext_1643_ = lean_ctor_get(v_ext_1640_, 1);
lean_inc_ref(v_ext_1643_);
lean_dec_ref(v_ext_1640_);
v_toEnvExtension_1644_ = lean_ctor_get(v_ext_1643_, 0);
v_asyncMode_1645_ = lean_ctor_get(v_toEnvExtension_1644_, 2);
lean_inc(v_asyncMode_1645_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_b_1642_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1643_, v_env_1641_, v___x_1646_, v_asyncMode_1645_, v___x_1647_);
lean_dec(v_asyncMode_1645_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_00_u03c3_1651_, lean_object* v_ext_1652_, lean_object* v_env_1653_, lean_object* v_b_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1652_, v_env_1653_, v_b_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1656_, lean_object* v_env_1657_, lean_object* v_namespaceName_1658_, lean_object* v_b_1659_){
_start:
{
lean_object* v_ext_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1671_; 
v_ext_1660_ = lean_ctor_get(v_ext_1656_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_ext_1656_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_ext_1656_, 0);
lean_dec(v_unused_1672_);
v___x_1662_ = v_ext_1656_;
v_isShared_1663_ = v_isSharedCheck_1671_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_ext_1660_);
lean_dec(v_ext_1656_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1671_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_toEnvExtension_1664_; lean_object* v_asyncMode_1665_; lean_object* v___x_1667_; 
v_toEnvExtension_1664_ = lean_ctor_get(v_ext_1660_, 0);
v_asyncMode_1665_ = lean_ctor_get(v_toEnvExtension_1664_, 2);
lean_inc(v_asyncMode_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 1);
lean_ctor_set(v___x_1662_, 1, v_b_1659_);
lean_ctor_set(v___x_1662_, 0, v_namespaceName_1658_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_namespaceName_1658_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_b_1659_);
v___x_1667_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_box(0);
v___x_1669_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1660_, v_env_1657_, v___x_1667_, v_asyncMode_1665_, v___x_1668_);
lean_dec(v_asyncMode_1665_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_00_u03c3_1675_, lean_object* v_ext_1676_, lean_object* v_env_1677_, lean_object* v_namespaceName_1678_, lean_object* v_b_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1676_, v_env_1677_, v_namespaceName_1678_, v_b_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1681_, lean_object* v_states_1682_, lean_object* v_b_1683_){
_start:
{
if (lean_obj_tag(v_states_1682_) == 0)
{
lean_dec(v_b_1683_);
lean_dec_ref(v_ext_1681_);
return v_states_1682_;
}
else
{
lean_object* v_descr_1684_; lean_object* v_head_1685_; lean_object* v_tail_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1709_; 
v_descr_1684_ = lean_ctor_get(v_ext_1681_, 0);
v_head_1685_ = lean_ctor_get(v_states_1682_, 0);
v_tail_1686_ = lean_ctor_get(v_states_1682_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_states_1682_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1688_ = v_states_1682_;
v_isShared_1689_ = v_isSharedCheck_1709_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_tail_1686_);
lean_inc(v_head_1685_);
lean_dec(v_states_1682_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1709_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_addEntry_1690_; lean_object* v_state_1691_; lean_object* v_activeScopes_1692_; uint8_t v_delimitsLocal_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1708_; 
v_addEntry_1690_ = lean_ctor_get(v_descr_1684_, 4);
v_state_1691_ = lean_ctor_get(v_head_1685_, 0);
v_activeScopes_1692_ = lean_ctor_get(v_head_1685_, 1);
v_delimitsLocal_1693_ = lean_ctor_get_uint8(v_head_1685_, sizeof(void*)*2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_head_1685_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1695_ = v_head_1685_;
v_isShared_1696_ = v_isSharedCheck_1708_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_activeScopes_1692_);
lean_inc(v_state_1691_);
lean_dec(v_head_1685_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1708_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v_top_1699_; 
lean_inc(v_addEntry_1690_);
lean_inc(v_b_1683_);
v___x_1697_ = lean_apply_2(v_addEntry_1690_, v_state_1691_, v_b_1683_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v_top_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_activeScopes_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*2, v_delimitsLocal_1693_);
v_top_1699_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
if (v_delimitsLocal_1693_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = l_Lean_stateStackModify___redArg(v_ext_1681_, v_tail_1686_, v_b_1683_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v___x_1700_);
lean_ctor_set(v___x_1688_, 0, v_top_1699_);
v___x_1702_ = v___x_1688_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_top_1699_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
else
{
lean_object* v___x_1705_; 
lean_dec(v_b_1683_);
lean_dec_ref(v_ext_1681_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v_top_1699_);
v___x_1705_ = v___x_1688_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_top_1699_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_tail_1686_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_00_u03c3_1712_, lean_object* v_ext_1713_, lean_object* v_states_1714_, lean_object* v_b_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_stateStackModify___redArg(v_ext_1713_, v_states_1714_, v_b_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1717_, lean_object* v_b_1718_, lean_object* v_s_1719_){
_start:
{
lean_object* v_stateStack_1720_; lean_object* v_scopedEntries_1721_; lean_object* v_newEntries_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
v_stateStack_1720_ = lean_ctor_get(v_s_1719_, 0);
v_scopedEntries_1721_ = lean_ctor_get(v_s_1719_, 1);
v_newEntries_1722_ = lean_ctor_get(v_s_1719_, 2);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_s_1719_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_s_1719_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_newEntries_1722_);
lean_inc(v_scopedEntries_1721_);
lean_inc(v_stateStack_1720_);
lean_dec(v_s_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_stateStackModify___redArg(v_ext_1717_, v_stateStack_1720_, v_b_1718_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_scopedEntries_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_newEntries_1722_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1731_, lean_object* v_env_1732_, lean_object* v_b_1733_){
_start:
{
lean_object* v_ext_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_ext_1734_ = lean_ctor_get(v_ext_1731_, 1);
lean_inc_ref(v_ext_1734_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1735_, 0, v_ext_1731_);
lean_closure_set(v___f_1735_, 1, v_b_1733_);
v___x_1736_ = lean_box(1);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1734_, v_env_1732_, v___f_1735_, v___x_1736_, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_00_u03c3_1741_, lean_object* v_ext_1742_, lean_object* v_env_1743_, lean_object* v_b_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1742_, v_env_1743_, v_b_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1746_, lean_object* v_ext_1747_, lean_object* v_b_1748_, uint8_t v_kind_1749_, lean_object* v_namespaceName_1750_){
_start:
{
switch(v_kind_1749_)
{
case 0:
{
lean_object* v___x_1751_; 
lean_dec(v_namespaceName_1750_);
v___x_1751_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1747_, v_env_1746_, v_b_1748_);
return v___x_1751_;
}
case 1:
{
lean_object* v___x_1752_; 
lean_dec(v_namespaceName_1750_);
v___x_1752_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1747_, v_env_1746_, v_b_1748_);
return v___x_1752_;
}
default: 
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1747_, v_env_1746_, v_namespaceName_1750_, v_b_1748_);
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1754_, lean_object* v_ext_1755_, lean_object* v_b_1756_, lean_object* v_kind_1757_, lean_object* v_namespaceName_1758_){
_start:
{
uint8_t v_kind_boxed_1759_; lean_object* v_res_1760_; 
v_kind_boxed_1759_ = lean_unbox(v_kind_1757_);
v_res_1760_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1754_, v_ext_1755_, v_b_1756_, v_kind_boxed_1759_, v_namespaceName_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_00_u03c3_1763_, lean_object* v_env_1764_, lean_object* v_ext_1765_, lean_object* v_b_1766_, uint8_t v_kind_1767_, lean_object* v_namespaceName_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1764_, v_ext_1765_, v_b_1766_, v_kind_1767_, v_namespaceName_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_00_u03c3_1772_, lean_object* v_env_1773_, lean_object* v_ext_1774_, lean_object* v_b_1775_, lean_object* v_kind_1776_, lean_object* v_namespaceName_1777_){
_start:
{
uint8_t v_kind_boxed_1778_; lean_object* v_res_1779_; 
v_kind_boxed_1778_ = lean_unbox(v_kind_1776_);
v_res_1779_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1770_, v_00_u03b2_1771_, v_00_u03c3_1772_, v_env_1773_, v_ext_1774_, v_b_1775_, v_kind_boxed_1778_, v_namespaceName_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1780_, lean_object* v_b_1781_, uint8_t v_kind_1782_, lean_object* v_ns_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1784_, v_ext_1780_, v_b_1781_, v_kind_1782_, v_ns_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1786_, lean_object* v_b_1787_, lean_object* v_kind_1788_, lean_object* v_ns_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v_kind_boxed_1791_; lean_object* v_res_1792_; 
v_kind_boxed_1791_ = lean_unbox(v_kind_1788_);
v_res_1792_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1786_, v_b_1787_, v_kind_boxed_1791_, v_ns_1789_, v_x_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1793_, lean_object* v_ext_1794_, lean_object* v_b_1795_, uint8_t v_kind_1796_, lean_object* v_ns_1797_){
_start:
{
lean_object* v_modifyEnv_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; 
v_modifyEnv_1798_ = lean_ctor_get(v_inst_1793_, 1);
lean_inc(v_modifyEnv_1798_);
lean_dec_ref(v_inst_1793_);
v___x_1799_ = lean_box(v_kind_1796_);
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1800_, 0, v_ext_1794_);
lean_closure_set(v___f_1800_, 1, v_b_1795_);
lean_closure_set(v___f_1800_, 2, v___x_1799_);
lean_closure_set(v___f_1800_, 3, v_ns_1797_);
v___x_1801_ = lean_apply_1(v_modifyEnv_1798_, v___f_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1802_, lean_object* v_ext_1803_, lean_object* v_b_1804_, lean_object* v_kind_1805_, lean_object* v_ns_1806_){
_start:
{
uint8_t v_kind_boxed_1807_; lean_object* v_res_1808_; 
v_kind_boxed_1807_ = lean_unbox(v_kind_1805_);
v_res_1808_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1802_, v_ext_1803_, v_b_1804_, v_kind_boxed_1807_, v_ns_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_ext_1812_, lean_object* v_b_1813_, uint8_t v_kind_1814_){
_start:
{
lean_object* v_toBind_1815_; lean_object* v_getCurrNamespace_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v_toBind_1815_ = lean_ctor_get(v_inst_1809_, 1);
lean_inc(v_toBind_1815_);
lean_dec_ref(v_inst_1809_);
v_getCurrNamespace_1816_ = lean_ctor_get(v_inst_1810_, 0);
lean_inc(v_getCurrNamespace_1816_);
lean_dec_ref(v_inst_1810_);
v___x_1817_ = lean_box(v_kind_1814_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1818_, 0, v_inst_1811_);
lean_closure_set(v___f_1818_, 1, v_ext_1812_);
lean_closure_set(v___f_1818_, 2, v_b_1813_);
lean_closure_set(v___f_1818_, 3, v___x_1817_);
v___x_1819_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v_getCurrNamespace_1816_, v___f_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_ext_1823_, lean_object* v_b_1824_, lean_object* v_kind_1825_){
_start:
{
uint8_t v_kind_boxed_1826_; lean_object* v_res_1827_; 
v_kind_boxed_1826_ = lean_unbox(v_kind_1825_);
v_res_1827_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1820_, v_inst_1821_, v_inst_1822_, v_ext_1823_, v_b_1824_, v_kind_boxed_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1828_, lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_00_u03c3_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_ext_1835_, lean_object* v_b_1836_, uint8_t v_kind_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1832_, v_inst_1833_, v_inst_1834_, v_ext_1835_, v_b_1836_, v_kind_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1839_, lean_object* v_00_u03b1_1840_, lean_object* v_00_u03b2_1841_, lean_object* v_00_u03c3_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_ext_1846_, lean_object* v_b_1847_, lean_object* v_kind_1848_){
_start:
{
uint8_t v_kind_boxed_1849_; lean_object* v_res_1850_; 
v_kind_boxed_1849_ = lean_unbox(v_kind_1848_);
v_res_1850_ = l_Lean_ScopedEnvExtension_add(v_m_1839_, v_00_u03b1_1840_, v_00_u03b2_1841_, v_00_u03c3_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_ext_1846_, v_b_1847_, v_kind_boxed_1849_);
return v_res_1850_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1854_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1855_ = lean_unsigned_to_nat(16u);
v___x_1856_ = lean_unsigned_to_nat(191u);
v___x_1857_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1858_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1859_ = l_mkPanicMessageWithDecl(v___x_1858_, v___x_1857_, v___x_1856_, v___x_1855_, v___x_1854_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1860_, lean_object* v_ext_1861_, lean_object* v_env_1862_, lean_object* v_asyncMode_1863_){
_start:
{
lean_object* v_ext_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_stateStack_1868_; 
v_ext_1864_ = lean_ctor_get(v_ext_1861_, 1);
v___x_1865_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1866_ = lean_box(0);
v___x_1867_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1865_, v_ext_1864_, v_env_1862_, v_asyncMode_1863_, v___x_1866_);
v_stateStack_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_stateStack_1868_);
lean_dec(v___x_1867_);
if (lean_obj_tag(v_stateStack_1868_) == 1)
{
lean_object* v_head_1869_; lean_object* v_state_1870_; 
lean_dec(v_inst_1860_);
v_head_1869_ = lean_ctor_get(v_stateStack_1868_, 0);
lean_inc(v_head_1869_);
lean_dec_ref(v_stateStack_1868_);
v_state_1870_ = lean_ctor_get(v_head_1869_, 0);
lean_inc(v_state_1870_);
lean_dec(v_head_1869_);
return v_state_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_stateStack_1868_);
v___x_1871_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1872_ = l_panic___redArg(v_inst_1860_, v___x_1871_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1873_, lean_object* v_ext_1874_, lean_object* v_env_1875_, lean_object* v_asyncMode_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1873_, v_ext_1874_, v_env_1875_, v_asyncMode_1876_);
lean_dec(v_asyncMode_1876_);
lean_dec_ref(v_ext_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1878_, lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_inst_1881_, lean_object* v_ext_1882_, lean_object* v_env_1883_, lean_object* v_asyncMode_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1881_, v_ext_1882_, v_env_1883_, v_asyncMode_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1886_, lean_object* v_00_u03b1_1887_, lean_object* v_00_u03b2_1888_, lean_object* v_inst_1889_, lean_object* v_ext_1890_, lean_object* v_env_1891_, lean_object* v_asyncMode_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1886_, v_00_u03b1_1887_, v_00_u03b2_1888_, v_inst_1889_, v_ext_1890_, v_env_1891_, v_asyncMode_1892_);
lean_dec(v_asyncMode_1892_);
lean_dec_ref(v_ext_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1894_, lean_object* v_as_1895_, size_t v_sz_1896_, size_t v_i_1897_, lean_object* v_b_1898_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_usize_dec_lt(v_i_1897_, v_sz_1896_);
if (v___x_1899_ == 0)
{
lean_dec_ref(v_ext_1894_);
return v_b_1898_;
}
else
{
lean_object* v_descr_1900_; lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1915_; 
v_descr_1900_ = lean_ctor_get(v_ext_1894_, 0);
v_snd_1901_ = lean_ctor_get(v_b_1898_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_b_1898_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_b_1898_, 0);
lean_dec(v_unused_1916_);
v___x_1903_ = v_b_1898_;
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_dec(v_b_1898_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1915_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_addEntry_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; lean_object* v_state_1908_; lean_object* v___x_1910_; 
v_addEntry_1905_ = lean_ctor_get(v_descr_1900_, 4);
v___x_1906_ = lean_box(0);
v_a_1907_ = lean_array_uget_borrowed(v_as_1895_, v_i_1897_);
lean_inc(v_addEntry_1905_);
lean_inc(v_a_1907_);
v_state_1908_ = lean_apply_2(v_addEntry_1905_, v_snd_1901_, v_a_1907_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_state_1908_);
lean_ctor_set(v___x_1903_, 0, v___x_1906_);
v___x_1910_ = v___x_1903_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_state_1908_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
size_t v___x_1911_; size_t v___x_1912_; 
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1897_, v___x_1911_);
v_i_1897_ = v___x_1912_;
v_b_1898_ = v___x_1910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1917_, lean_object* v_as_1918_, lean_object* v_sz_1919_, lean_object* v_i_1920_, lean_object* v_b_1921_){
_start:
{
size_t v_sz_boxed_1922_; size_t v_i_boxed_1923_; lean_object* v_res_1924_; 
v_sz_boxed_1922_ = lean_unbox_usize(v_sz_1919_);
lean_dec(v_sz_1919_);
v_i_boxed_1923_ = lean_unbox_usize(v_i_1920_);
lean_dec(v_i_1920_);
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1917_, v_as_1918_, v_sz_boxed_1922_, v_i_boxed_1923_, v_b_1921_);
lean_dec_ref(v_as_1918_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1925_, lean_object* v_as_1926_, size_t v_sz_1927_, size_t v_i_1928_, lean_object* v_b_1929_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_lt(v_i_1928_, v_sz_1927_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v_ext_1925_);
return v_b_1929_;
}
else
{
lean_object* v_descr_1931_; lean_object* v_snd_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1946_; 
v_descr_1931_ = lean_ctor_get(v_ext_1925_, 0);
v_snd_1932_ = lean_ctor_get(v_b_1929_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_b_1929_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_b_1929_, 0);
lean_dec(v_unused_1947_);
v___x_1934_ = v_b_1929_;
v_isShared_1935_ = v_isSharedCheck_1946_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1932_);
lean_dec(v_b_1929_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1946_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_addEntry_1936_; lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v_state_1939_; lean_object* v___x_1941_; 
v_addEntry_1936_ = lean_ctor_get(v_descr_1931_, 4);
v___x_1937_ = lean_box(0);
v_a_1938_ = lean_array_uget_borrowed(v_as_1926_, v_i_1928_);
lean_inc(v_addEntry_1936_);
lean_inc(v_a_1938_);
v_state_1939_ = lean_apply_2(v_addEntry_1936_, v_snd_1932_, v_a_1938_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v_state_1939_);
lean_ctor_set(v___x_1934_, 0, v___x_1937_);
v___x_1941_ = v___x_1934_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_state_1939_);
v___x_1941_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
size_t v___x_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((size_t)1ULL);
v___x_1943_ = lean_usize_add(v_i_1928_, v___x_1942_);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1925_, v_as_1926_, v_sz_1927_, v___x_1943_, v___x_1941_);
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1948_, lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_){
_start:
{
size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1948_, v_as_1949_, v_sz_boxed_1953_, v_i_boxed_1954_, v_b_1952_);
lean_dec_ref(v_as_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_ext_1956_, lean_object* v_inh_1957_, lean_object* v_n_1958_, lean_object* v_b_1959_){
_start:
{
if (lean_obj_tag(v_n_1958_) == 0)
{
lean_object* v_cs_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1975_; 
v_cs_1960_ = lean_ctor_get(v_n_1958_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_n_1958_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1962_ = v_n_1958_;
v_isShared_1963_ = v_isSharedCheck_1975_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_cs_1960_);
lean_dec(v_n_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1975_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; size_t v_sz_1966_; size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v_fst_1969_; 
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v_b_1959_);
v_sz_1966_ = lean_array_size(v_cs_1960_);
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_1956_, v_inh_1957_, v_cs_1960_, v_sz_1966_, v___x_1967_, v___x_1965_);
lean_dec_ref(v_cs_1960_);
v_fst_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_fst_1969_);
if (lean_obj_tag(v_fst_1969_) == 0)
{
lean_object* v_snd_1970_; lean_object* v___x_1972_; 
v_snd_1970_ = lean_ctor_get(v___x_1968_, 1);
lean_inc(v_snd_1970_);
lean_dec_ref(v___x_1968_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set_tag(v___x_1962_, 1);
lean_ctor_set(v___x_1962_, 0, v_snd_1970_);
v___x_1972_ = v___x_1962_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_snd_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v_val_1974_; 
lean_dec_ref(v___x_1968_);
lean_del_object(v___x_1962_);
v_val_1974_ = lean_ctor_get(v_fst_1969_, 0);
lean_inc(v_val_1974_);
lean_dec_ref(v_fst_1969_);
return v_val_1974_;
}
}
}
else
{
lean_object* v_vs_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1991_; 
v_vs_1976_ = lean_ctor_get(v_n_1958_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_n_1958_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1978_ = v_n_1958_;
v_isShared_1979_ = v_isSharedCheck_1991_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_vs_1976_);
lean_dec(v_n_1958_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1991_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; size_t v_sz_1982_; size_t v___x_1983_; lean_object* v___x_1984_; lean_object* v_fst_1985_; 
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_b_1959_);
v_sz_1982_ = lean_array_size(v_vs_1976_);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1956_, v_vs_1976_, v_sz_1982_, v___x_1983_, v___x_1981_);
lean_dec_ref(v_vs_1976_);
v_fst_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_fst_1985_);
if (lean_obj_tag(v_fst_1985_) == 0)
{
lean_object* v_snd_1986_; lean_object* v___x_1988_; 
v_snd_1986_ = lean_ctor_get(v___x_1984_, 1);
lean_inc(v_snd_1986_);
lean_dec_ref(v___x_1984_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v_snd_1986_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_snd_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v_val_1990_; 
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1978_);
v_val_1990_ = lean_ctor_get(v_fst_1985_, 0);
lean_inc(v_val_1990_);
lean_dec_ref(v_fst_1985_);
return v_val_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_ext_1992_, lean_object* v_inh_1993_, lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_1998_ == 0)
{
lean_dec_ref(v_ext_1992_);
return v_b_1997_;
}
else
{
lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2017_; 
v_snd_1999_ = lean_ctor_get(v_b_1997_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_b_1997_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_b_1997_, 0);
lean_dec(v_unused_2018_);
v___x_2001_ = v_b_1997_;
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_dec(v_b_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_array_uget_borrowed(v_as_1994_, v_i_1996_);
lean_inc(v_snd_1999_);
lean_inc(v_a_2003_);
lean_inc_ref(v_ext_1992_);
v___x_2004_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_1992_, v_inh_1993_, v_a_2003_, v_snd_1999_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
lean_dec_ref(v_ext_1992_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2005_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_snd_1999_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_dec(v_snd_1999_);
v_a_2009_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2004_);
v___x_2010_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v_a_2009_);
lean_ctor_set(v___x_2001_, 0, v___x_2010_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_a_2009_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
size_t v___x_2013_; size_t v___x_2014_; 
v___x_2013_ = ((size_t)1ULL);
v___x_2014_ = lean_usize_add(v_i_1996_, v___x_2013_);
v_i_1996_ = v___x_2014_;
v_b_1997_ = v___x_2012_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2019_, lean_object* v_inh_2020_, lean_object* v_as_2021_, lean_object* v_sz_2022_, lean_object* v_i_2023_, lean_object* v_b_2024_){
_start:
{
size_t v_sz_boxed_2025_; size_t v_i_boxed_2026_; lean_object* v_res_2027_; 
v_sz_boxed_2025_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2026_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_2019_, v_inh_2020_, v_as_2021_, v_sz_boxed_2025_, v_i_boxed_2026_, v_b_2024_);
lean_dec_ref(v_as_2021_);
lean_dec(v_inh_2020_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_ext_2028_, lean_object* v_inh_2029_, lean_object* v_n_2030_, lean_object* v_b_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2028_, v_inh_2029_, v_n_2030_, v_b_2031_);
lean_dec(v_inh_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2033_, lean_object* v_as_2034_, size_t v_sz_2035_, size_t v_i_2036_, lean_object* v_b_2037_){
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
size_t v___x_2050_; size_t v___x_2051_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2036_, v___x_2050_);
v_i_2036_ = v___x_2051_;
v_b_2037_ = v___x_2049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2056_, lean_object* v_as_2057_, lean_object* v_sz_2058_, lean_object* v_i_2059_, lean_object* v_b_2060_){
_start:
{
size_t v_sz_boxed_2061_; size_t v_i_boxed_2062_; lean_object* v_res_2063_; 
v_sz_boxed_2061_ = lean_unbox_usize(v_sz_2058_);
lean_dec(v_sz_2058_);
v_i_boxed_2062_ = lean_unbox_usize(v_i_2059_);
lean_dec(v_i_2059_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2056_, v_as_2057_, v_sz_boxed_2061_, v_i_boxed_2062_, v_b_2060_);
lean_dec_ref(v_as_2057_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2064_, lean_object* v_as_2065_, size_t v_sz_2066_, size_t v_i_2067_, lean_object* v_b_2068_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_usize_dec_lt(v_i_2067_, v_sz_2066_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_ext_2064_);
return v_b_2068_;
}
else
{
lean_object* v_descr_2070_; lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2085_; 
v_descr_2070_ = lean_ctor_get(v_ext_2064_, 0);
v_snd_2071_ = lean_ctor_get(v_b_2068_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_b_2068_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_b_2068_, 0);
lean_dec(v_unused_2086_);
v___x_2073_ = v_b_2068_;
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_dec(v_b_2068_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_addEntry_2075_; lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v_state_2078_; lean_object* v___x_2080_; 
v_addEntry_2075_ = lean_ctor_get(v_descr_2070_, 4);
v___x_2076_ = lean_box(0);
v_a_2077_ = lean_array_uget_borrowed(v_as_2065_, v_i_2067_);
lean_inc(v_addEntry_2075_);
lean_inc(v_a_2077_);
v_state_2078_ = lean_apply_2(v_addEntry_2075_, v_snd_2071_, v_a_2077_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_state_2078_);
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_state_2078_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((size_t)1ULL);
v___x_2082_ = lean_usize_add(v_i_2067_, v___x_2081_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2064_, v_as_2065_, v_sz_2066_, v___x_2082_, v___x_2080_);
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2087_, lean_object* v_as_2088_, lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_b_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2087_, v_as_2088_, v_sz_boxed_2092_, v_i_boxed_2093_, v_b_2091_);
lean_dec_ref(v_as_2088_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2095_, lean_object* v_t_2096_, lean_object* v_init_2097_){
_start:
{
lean_object* v_root_2098_; lean_object* v_tail_2099_; lean_object* v___x_2100_; 
v_root_2098_ = lean_ctor_get(v_t_2096_, 0);
lean_inc_ref(v_root_2098_);
v_tail_2099_ = lean_ctor_get(v_t_2096_, 1);
lean_inc_ref(v_tail_2099_);
lean_dec_ref(v_t_2096_);
lean_inc(v_init_2097_);
lean_inc_ref(v_ext_2095_);
v___x_2100_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2095_, v_init_2097_, v_root_2098_, v_init_2097_);
lean_dec(v_init_2097_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
lean_dec_ref(v_tail_2099_);
lean_dec_ref(v_ext_2095_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
return v_a_2101_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; size_t v_sz_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v_fst_2108_; 
v_a_2102_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2100_);
v___x_2103_ = lean_box(0);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_a_2102_);
v_sz_2105_ = lean_array_size(v_tail_2099_);
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2095_, v_tail_2099_, v_sz_2105_, v___x_2106_, v___x_2104_);
lean_dec_ref(v_tail_2099_);
v_fst_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_fst_2108_);
if (lean_obj_tag(v_fst_2108_) == 0)
{
lean_object* v_snd_2109_; 
v_snd_2109_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2109_);
lean_dec_ref(v___x_2107_);
return v_snd_2109_;
}
else
{
lean_object* v_val_2110_; 
lean_dec_ref(v___x_2107_);
v_val_2110_ = lean_ctor_get(v_fst_2108_, 0);
lean_inc(v_val_2110_);
lean_dec_ref(v_fst_2108_);
return v_val_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2111_, lean_object* v_ext_2112_, lean_object* v_s_2113_){
_start:
{
lean_object* v_stateStack_2114_; 
v_stateStack_2114_ = lean_ctor_get(v_s_2113_, 0);
lean_inc(v_stateStack_2114_);
if (lean_obj_tag(v_stateStack_2114_) == 1)
{
lean_object* v_scopedEntries_2115_; lean_object* v_newEntries_2116_; lean_object* v_head_2117_; lean_object* v_tail_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2147_; 
v_scopedEntries_2115_ = lean_ctor_get(v_s_2113_, 1);
v_newEntries_2116_ = lean_ctor_get(v_s_2113_, 2);
v_head_2117_ = lean_ctor_get(v_stateStack_2114_, 0);
v_tail_2118_ = lean_ctor_get(v_stateStack_2114_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_stateStack_2114_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2120_ = v_stateStack_2114_;
v_isShared_2121_ = v_isSharedCheck_2147_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_tail_2118_);
lean_inc(v_head_2117_);
lean_dec(v_stateStack_2114_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2147_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___y_2123_; lean_object* v_state_2128_; lean_object* v_activeScopes_2129_; uint8_t v_delimitsLocal_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2146_; 
v_state_2128_ = lean_ctor_get(v_head_2117_, 0);
v_activeScopes_2129_ = lean_ctor_get(v_head_2117_, 1);
v_delimitsLocal_2130_ = lean_ctor_get_uint8(v_head_2117_, sizeof(void*)*2);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_head_2117_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2132_ = v_head_2117_;
v_isShared_2133_ = v_isSharedCheck_2146_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_activeScopes_2129_);
lean_inc(v_state_2128_);
lean_dec(v_head_2117_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2146_;
goto v_resetjp_2131_;
}
v___jp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___y_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___y_2123_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_tail_2118_);
v___x_2125_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v_scopedEntries_2115_);
lean_ctor_set(v___x_2126_, 2, v_newEntries_2116_);
return v___x_2126_;
}
}
v_resetjp_2131_:
{
uint8_t v___x_2134_; 
v___x_2134_ = l_Lean_NameSet_contains(v_activeScopes_2129_, v_namespaceName_2111_);
if (v___x_2134_ == 0)
{
lean_object* v_activeScopes_2135_; lean_object* v___x_2136_; 
lean_inc(v_newEntries_2116_);
lean_inc_ref(v_scopedEntries_2115_);
lean_dec_ref(v_s_2113_);
lean_inc(v_namespaceName_2111_);
v_activeScopes_2135_ = l_Lean_NameSet_insert(v_activeScopes_2129_, v_namespaceName_2111_);
lean_inc_ref(v_scopedEntries_2115_);
v___x_2136_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2115_, v_namespaceName_2111_);
lean_dec(v_namespaceName_2111_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v_ext_2112_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_activeScopes_2135_);
v___x_2138_ = v___x_2132_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_state_2128_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_activeScopes_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*2, v_delimitsLocal_2130_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v___y_2123_ = v___x_2138_;
goto v___jp_2122_;
}
}
else
{
lean_object* v_val_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v_val_2140_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2140_);
lean_dec_ref(v___x_2136_);
v___x_2141_ = 1;
v___x_2142_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2112_, v_val_2140_, v_state_2128_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_activeScopes_2135_);
lean_ctor_set(v___x_2132_, 0, v___x_2142_);
v___x_2144_ = v___x_2132_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_activeScopes_2135_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*2, v___x_2141_);
v___y_2123_ = v___x_2144_;
goto v___jp_2122_;
}
}
}
else
{
lean_del_object(v___x_2132_);
lean_dec(v_activeScopes_2129_);
lean_dec(v_state_2128_);
lean_del_object(v___x_2120_);
lean_dec(v_tail_2118_);
lean_dec_ref(v_ext_2112_);
lean_dec(v_namespaceName_2111_);
return v_s_2113_;
}
}
}
}
else
{
lean_dec(v_stateStack_2114_);
lean_dec_ref(v_ext_2112_);
lean_dec(v_namespaceName_2111_);
return v_s_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2148_, lean_object* v_env_2149_, lean_object* v_namespaceName_2150_){
_start:
{
lean_object* v_ext_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_ext_2151_ = lean_ctor_get(v_ext_2148_, 1);
lean_inc_ref(v_ext_2151_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2152_, 0, v_namespaceName_2150_);
lean_closure_set(v___f_2152_, 1, v_ext_2148_);
v___x_2153_ = lean_box(1);
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2151_, v_env_2149_, v___f_2152_, v___x_2153_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2156_, lean_object* v_00_u03b2_2157_, lean_object* v_00_u03c3_2158_, lean_object* v_ext_2159_, lean_object* v_env_2160_, lean_object* v_namespaceName_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2159_, v_env_2160_, v_namespaceName_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2163_, lean_object* v_00_u03c3_2164_, lean_object* v_00_u03b1_2165_, lean_object* v_ext_2166_, lean_object* v_t_2167_, lean_object* v_init_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2166_, v_t_2167_, v_init_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2170_, lean_object* v_00_u03c3_2171_, lean_object* v_00_u03b1_2172_, lean_object* v_ext_2173_, lean_object* v_inh_2174_, lean_object* v_n_2175_, lean_object* v_b_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2173_, v_inh_2174_, v_n_2175_, v_b_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2178_, lean_object* v_00_u03c3_2179_, lean_object* v_00_u03b1_2180_, lean_object* v_ext_2181_, lean_object* v_inh_2182_, lean_object* v_n_2183_, lean_object* v_b_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2178_, v_00_u03c3_2179_, v_00_u03b1_2180_, v_ext_2181_, v_inh_2182_, v_n_2183_, v_b_2184_);
lean_dec(v_inh_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2186_, lean_object* v_00_u03c3_2187_, lean_object* v_00_u03b1_2188_, lean_object* v_ext_2189_, lean_object* v_as_2190_, size_t v_sz_2191_, size_t v_i_2192_, lean_object* v_b_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2189_, v_as_2190_, v_sz_2191_, v_i_2192_, v_b_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2195_, lean_object* v_00_u03c3_2196_, lean_object* v_00_u03b1_2197_, lean_object* v_ext_2198_, lean_object* v_as_2199_, lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_b_2202_){
_start:
{
size_t v_sz_boxed_2203_; size_t v_i_boxed_2204_; lean_object* v_res_2205_; 
v_sz_boxed_2203_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2204_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2195_, v_00_u03c3_2196_, v_00_u03b1_2197_, v_ext_2198_, v_as_2199_, v_sz_boxed_2203_, v_i_boxed_2204_, v_b_2202_);
lean_dec_ref(v_as_2199_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2206_, lean_object* v_00_u03c3_2207_, lean_object* v_00_u03b1_2208_, lean_object* v_ext_2209_, lean_object* v_inh_2210_, lean_object* v_as_2211_, size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_b_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_2209_, v_inh_2210_, v_as_2211_, v_sz_2212_, v_i_2213_, v_b_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_00_u03c3_2217_, lean_object* v_00_u03b1_2218_, lean_object* v_ext_2219_, lean_object* v_inh_2220_, lean_object* v_as_2221_, lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_b_2224_){
_start:
{
size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; lean_object* v_res_2227_; 
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2216_, v_00_u03c3_2217_, v_00_u03b1_2218_, v_ext_2219_, v_inh_2220_, v_as_2221_, v_sz_boxed_2225_, v_i_boxed_2226_, v_b_2224_);
lean_dec_ref(v_as_2221_);
lean_dec(v_inh_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2228_, lean_object* v_00_u03c3_2229_, lean_object* v_00_u03b1_2230_, lean_object* v_ext_2231_, lean_object* v_as_2232_, size_t v_sz_2233_, size_t v_i_2234_, lean_object* v_b_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2231_, v_as_2232_, v_sz_2233_, v_i_2234_, v_b_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2237_, lean_object* v_00_u03c3_2238_, lean_object* v_00_u03b1_2239_, lean_object* v_ext_2240_, lean_object* v_as_2241_, lean_object* v_sz_2242_, lean_object* v_i_2243_, lean_object* v_b_2244_){
_start:
{
size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2242_);
lean_dec(v_sz_2242_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2237_, v_00_u03c3_2238_, v_00_u03b1_2239_, v_ext_2240_, v_as_2241_, v_sz_boxed_2245_, v_i_boxed_2246_, v_b_2244_);
lean_dec_ref(v_as_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2248_, lean_object* v_00_u03c3_2249_, lean_object* v_00_u03b1_2250_, lean_object* v_ext_2251_, lean_object* v_as_2252_, size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_b_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2251_, v_as_2252_, v_sz_2253_, v_i_2254_, v_b_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2257_, lean_object* v_00_u03c3_2258_, lean_object* v_00_u03b1_2259_, lean_object* v_ext_2260_, lean_object* v_as_2261_, lean_object* v_sz_2262_, lean_object* v_i_2263_, lean_object* v_b_2264_){
_start:
{
size_t v_sz_boxed_2265_; size_t v_i_boxed_2266_; lean_object* v_res_2267_; 
v_sz_boxed_2265_ = lean_unbox_usize(v_sz_2262_);
lean_dec(v_sz_2262_);
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2257_, v_00_u03c3_2258_, v_00_u03b1_2259_, v_ext_2260_, v_as_2261_, v_sz_boxed_2265_, v_i_boxed_2266_, v_b_2264_);
lean_dec_ref(v_as_2261_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2268_, lean_object* v_00_u03c3_2269_, lean_object* v_00_u03b1_2270_, lean_object* v_ext_2271_, lean_object* v_as_2272_, size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_b_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2271_, v_as_2272_, v_sz_2273_, v_i_2274_, v_b_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2277_, lean_object* v_00_u03c3_2278_, lean_object* v_00_u03b1_2279_, lean_object* v_ext_2280_, lean_object* v_as_2281_, lean_object* v_sz_2282_, lean_object* v_i_2283_, lean_object* v_b_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; lean_object* v_res_2287_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2282_);
lean_dec(v_sz_2282_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2277_, v_00_u03c3_2278_, v_00_u03b1_2279_, v_ext_2280_, v_as_2281_, v_sz_boxed_2285_, v_i_boxed_2286_, v_b_2284_);
lean_dec_ref(v_as_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2288_, lean_object* v_s_2289_){
_start:
{
lean_object* v_stateStack_2290_; 
v_stateStack_2290_ = lean_ctor_get(v_s_2289_, 0);
lean_inc(v_stateStack_2290_);
if (lean_obj_tag(v_stateStack_2290_) == 1)
{
lean_object* v_head_2291_; lean_object* v_scopedEntries_2292_; lean_object* v_newEntries_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2320_; 
v_head_2291_ = lean_ctor_get(v_stateStack_2290_, 0);
lean_inc(v_head_2291_);
v_scopedEntries_2292_ = lean_ctor_get(v_s_2289_, 1);
v_newEntries_2293_ = lean_ctor_get(v_s_2289_, 2);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_s_2289_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v_s_2289_, 0);
lean_dec(v_unused_2321_);
v___x_2295_ = v_s_2289_;
v_isShared_2296_ = v_isSharedCheck_2320_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_newEntries_2293_);
lean_inc(v_scopedEntries_2292_);
lean_dec(v_s_2289_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2320_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_tail_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2318_; 
v_tail_2297_ = lean_ctor_get(v_stateStack_2290_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_stateStack_2290_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_stateStack_2290_, 0);
lean_dec(v_unused_2319_);
v___x_2299_ = v_stateStack_2290_;
v_isShared_2300_ = v_isSharedCheck_2318_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_tail_2297_);
lean_dec(v_stateStack_2290_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2318_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_state_2301_; lean_object* v_activeScopes_2302_; uint8_t v_delimitsLocal_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2317_; 
v_state_2301_ = lean_ctor_get(v_head_2291_, 0);
v_activeScopes_2302_ = lean_ctor_get(v_head_2291_, 1);
v_delimitsLocal_2303_ = lean_ctor_get_uint8(v_head_2291_, sizeof(void*)*2);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_head_2291_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2305_ = v_head_2291_;
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_activeScopes_2302_);
lean_inc(v_state_2301_);
lean_dec(v_head_2291_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2317_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2307_ = lean_apply_1(v_f_2288_, v_state_2301_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2307_);
v___x_2309_ = v___x_2305_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_activeScopes_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2316_, sizeof(void*)*2, v_delimitsLocal_2303_);
v___x_2309_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2309_);
v___x_2311_ = v___x_2299_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_tail_2297_);
v___x_2311_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2311_);
v___x_2313_ = v___x_2295_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_scopedEntries_2292_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_newEntries_2293_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2290_);
lean_dec(v_f_2288_);
return v_s_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2322_, lean_object* v_env_2323_, lean_object* v_f_2324_){
_start:
{
lean_object* v_ext_2325_; lean_object* v_toEnvExtension_2326_; lean_object* v_asyncMode_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_ext_2325_ = lean_ctor_get(v_ext_2322_, 1);
lean_inc_ref(v_ext_2325_);
lean_dec_ref(v_ext_2322_);
v_toEnvExtension_2326_ = lean_ctor_get(v_ext_2325_, 0);
v_asyncMode_2327_ = lean_ctor_get(v_toEnvExtension_2326_, 2);
lean_inc(v_asyncMode_2327_);
v___f_2328_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2328_, 0, v_f_2324_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2325_, v_env_2323_, v___f_2328_, v_asyncMode_2327_, v___x_2329_);
lean_dec(v_asyncMode_2327_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_00_u03c3_2333_, lean_object* v_ext_2334_, lean_object* v_env_2335_, lean_object* v_f_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2334_, v_env_2335_, v_f_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2338_, lean_object* v_____s_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_apply_2(v_toPure_2338_, lean_box(0), v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2342_, lean_object* v_toPure_2343_, lean_object* v_r_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2342_);
v___x_2346_ = lean_apply_2(v_toPure_2343_, lean_box(0), v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2347_, lean_object* v_toBind_2348_, lean_object* v___f_2349_, lean_object* v_a_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_modifyEnv_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_modifyEnv_2353_ = lean_ctor_get(v_inst_2347_, 1);
lean_inc(v_modifyEnv_2353_);
lean_dec_ref(v_inst_2347_);
v___x_2354_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2354_, 0, lean_box(0));
lean_closure_set(v___x_2354_, 1, lean_box(0));
lean_closure_set(v___x_2354_, 2, lean_box(0));
lean_closure_set(v___x_2354_, 3, v_a_2350_);
v___x_2355_ = lean_apply_1(v_modifyEnv_2353_, v___x_2354_);
v___x_2356_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2355_, v___f_2349_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2357_, lean_object* v_inst_2358_, lean_object* v_toBind_2359_, lean_object* v_inst_2360_, lean_object* v___f_2361_, lean_object* v_____do__lift_2362_){
_start:
{
lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2363_ = lean_box(0);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2364_, 0, v___x_2363_);
lean_closure_set(v___f_2364_, 1, v_toPure_2357_);
lean_inc(v_toBind_2359_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2365_, 0, v_inst_2358_);
lean_closure_set(v___f_2365_, 1, v_toBind_2359_);
lean_closure_set(v___f_2365_, 2, v___f_2364_);
v_sz_2366_ = lean_array_size(v_____do__lift_2362_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2360_, v_____do__lift_2362_, v___f_2365_, v_sz_2366_, v___x_2367_, v___x_2363_);
v___x_2369_ = lean_apply_4(v_toBind_2359_, lean_box(0), lean_box(0), v___x_2368_, v___f_2361_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_scopedEnvExtensionsRef;
v___x_2371_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2371_, 0, lean_box(0));
lean_closure_set(v___x_2371_, 1, lean_box(0));
lean_closure_set(v___x_2371_, 2, v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_){
_start:
{
lean_object* v_toApplicative_2375_; lean_object* v_toBind_2376_; lean_object* v_toPure_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; 
v_toApplicative_2375_ = lean_ctor_get(v_inst_2372_, 0);
v_toBind_2376_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc(v_toBind_2376_);
v_toPure_2377_ = lean_ctor_get(v_toApplicative_2375_, 1);
lean_inc(v_toPure_2377_);
v___x_2378_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2379_ = lean_apply_2(v_inst_2374_, lean_box(0), v___x_2378_);
lean_inc(v_toPure_2377_);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2380_, 0, v_toPure_2377_);
lean_inc(v_toBind_2376_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2381_, 0, v_toPure_2377_);
lean_closure_set(v___f_2381_, 1, v_inst_2373_);
lean_closure_set(v___f_2381_, 2, v_toBind_2376_);
lean_closure_set(v___f_2381_, 3, v_inst_2372_);
lean_closure_set(v___f_2381_, 4, v___f_2380_);
v___x_2382_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v___x_2379_, v___f_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_pushScope___redArg(v_inst_2384_, v_inst_2385_, v_inst_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2388_, lean_object* v_toBind_2389_, lean_object* v___f_2390_, lean_object* v_a_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_modifyEnv_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_modifyEnv_2394_ = lean_ctor_get(v_inst_2388_, 1);
lean_inc(v_modifyEnv_2394_);
lean_dec_ref(v_inst_2388_);
v___x_2395_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2395_, 0, lean_box(0));
lean_closure_set(v___x_2395_, 1, lean_box(0));
lean_closure_set(v___x_2395_, 2, lean_box(0));
lean_closure_set(v___x_2395_, 3, v_a_2391_);
v___x_2396_ = lean_apply_1(v_modifyEnv_2394_, v___x_2395_);
v___x_2397_ = lean_apply_4(v_toBind_2389_, lean_box(0), lean_box(0), v___x_2396_, v___f_2390_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2398_, lean_object* v_inst_2399_, lean_object* v_toBind_2400_, lean_object* v_inst_2401_, lean_object* v___f_2402_, lean_object* v_____do__lift_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___f_2406_; size_t v_sz_2407_; size_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2404_ = lean_box(0);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2405_, 0, v___x_2404_);
lean_closure_set(v___f_2405_, 1, v_toPure_2398_);
lean_inc(v_toBind_2400_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2406_, 0, v_inst_2399_);
lean_closure_set(v___f_2406_, 1, v_toBind_2400_);
lean_closure_set(v___f_2406_, 2, v___f_2405_);
v_sz_2407_ = lean_array_size(v_____do__lift_2403_);
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2401_, v_____do__lift_2403_, v___f_2406_, v_sz_2407_, v___x_2408_, v___x_2404_);
v___x_2410_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2409_, v___f_2402_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_){
_start:
{
lean_object* v_toApplicative_2414_; lean_object* v_toBind_2415_; lean_object* v_toPure_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___x_2421_; 
v_toApplicative_2414_ = lean_ctor_get(v_inst_2411_, 0);
v_toBind_2415_ = lean_ctor_get(v_inst_2411_, 1);
lean_inc(v_toBind_2415_);
v_toPure_2416_ = lean_ctor_get(v_toApplicative_2414_, 1);
lean_inc(v_toPure_2416_);
v___x_2417_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2418_ = lean_apply_2(v_inst_2413_, lean_box(0), v___x_2417_);
lean_inc(v_toPure_2416_);
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2419_, 0, v_toPure_2416_);
lean_inc(v_toBind_2415_);
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2420_, 0, v_toPure_2416_);
lean_closure_set(v___f_2420_, 1, v_inst_2412_);
lean_closure_set(v___f_2420_, 2, v_toBind_2415_);
lean_closure_set(v___f_2420_, 3, v_inst_2411_);
lean_closure_set(v___f_2420_, 4, v___f_2419_);
v___x_2421_ = lean_apply_4(v_toBind_2415_, lean_box(0), lean_box(0), v___x_2418_, v___f_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_popScope___redArg(v_inst_2423_, v_inst_2424_, v_inst_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2427_, v_x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2430_, lean_object* v_toBind_2431_, lean_object* v___f_2432_, lean_object* v_a_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_modifyEnv_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_modifyEnv_2436_ = lean_ctor_get(v_inst_2430_, 1);
lean_inc(v_modifyEnv_2436_);
lean_dec_ref(v_inst_2430_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2437_, 0, v_a_2433_);
v___x_2438_ = lean_apply_1(v_modifyEnv_2436_, v___f_2437_);
v___x_2439_ = lean_apply_4(v_toBind_2431_, lean_box(0), lean_box(0), v___x_2438_, v___f_2432_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2440_, lean_object* v_inst_2441_, lean_object* v_toBind_2442_, lean_object* v_inst_2443_, lean_object* v___f_2444_, lean_object* v_____do__lift_2445_){
_start:
{
lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; size_t v_sz_2449_; size_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2446_ = lean_box(0);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
lean_closure_set(v___f_2447_, 1, v_toPure_2440_);
lean_inc(v_toBind_2442_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2448_, 0, v_inst_2441_);
lean_closure_set(v___f_2448_, 1, v_toBind_2442_);
lean_closure_set(v___f_2448_, 2, v___f_2447_);
v_sz_2449_ = lean_array_size(v_____do__lift_2445_);
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2443_, v_____do__lift_2445_, v___f_2448_, v_sz_2449_, v___x_2450_, v___x_2446_);
v___x_2452_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2451_, v___f_2444_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_){
_start:
{
lean_object* v_toApplicative_2456_; lean_object* v_toBind_2457_; lean_object* v_toPure_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; 
v_toApplicative_2456_ = lean_ctor_get(v_inst_2453_, 0);
v_toBind_2457_ = lean_ctor_get(v_inst_2453_, 1);
lean_inc(v_toBind_2457_);
v_toPure_2458_ = lean_ctor_get(v_toApplicative_2456_, 1);
lean_inc(v_toPure_2458_);
v___x_2459_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2460_ = lean_apply_2(v_inst_2455_, lean_box(0), v___x_2459_);
lean_inc(v_toPure_2458_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2461_, 0, v_toPure_2458_);
lean_inc(v_toBind_2457_);
v___f_2462_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2462_, 0, v_toPure_2458_);
lean_closure_set(v___f_2462_, 1, v_inst_2454_);
lean_closure_set(v___f_2462_, 2, v_toBind_2457_);
lean_closure_set(v___f_2462_, 3, v_inst_2453_);
lean_closure_set(v___f_2462_, 4, v___f_2461_);
v___x_2463_ = lean_apply_4(v_toBind_2457_, lean_box(0), lean_box(0), v___x_2460_, v___f_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_setDelimitsLocal___redArg(v_inst_2465_, v_inst_2466_, v_inst_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2469_, lean_object* v_namespaceName_2470_, lean_object* v_x_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2469_, v_x_2471_, v_namespaceName_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2473_, lean_object* v_namespaceName_2474_, lean_object* v_toBind_2475_, lean_object* v___f_2476_, lean_object* v_a_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_modifyEnv_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_modifyEnv_2480_ = lean_ctor_get(v_inst_2473_, 1);
lean_inc(v_modifyEnv_2480_);
lean_dec_ref(v_inst_2473_);
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2481_, 0, v_a_2477_);
lean_closure_set(v___f_2481_, 1, v_namespaceName_2474_);
v___x_2482_ = lean_apply_1(v_modifyEnv_2480_, v___f_2481_);
v___x_2483_ = lean_apply_4(v_toBind_2475_, lean_box(0), lean_box(0), v___x_2482_, v___f_2476_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2484_, lean_object* v_inst_2485_, lean_object* v_namespaceName_2486_, lean_object* v_toBind_2487_, lean_object* v_inst_2488_, lean_object* v___f_2489_, lean_object* v_____do__lift_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___f_2493_; size_t v_sz_2494_; size_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2491_ = lean_box(0);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2492_, 0, v___x_2491_);
lean_closure_set(v___f_2492_, 1, v_toPure_2484_);
lean_inc(v_toBind_2487_);
v___f_2493_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2493_, 0, v_inst_2485_);
lean_closure_set(v___f_2493_, 1, v_namespaceName_2486_);
lean_closure_set(v___f_2493_, 2, v_toBind_2487_);
lean_closure_set(v___f_2493_, 3, v___f_2492_);
v_sz_2494_ = lean_array_size(v_____do__lift_2490_);
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2488_, v_____do__lift_2490_, v___f_2493_, v_sz_2494_, v___x_2495_, v___x_2491_);
v___x_2497_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v___x_2496_, v___f_2489_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_namespaceName_2501_){
_start:
{
lean_object* v_toApplicative_2502_; lean_object* v_toBind_2503_; lean_object* v_toPure_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; 
v_toApplicative_2502_ = lean_ctor_get(v_inst_2498_, 0);
v_toBind_2503_ = lean_ctor_get(v_inst_2498_, 1);
lean_inc(v_toBind_2503_);
v_toPure_2504_ = lean_ctor_get(v_toApplicative_2502_, 1);
lean_inc(v_toPure_2504_);
v___x_2505_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2506_ = lean_apply_2(v_inst_2500_, lean_box(0), v___x_2505_);
lean_inc(v_toPure_2504_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2507_, 0, v_toPure_2504_);
lean_inc(v_toBind_2503_);
v___f_2508_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2508_, 0, v_toPure_2504_);
lean_closure_set(v___f_2508_, 1, v_inst_2499_);
lean_closure_set(v___f_2508_, 2, v_namespaceName_2501_);
lean_closure_set(v___f_2508_, 3, v_toBind_2503_);
lean_closure_set(v___f_2508_, 4, v_inst_2498_);
lean_closure_set(v___f_2508_, 5, v___f_2507_);
v___x_2509_ = lean_apply_4(v_toBind_2503_, lean_box(0), lean_box(0), v___x_2506_, v___f_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2510_, lean_object* v_inst_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_namespaceName_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_activateScoped___redArg(v_inst_2511_, v_inst_2512_, v_inst_2513_, v_namespaceName_2514_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2517_){
_start:
{
lean_inc(v___y_2517_);
return v___y_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2518_);
lean_dec(v___y_2518_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2520_, lean_object* v_a_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_a_2521_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2525_, lean_object* v_a_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2525_, v_a_2526_, v___y_2527_);
lean_dec_ref(v___y_2527_);
lean_dec(v_x_2525_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_initial_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2538_){
_start:
{
lean_object* v_name_2540_; lean_object* v_addEntry_2541_; lean_object* v_initial_2542_; lean_object* v_finalizeImport_2543_; lean_object* v_exportEntry_x3f_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_name_2540_ = lean_ctor_get(v_descr_2538_, 0);
lean_inc(v_name_2540_);
v_addEntry_2541_ = lean_ctor_get(v_descr_2538_, 1);
lean_inc(v_addEntry_2541_);
v_initial_2542_ = lean_ctor_get(v_descr_2538_, 2);
lean_inc(v_initial_2542_);
v_finalizeImport_2543_ = lean_ctor_get(v_descr_2538_, 3);
lean_inc(v_finalizeImport_2543_);
v_exportEntry_x3f_2544_ = lean_ctor_get(v_descr_2538_, 4);
lean_inc_ref(v_exportEntry_x3f_2544_);
lean_dec_ref(v_descr_2538_);
v___f_2545_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2546_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2547_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2547_, 0, v_initial_2542_);
v___x_2548_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2548_, 0, v_name_2540_);
lean_ctor_set(v___x_2548_, 1, v___f_2547_);
lean_ctor_set(v___x_2548_, 2, v___f_2546_);
lean_ctor_set(v___x_2548_, 3, v___f_2545_);
lean_ctor_set(v___x_2548_, 4, v_addEntry_2541_);
lean_ctor_set(v___x_2548_, 5, v_finalizeImport_2543_);
lean_ctor_set(v___x_2548_, 6, v_exportEntry_x3f_2544_);
v___x_2549_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2553_, lean_object* v_00_u03c3_2554_, lean_object* v_descr_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2558_, lean_object* v_00_u03c3_2559_, lean_object* v_descr_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2558_, v_00_u03c3_2559_, v_descr_2560_);
return v_res_2562_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
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
