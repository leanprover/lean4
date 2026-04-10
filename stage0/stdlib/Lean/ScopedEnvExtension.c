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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0_value),((lean_object*)&l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0_value),((lean_object*)&l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(uint8_t v_x_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v___y_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
uint8_t v_x_130__boxed_187_; lean_object* v_res_188_; 
v_x_130__boxed_187_ = lean_unbox(v_x_185_);
v_res_188_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_130__boxed_187_, v___y_186_);
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_263_; uint64_t v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1723u);
v___x_264_ = lean_uint64_of_nat(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_buckets_267_; lean_object* v___x_268_; uint64_t v___y_270_; 
v_buckets_267_ = lean_ctor_get(v_m_265_, 1);
v___x_268_ = lean_array_get_size(v_buckets_267_);
if (lean_obj_tag(v_a_266_) == 0)
{
uint64_t v___x_284_; 
v___x_284_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_270_ = v___x_284_;
goto v___jp_269_;
}
else
{
uint64_t v_hash_285_; 
v_hash_285_ = lean_ctor_get_uint64(v_a_266_, sizeof(void*)*2);
v___y_270_ = v_hash_285_;
goto v___jp_269_;
}
v___jp_269_:
{
uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v_fold_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_271_ = 32ULL;
v___x_272_ = lean_uint64_shift_right(v___y_270_, v___x_271_);
v_fold_273_ = lean_uint64_xor(v___y_270_, v___x_272_);
v___x_274_ = 16ULL;
v___x_275_ = lean_uint64_shift_right(v_fold_273_, v___x_274_);
v___x_276_ = lean_uint64_xor(v_fold_273_, v___x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = lean_usize_of_nat(v___x_268_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_sub(v___x_278_, v___x_279_);
v___x_281_ = lean_usize_land(v___x_277_, v___x_280_);
v___x_282_ = lean_array_uget_borrowed(v_buckets_267_, v___x_281_);
v___x_283_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_266_, v___x_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_m_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_289_, lean_object* v_vals_290_, lean_object* v_i_291_, lean_object* v_k_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_get_size(v_keys_289_);
v___x_294_ = lean_nat_dec_lt(v_i_291_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec(v_i_291_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v_k_x27_296_; uint8_t v___x_297_; 
v_k_x27_296_ = lean_array_fget_borrowed(v_keys_289_, v_i_291_);
v___x_297_ = lean_name_eq(v_k_292_, v_k_x27_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_291_, v___x_298_);
lean_dec(v_i_291_);
v_i_291_ = v___x_299_;
goto _start;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_array_fget_borrowed(v_vals_290_, v_i_291_);
lean_dec(v_i_291_);
lean_inc(v___x_301_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_303_, lean_object* v_vals_304_, lean_object* v_i_305_, lean_object* v_k_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_303_, v_vals_304_, v_i_305_, v_k_306_);
lean_dec(v_k_306_);
lean_dec_ref(v_vals_304_);
lean_dec_ref(v_keys_303_);
return v_res_307_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_308_; size_t v___x_309_; size_t v___x_310_; 
v___x_308_ = ((size_t)5ULL);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_shift_left(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; 
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_313_ = lean_usize_sub(v___x_312_, v___x_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_314_, size_t v_x_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v_es_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_338_; 
v_es_317_ = lean_ctor_get(v_x_314_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_338_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_338_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_es_317_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_338_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_j_325_; lean_object* v___x_326_; 
v___x_321_ = lean_box(2);
v___x_322_ = ((size_t)5ULL);
v___x_323_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_324_ = lean_usize_land(v_x_315_, v___x_323_);
v_j_325_ = lean_usize_to_nat(v___x_324_);
v___x_326_ = lean_array_get(v___x_321_, v_es_317_, v_j_325_);
lean_dec(v_j_325_);
lean_dec_ref(v_es_317_);
switch(lean_obj_tag(v___x_326_))
{
case 0:
{
lean_object* v_key_327_; lean_object* v_val_328_; uint8_t v___x_329_; 
v_key_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_key_327_);
v_val_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_val_328_);
lean_dec_ref(v___x_326_);
v___x_329_ = lean_name_eq(v_x_316_, v_key_327_);
lean_dec(v_key_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v_val_328_);
lean_del_object(v___x_319_);
v___x_330_ = lean_box(0);
return v___x_330_;
}
else
{
lean_object* v___x_332_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 1);
lean_ctor_set(v___x_319_, 0, v_val_328_);
v___x_332_ = v___x_319_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_val_328_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
case 1:
{
lean_object* v_node_334_; size_t v___x_335_; 
lean_del_object(v___x_319_);
v_node_334_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_node_334_);
lean_dec_ref(v___x_326_);
v___x_335_ = lean_usize_shift_right(v_x_315_, v___x_322_);
v_x_314_ = v_node_334_;
v_x_315_ = v___x_335_;
goto _start;
}
default: 
{
lean_object* v___x_337_; 
lean_del_object(v___x_319_);
v___x_337_ = lean_box(0);
return v___x_337_;
}
}
}
}
else
{
lean_object* v_ks_339_; lean_object* v_vs_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_ks_339_ = lean_ctor_get(v_x_314_, 0);
lean_inc_ref(v_ks_339_);
v_vs_340_ = lean_ctor_get(v_x_314_, 1);
lean_inc_ref(v_vs_340_);
lean_dec_ref(v_x_314_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_339_, v_vs_340_, v___x_341_, v_x_316_);
lean_dec_ref(v_vs_340_);
lean_dec_ref(v_ks_339_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
size_t v_x_1076__boxed_346_; lean_object* v_res_347_; 
v_x_1076__boxed_346_ = lean_unbox_usize(v_x_344_);
lean_dec(v_x_344_);
v_res_347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_343_, v_x_1076__boxed_346_, v_x_345_);
lean_dec(v_x_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint64_t v___y_351_; 
if (lean_obj_tag(v_x_349_) == 0)
{
uint64_t v___x_354_; 
v___x_354_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_351_ = v___x_354_;
goto v___jp_350_;
}
else
{
uint64_t v_hash_355_; 
v_hash_355_ = lean_ctor_get_uint64(v_x_349_, sizeof(void*)*2);
v___y_351_ = v_hash_355_;
goto v___jp_350_;
}
v___jp_350_:
{
size_t v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_uint64_to_usize(v___y_351_);
v___x_353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_348_, v___x_352_, v_x_349_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_356_, v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_stage_u2081_361_; 
v_stage_u2081_361_ = lean_ctor_get_uint8(v_x_359_, sizeof(void*)*2);
if (v_stage_u2081_361_ == 0)
{
lean_object* v_map_u2081_362_; lean_object* v_map_u2082_363_; lean_object* v___x_364_; 
v_map_u2081_362_ = lean_ctor_get(v_x_359_, 0);
lean_inc_ref(v_map_u2081_362_);
v_map_u2082_363_ = lean_ctor_get(v_x_359_, 1);
lean_inc_ref(v_map_u2082_363_);
lean_dec_ref(v_x_359_);
v___x_364_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_363_, v_x_360_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_362_, v_x_360_);
lean_dec_ref(v_map_u2081_362_);
return v___x_365_;
}
else
{
lean_dec_ref(v_map_u2081_362_);
return v___x_364_;
}
}
else
{
lean_object* v_map_u2081_366_; lean_object* v___x_367_; 
v_map_u2081_366_ = lean_ctor_get(v_x_359_, 0);
lean_inc_ref(v_map_u2081_366_);
lean_dec_ref(v_x_359_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_366_, v_x_360_);
lean_dec_ref(v_map_u2081_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_368_, v_x_369_);
lean_dec(v_x_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_371_, lean_object* v_b_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
lean_dec(v_b_372_);
lean_dec(v_a_371_);
return v_x_373_;
}
else
{
lean_object* v_key_374_; lean_object* v_value_375_; lean_object* v_tail_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v_key_374_ = lean_ctor_get(v_x_373_, 0);
v_value_375_ = lean_ctor_get(v_x_373_, 1);
v_tail_376_ = lean_ctor_get(v_x_373_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v_x_373_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_tail_376_);
lean_inc(v_value_375_);
lean_inc(v_key_374_);
lean_dec(v_x_373_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint8_t v___x_380_; 
v___x_380_ = lean_name_eq(v_key_374_, v_a_371_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_371_, v_b_372_, v_tail_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 2, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_key_374_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_value_375_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___x_386_; 
lean_dec(v_value_375_);
lean_dec(v_key_374_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v_b_372_);
lean_ctor_set(v___x_378_, 0, v_a_371_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_371_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_b_372_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_tail_376_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
return v_x_389_;
}
else
{
lean_object* v_key_391_; lean_object* v_value_392_; lean_object* v_tail_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_419_; 
v_key_391_ = lean_ctor_get(v_x_390_, 0);
v_value_392_ = lean_ctor_get(v_x_390_, 1);
v_tail_393_ = lean_ctor_get(v_x_390_, 2);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_419_ == 0)
{
v___x_395_ = v_x_390_;
v_isShared_396_ = v_isSharedCheck_419_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_tail_393_);
lean_inc(v_value_392_);
lean_inc(v_key_391_);
lean_dec(v_x_390_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_419_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; uint64_t v___y_399_; 
v___x_397_ = lean_array_get_size(v_x_389_);
if (lean_obj_tag(v_key_391_) == 0)
{
uint64_t v___x_417_; 
v___x_417_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_399_ = v___x_417_;
goto v___jp_398_;
}
else
{
uint64_t v_hash_418_; 
v_hash_418_ = lean_ctor_get_uint64(v_key_391_, sizeof(void*)*2);
v___y_399_ = v_hash_418_;
goto v___jp_398_;
}
v___jp_398_:
{
uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v_fold_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_400_ = 32ULL;
v___x_401_ = lean_uint64_shift_right(v___y_399_, v___x_400_);
v_fold_402_ = lean_uint64_xor(v___y_399_, v___x_401_);
v___x_403_ = 16ULL;
v___x_404_ = lean_uint64_shift_right(v_fold_402_, v___x_403_);
v___x_405_ = lean_uint64_xor(v_fold_402_, v___x_404_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = lean_usize_of_nat(v___x_397_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_sub(v___x_407_, v___x_408_);
v___x_410_ = lean_usize_land(v___x_406_, v___x_409_);
v___x_411_ = lean_array_uget_borrowed(v_x_389_, v___x_410_);
lean_inc(v___x_411_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 2, v___x_411_);
v___x_413_ = v___x_395_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_key_391_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_value_392_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v___x_411_);
v___x_413_ = v_reuseFailAlloc_416_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = lean_array_uset(v_x_389_, v___x_410_, v___x_413_);
v_x_389_ = v___x_414_;
v_x_390_ = v_tail_393_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_420_, lean_object* v_source_421_, lean_object* v_target_422_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_array_get_size(v_source_421_);
v___x_424_ = lean_nat_dec_lt(v_i_420_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec_ref(v_source_421_);
lean_dec(v_i_420_);
return v_target_422_;
}
else
{
lean_object* v_es_425_; lean_object* v___x_426_; lean_object* v_source_427_; lean_object* v_target_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_es_425_ = lean_array_fget(v_source_421_, v_i_420_);
v___x_426_ = lean_box(0);
v_source_427_ = lean_array_fset(v_source_421_, v_i_420_, v___x_426_);
v_target_428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_422_, v_es_425_);
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_i_420_, v___x_429_);
lean_dec(v_i_420_);
v_i_420_ = v___x_430_;
v_source_421_ = v_source_427_;
v_target_422_ = v_target_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_nbuckets_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_433_ = lean_array_get_size(v_data_432_);
v___x_434_ = lean_unsigned_to_nat(2u);
v_nbuckets_435_ = lean_nat_mul(v___x_433_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_box(0);
v___x_438_ = lean_mk_array(v_nbuckets_435_, v___x_437_);
v___x_439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_436_, v_data_432_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
else
{
lean_object* v_key_443_; lean_object* v_tail_444_; uint8_t v___x_445_; 
v_key_443_ = lean_ctor_get(v_x_441_, 0);
v_tail_444_ = lean_ctor_get(v_x_441_, 2);
v___x_445_ = lean_name_eq(v_key_443_, v_a_440_);
if (v___x_445_ == 0)
{
v_x_441_ = v_tail_444_;
goto _start;
}
else
{
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_447_, v_x_448_);
lean_dec(v_x_448_);
lean_dec(v_a_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_451_, lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v_size_454_; lean_object* v_buckets_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_501_; 
v_size_454_ = lean_ctor_get(v_m_451_, 0);
v_buckets_455_ = lean_ctor_get(v_m_451_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_m_451_);
if (v_isSharedCheck_501_ == 0)
{
v___x_457_ = v_m_451_;
v_isShared_458_ = v_isSharedCheck_501_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_buckets_455_);
lean_inc(v_size_454_);
lean_dec(v_m_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_501_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; uint64_t v___y_461_; 
v___x_459_ = lean_array_get_size(v_buckets_455_);
if (lean_obj_tag(v_a_452_) == 0)
{
uint64_t v___x_499_; 
v___x_499_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_461_ = v___x_499_;
goto v___jp_460_;
}
else
{
uint64_t v_hash_500_; 
v_hash_500_ = lean_ctor_get_uint64(v_a_452_, sizeof(void*)*2);
v___y_461_ = v_hash_500_;
goto v___jp_460_;
}
v___jp_460_:
{
uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v_fold_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v_bkt_473_; uint8_t v___x_474_; 
v___x_462_ = 32ULL;
v___x_463_ = lean_uint64_shift_right(v___y_461_, v___x_462_);
v_fold_464_ = lean_uint64_xor(v___y_461_, v___x_463_);
v___x_465_ = 16ULL;
v___x_466_ = lean_uint64_shift_right(v_fold_464_, v___x_465_);
v___x_467_ = lean_uint64_xor(v_fold_464_, v___x_466_);
v___x_468_ = lean_uint64_to_usize(v___x_467_);
v___x_469_ = lean_usize_of_nat(v___x_459_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_sub(v___x_469_, v___x_470_);
v___x_472_ = lean_usize_land(v___x_468_, v___x_471_);
v_bkt_473_ = lean_array_uget_borrowed(v_buckets_455_, v___x_472_);
v___x_474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_452_, v_bkt_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v_size_x27_476_; lean_object* v___x_477_; lean_object* v_buckets_x27_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v_size_x27_476_ = lean_nat_add(v_size_454_, v___x_475_);
lean_dec(v_size_454_);
lean_inc(v_bkt_473_);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v_a_452_);
lean_ctor_set(v___x_477_, 1, v_b_453_);
lean_ctor_set(v___x_477_, 2, v_bkt_473_);
v_buckets_x27_478_ = lean_array_uset(v_buckets_455_, v___x_472_, v___x_477_);
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_mul(v_size_x27_476_, v___x_479_);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_nat_div(v___x_480_, v___x_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_array_get_size(v_buckets_x27_478_);
v___x_484_ = lean_nat_dec_le(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v_val_485_; lean_object* v___x_487_; 
v_val_485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_478_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_val_485_);
lean_ctor_set(v___x_457_, 0, v_size_x27_476_);
v___x_487_ = v___x_457_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_val_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_buckets_x27_478_);
lean_ctor_set(v___x_457_, 0, v_size_x27_476_);
v___x_490_ = v___x_457_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_buckets_x27_478_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v_buckets_x27_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
lean_inc(v_bkt_473_);
v___x_492_ = lean_box(0);
v_buckets_x27_493_ = lean_array_uset(v_buckets_455_, v___x_472_, v___x_492_);
v___x_494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_452_, v_b_453_, v_bkt_473_);
v___x_495_ = lean_array_uset(v_buckets_x27_493_, v___x_472_, v___x_494_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_495_);
v___x_497_ = v___x_457_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_size_454_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_ks_506_; lean_object* v_vs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_531_; 
v_ks_506_ = lean_ctor_get(v_x_502_, 0);
v_vs_507_ = lean_ctor_get(v_x_502_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_509_ = v_x_502_;
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_vs_507_);
lean_inc(v_ks_506_);
lean_dec(v_x_502_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_531_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_ks_506_);
v___x_512_ = lean_nat_dec_lt(v_x_503_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_x_503_);
v___x_513_ = lean_array_push(v_ks_506_, v_x_504_);
v___x_514_ = lean_array_push(v_vs_507_, v_x_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_514_);
lean_ctor_set(v___x_509_, 0, v___x_513_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v_k_x27_518_; uint8_t v___x_519_; 
v_k_x27_518_ = lean_array_fget_borrowed(v_ks_506_, v_x_503_);
v___x_519_ = lean_name_eq(v_x_504_, v_k_x27_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; 
if (v_isShared_510_ == 0)
{
v___x_521_ = v___x_509_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_ks_506_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_vs_507_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_x_503_, v___x_522_);
lean_dec(v_x_503_);
v_x_502_ = v___x_521_;
v_x_503_ = v___x_523_;
goto _start;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = lean_array_fset(v_ks_506_, v_x_503_, v_x_504_);
v___x_527_ = lean_array_fset(v_vs_507_, v_x_503_, v_x_505_);
lean_dec(v_x_503_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_527_);
lean_ctor_set(v___x_509_, 0, v___x_526_);
v___x_529_ = v___x_509_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_532_, lean_object* v_k_533_, lean_object* v_v_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_532_, v___x_535_, v_k_533_, v_v_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_es_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v_j_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_es_543_ = lean_ctor_get(v_x_538_, 0);
v___x_544_ = ((size_t)5ULL);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_547_ = lean_usize_land(v_x_539_, v___x_546_);
v_j_548_ = lean_usize_to_nat(v___x_547_);
v___x_549_ = lean_array_get_size(v_es_543_);
v___x_550_ = lean_nat_dec_lt(v_j_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v_j_548_);
lean_dec(v_x_542_);
lean_dec(v_x_541_);
return v_x_538_;
}
else
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_587_; 
lean_inc_ref(v_es_543_);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_x_538_, 0);
lean_dec(v_unused_588_);
v___x_552_ = v_x_538_;
v_isShared_553_ = v_isSharedCheck_587_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_x_538_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_587_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_v_554_; lean_object* v___x_555_; lean_object* v_xs_x27_556_; lean_object* v___y_558_; 
v_v_554_ = lean_array_fget(v_es_543_, v_j_548_);
v___x_555_ = lean_box(0);
v_xs_x27_556_ = lean_array_fset(v_es_543_, v_j_548_, v___x_555_);
switch(lean_obj_tag(v_v_554_))
{
case 0:
{
lean_object* v_key_563_; lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
v_key_563_ = lean_ctor_get(v_v_554_, 0);
v_val_564_ = lean_ctor_get(v_v_554_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_566_ = v_v_554_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_inc(v_key_563_);
lean_dec(v_v_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint8_t v___x_568_; 
v___x_568_ = lean_name_eq(v_x_541_, v_key_563_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_del_object(v___x_566_);
v___x_569_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_563_, v_val_564_, v_x_541_, v_x_542_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___y_558_ = v___x_570_;
goto v___jp_557_;
}
else
{
lean_object* v___x_572_; 
lean_dec(v_val_564_);
lean_dec(v_key_563_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v_x_542_);
lean_ctor_set(v___x_566_, 0, v_x_541_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_x_541_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_x_542_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_558_ = v___x_572_;
goto v___jp_557_;
}
}
}
}
case 1:
{
lean_object* v_node_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_node_575_ = lean_ctor_get(v_v_554_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_v_554_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v_v_554_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_node_575_);
lean_dec(v_v_554_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_579_ = lean_usize_shift_right(v_x_539_, v___x_544_);
v___x_580_ = lean_usize_add(v_x_540_, v___x_545_);
v___x_581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_575_, v___x_579_, v___x_580_, v_x_541_, v_x_542_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v___y_558_ = v___x_583_;
goto v___jp_557_;
}
}
}
default: 
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_x_541_);
lean_ctor_set(v___x_586_, 1, v_x_542_);
v___y_558_ = v___x_586_;
goto v___jp_557_;
}
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_array_fset(v_xs_x27_556_, v_j_548_, v___y_558_);
lean_dec(v_j_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_559_);
v___x_561_ = v___x_552_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_ks_589_; lean_object* v_vs_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_610_; 
v_ks_589_ = lean_ctor_get(v_x_538_, 0);
v_vs_590_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_610_ == 0)
{
v___x_592_ = v_x_538_;
v_isShared_593_ = v_isSharedCheck_610_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_vs_590_);
lean_inc(v_ks_589_);
lean_dec(v_x_538_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_610_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_ks_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_vs_590_);
v___x_595_ = v_reuseFailAlloc_609_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v_newNode_596_; uint8_t v___y_598_; size_t v___x_604_; uint8_t v___x_605_; 
v_newNode_596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_595_, v_x_541_, v_x_542_);
v___x_604_ = ((size_t)7ULL);
v___x_605_ = lean_usize_dec_le(v___x_604_, v_x_540_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_596_);
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___y_598_ = v___x_608_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_605_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v_ks_599_; lean_object* v_vs_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_ks_599_ = lean_ctor_get(v_newNode_596_, 0);
lean_inc_ref(v_ks_599_);
v_vs_600_ = lean_ctor_get(v_newNode_596_, 1);
lean_inc_ref(v_vs_600_);
lean_dec_ref(v_newNode_596_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_540_, v_ks_599_, v_vs_600_, v___x_601_, v___x_602_);
lean_dec_ref(v_vs_600_);
lean_dec_ref(v_ks_599_);
return v___x_603_;
}
else
{
return v_newNode_596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_i_614_, lean_object* v_entries_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_keys_612_);
v___x_617_ = lean_nat_dec_lt(v_i_614_, v___x_616_);
if (v___x_617_ == 0)
{
lean_dec(v_i_614_);
return v_entries_615_;
}
else
{
lean_object* v_k_618_; lean_object* v_v_619_; uint64_t v___y_621_; 
v_k_618_ = lean_array_fget_borrowed(v_keys_612_, v_i_614_);
v_v_619_ = lean_array_fget_borrowed(v_vals_613_, v_i_614_);
if (lean_obj_tag(v_k_618_) == 0)
{
uint64_t v___x_632_; 
v___x_632_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_621_ = v___x_632_;
goto v___jp_620_;
}
else
{
uint64_t v_hash_633_; 
v_hash_633_ = lean_ctor_get_uint64(v_k_618_, sizeof(void*)*2);
v___y_621_ = v_hash_633_;
goto v___jp_620_;
}
v___jp_620_:
{
size_t v_h_622_; size_t v___x_623_; lean_object* v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; size_t v_h_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_h_622_ = lean_uint64_to_usize(v___y_621_);
v___x_623_ = ((size_t)5ULL);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_sub(v_depth_611_, v___x_625_);
v___x_627_ = lean_usize_mul(v___x_623_, v___x_626_);
v_h_628_ = lean_usize_shift_right(v_h_622_, v___x_627_);
v___x_629_ = lean_nat_add(v_i_614_, v___x_624_);
lean_dec(v_i_614_);
lean_inc(v_v_619_);
lean_inc(v_k_618_);
v___x_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_615_, v_h_628_, v_depth_611_, v_k_618_, v_v_619_);
v_i_614_ = v___x_629_;
v_entries_615_ = v___x_630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_634_, lean_object* v_keys_635_, lean_object* v_vals_636_, lean_object* v_i_637_, lean_object* v_entries_638_){
_start:
{
size_t v_depth_boxed_639_; lean_object* v_res_640_; 
v_depth_boxed_639_ = lean_unbox_usize(v_depth_634_);
lean_dec(v_depth_634_);
v_res_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_639_, v_keys_635_, v_vals_636_, v_i_637_, v_entries_638_);
lean_dec_ref(v_vals_636_);
lean_dec_ref(v_keys_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
size_t v_x_1486__boxed_646_; size_t v_x_1487__boxed_647_; lean_object* v_res_648_; 
v_x_1486__boxed_646_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_x_1487__boxed_647_ = lean_unbox_usize(v_x_643_);
lean_dec(v_x_643_);
v_res_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_641_, v_x_1486__boxed_646_, v_x_1487__boxed_647_, v_x_644_, v_x_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
uint64_t v___y_653_; 
if (lean_obj_tag(v_x_650_) == 0)
{
uint64_t v___x_657_; 
v___x_657_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_653_ = v___x_657_;
goto v___jp_652_;
}
else
{
uint64_t v_hash_658_; 
v_hash_658_ = lean_ctor_get_uint64(v_x_650_, sizeof(void*)*2);
v___y_653_ = v_hash_658_;
goto v___jp_652_;
}
v___jp_652_:
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_uint64_to_usize(v___y_653_);
v___x_655_ = ((size_t)1ULL);
v___x_656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_649_, v___x_654_, v___x_655_, v_x_650_, v_x_651_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_stage_u2081_662_; 
v_stage_u2081_662_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*2);
if (v_stage_u2081_662_ == 0)
{
lean_object* v_map_u2081_663_; lean_object* v_map_u2082_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_map_u2081_663_ = lean_ctor_get(v_x_659_, 0);
v_map_u2082_664_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v_x_659_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_map_u2082_664_);
lean_inc(v_map_u2081_663_);
lean_dec(v_x_659_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_664_, v_x_660_, v_x_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_map_u2081_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*2, v_stage_u2081_662_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_map_u2081_673_; lean_object* v_map_u2082_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_map_u2081_673_ = lean_ctor_get(v_x_659_, 0);
v_map_u2082_674_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v_x_659_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_map_u2082_674_);
lean_inc(v_map_u2081_673_);
lean_dec(v_x_659_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_673_, v_x_660_, v_x_661_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_map_u2082_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_681_, sizeof(void*)*2, v_stage_u2081_662_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(32u);
v___x_684_ = lean_mk_empty_array_with_capacity(v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = ((size_t)5ULL);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_unsigned_to_nat(32u);
v___x_689_ = lean_mk_empty_array_with_capacity(v___x_688_);
v___x_690_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_691_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
lean_ctor_set(v___x_691_, 2, v___x_687_);
lean_ctor_set(v___x_691_, 3, v___x_687_);
lean_ctor_set_usize(v___x_691_, 4, v___x_686_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_692_, lean_object* v_ns_693_, lean_object* v_b_694_){
_start:
{
lean_object* v___x_695_; 
lean_inc_ref(v_scopedEntries_692_);
v___x_695_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_692_, v_ns_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_697_ = l_Lean_PersistentArray_push___redArg(v___x_696_, v_b_694_);
v___x_698_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_692_, v_ns_693_, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_val_699_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_699_);
lean_dec_ref(v___x_695_);
v___x_700_ = l_Lean_PersistentArray_push___redArg(v_val_699_, v_b_694_);
v___x_701_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_692_, v_ns_693_, v___x_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_702_, lean_object* v_scopedEntries_703_, lean_object* v_ns_704_, lean_object* v_b_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_703_, v_ns_704_, v_b_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_708_, v_x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_711_, v_x_712_, v_x_713_);
lean_dec(v_x_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_716_, v_x_717_, v_x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_721_, v_x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_724_, v_x_725_, v_x_726_);
lean_dec(v_x_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_728_, lean_object* v_m_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_729_, v_a_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_732_, v_m_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_m_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_737_, v_x_738_, v_x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_742_, v_a_743_, v_b_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, size_t v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_747_, v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
size_t v_x_1794__boxed_755_; lean_object* v_res_756_; 
v_x_1794__boxed_755_ = lean_unbox_usize(v_x_753_);
lean_dec(v_x_753_);
v_res_756_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_751_, v_x_752_, v_x_1794__boxed_755_, v_x_754_);
lean_dec(v_x_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_757_, lean_object* v_a_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_761_, lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_761_, v_a_762_, v_x_763_);
lean_dec(v_x_763_);
lean_dec(v_a_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_765_, lean_object* v_x_766_, size_t v_x_767_, size_t v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_766_, v_x_767_, v_x_768_, v_x_769_, v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
size_t v_x_1810__boxed_778_; size_t v_x_1811__boxed_779_; lean_object* v_res_780_; 
v_x_1810__boxed_778_ = lean_unbox_usize(v_x_774_);
lean_dec(v_x_774_);
v_x_1811__boxed_779_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_res_780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_772_, v_x_773_, v_x_1810__boxed_778_, v_x_1811__boxed_779_, v_x_776_, v_x_777_);
return v_res_780_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_781_, lean_object* v_a_782_, lean_object* v_x_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_785_, lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_785_, v_a_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_a_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_790_, lean_object* v_data_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_793_, lean_object* v_a_794_, lean_object* v_b_795_, lean_object* v_x_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_794_, v_b_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_heq_801_, lean_object* v_i_802_, lean_object* v_k_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_799_, v_vals_800_, v_i_802_, v_k_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_805_, lean_object* v_keys_806_, lean_object* v_vals_807_, lean_object* v_heq_808_, lean_object* v_i_809_, lean_object* v_k_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_805_, v_keys_806_, v_vals_807_, v_heq_808_, v_i_809_, v_k_810_);
lean_dec(v_k_810_);
lean_dec_ref(v_vals_807_);
lean_dec_ref(v_keys_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_812_, lean_object* v_n_813_, lean_object* v_k_814_, lean_object* v_v_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_813_, v_k_814_, v_v_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_817_, size_t v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_818_, v_keys_819_, v_vals_820_, v_i_822_, v_entries_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_825_, lean_object* v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_entries_831_){
_start:
{
size_t v_depth_boxed_832_; lean_object* v_res_833_; 
v_depth_boxed_832_ = lean_unbox_usize(v_depth_826_);
lean_dec(v_depth_826_);
v_res_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_825_, v_depth_boxed_832_, v_keys_827_, v_vals_828_, v_heq_829_, v_i_830_, v_entries_831_);
lean_dec_ref(v_vals_828_);
lean_dec_ref(v_keys_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_834_, lean_object* v_i_835_, lean_object* v_source_836_, lean_object* v_target_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_835_, v_source_836_, v_target_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_840_, v_x_841_, v_x_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_849_, lean_object* v_as_850_, size_t v_sz_851_, size_t v_i_852_, lean_object* v_b_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_a_857_; uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_lt(v_i_852_, v_sz_851_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_descr_849_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_b_853_);
return v___x_862_;
}
else
{
lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_903_; 
v_fst_863_ = lean_ctor_get(v_b_853_, 0);
v_snd_864_ = lean_ctor_get(v_b_853_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_b_853_);
if (v_isSharedCheck_903_ == 0)
{
v___x_866_ = v_b_853_;
v_isShared_867_ = v_isSharedCheck_903_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_b_853_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_903_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_a_868_; 
v_a_868_ = lean_array_uget_borrowed(v_as_850_, v_i_852_);
if (lean_obj_tag(v_a_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_ofOLeanEntry_870_; lean_object* v_addEntry_871_; lean_object* v___x_872_; 
v_a_869_ = lean_ctor_get(v_a_868_, 0);
v_ofOLeanEntry_870_ = lean_ctor_get(v_descr_849_, 2);
v_addEntry_871_ = lean_ctor_get(v_descr_849_, 4);
lean_inc_ref(v_ofOLeanEntry_870_);
lean_inc_ref(v___y_854_);
lean_inc(v_a_869_);
lean_inc(v_fst_863_);
v___x_872_ = lean_apply_4(v_ofOLeanEntry_870_, v_fst_863_, v_a_869_, v___y_854_, lean_box(0));
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
lean_inc(v_addEntry_871_);
v___x_874_ = lean_apply_2(v_addEntry_871_, v_fst_863_, v_a_873_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_874_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_snd_864_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
v_a_857_ = v___x_876_;
goto v___jp_856_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec_ref(v_descr_849_);
v_a_878_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_872_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_872_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v_ofOLeanEntry_888_; lean_object* v___x_889_; 
v_a_886_ = lean_ctor_get(v_a_868_, 0);
v_a_887_ = lean_ctor_get(v_a_868_, 1);
v_ofOLeanEntry_888_ = lean_ctor_get(v_descr_849_, 2);
lean_inc_ref(v_ofOLeanEntry_888_);
lean_inc_ref(v___y_854_);
lean_inc(v_a_887_);
lean_inc(v_fst_863_);
v___x_889_ = lean_apply_4(v_ofOLeanEntry_888_, v_fst_863_, v_a_887_, v___y_854_, lean_box(0));
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
lean_inc(v_a_886_);
v___x_891_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_864_, v_a_886_, v_a_890_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_891_);
v___x_893_ = v___x_866_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_863_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
v_a_857_ = v___x_893_;
goto v___jp_856_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_del_object(v___x_866_);
lean_dec(v_snd_864_);
lean_dec(v_fst_863_);
lean_dec_ref(v_descr_849_);
v_a_895_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_889_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_889_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
v___jp_856_:
{
size_t v___x_858_; size_t v___x_859_; 
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_852_, v___x_858_);
v_i_852_ = v___x_859_;
v_b_853_ = v_a_857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_904_, lean_object* v_as_905_, lean_object* v_sz_906_, lean_object* v_i_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
size_t v_sz_boxed_911_; size_t v_i_boxed_912_; lean_object* v_res_913_; 
v_sz_boxed_911_ = lean_unbox_usize(v_sz_906_);
lean_dec(v_sz_906_);
v_i_boxed_912_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_904_, v_as_905_, v_sz_boxed_911_, v_i_boxed_912_, v_b_908_, v___y_909_);
lean_dec_ref(v___y_909_);
lean_dec_ref(v_as_905_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_914_, lean_object* v_as_915_, size_t v_sz_916_, size_t v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_917_, v_sz_916_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec_ref(v_descr_914_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_918_);
return v___x_922_;
}
else
{
lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_948_; 
v_fst_923_ = lean_ctor_get(v_b_918_, 0);
v_snd_924_ = lean_ctor_get(v_b_918_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_b_918_);
if (v_isSharedCheck_948_ == 0)
{
v___x_926_ = v_b_918_;
v_isShared_927_ = v_isSharedCheck_948_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_inc(v_fst_923_);
lean_dec(v_b_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_948_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_a_928_; lean_object* v___x_930_; 
v_a_928_ = lean_array_uget_borrowed(v_as_915_, v_i_917_);
if (v_isShared_927_ == 0)
{
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_923_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_924_);
v___x_930_ = v_reuseFailAlloc_947_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
size_t v_sz_931_; size_t v___x_932_; lean_object* v___x_933_; 
v_sz_931_ = lean_array_size(v_a_928_);
v___x_932_ = ((size_t)0ULL);
lean_inc_ref(v_descr_914_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_914_, v_a_928_, v_sz_931_, v___x_932_, v___x_930_, v___y_919_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_946_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v_fst_935_ = lean_ctor_get(v_a_934_, 0);
v_snd_936_ = lean_ctor_get(v_a_934_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v_a_934_);
if (v_isSharedCheck_946_ == 0)
{
v___x_938_ = v_a_934_;
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_935_);
lean_dec(v_a_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_fst_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_snd_936_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
size_t v___x_942_; size_t v___x_943_; 
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_917_, v___x_942_);
v_i_917_ = v___x_943_;
v_b_918_ = v___x_941_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_914_);
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_949_, lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_957_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_949_, v_as_950_, v_sz_boxed_956_, v_i_boxed_957_, v_b_953_, v___y_954_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_959_, lean_object* v_as_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_mkInitial_963_; lean_object* v_finalizeImport_964_; lean_object* v___x_965_; 
v_mkInitial_963_ = lean_ctor_get(v_descr_959_, 1);
v_finalizeImport_964_ = lean_ctor_get(v_descr_959_, 5);
lean_inc(v_finalizeImport_964_);
lean_inc_ref(v_mkInitial_963_);
v___x_965_ = lean_apply_1(v_mkInitial_963_, lean_box(0));
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = 1;
v___x_968_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_a_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v_sz_970_ = lean_array_size(v_as_960_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_959_, v_as_960_, v_sz_970_, v___x_971_, v___x_969_, v_a_961_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_994_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_993_; 
v_fst_977_ = lean_ctor_get(v_a_973_, 0);
v_snd_978_ = lean_ctor_get(v_a_973_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_973_);
if (v_isSharedCheck_993_ == 0)
{
v___x_980_ = v_a_973_;
v_isShared_981_ = v_isSharedCheck_993_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v_a_973_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_993_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_982_ = lean_apply_1(v_finalizeImport_964_, v_fst_977_);
v___x_983_ = l_Lean_NameSet_empty;
v___x_984_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*2, v___x_967_);
v___x_985_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 1);
lean_ctor_set(v___x_980_, 1, v___x_985_);
lean_ctor_set(v___x_980_, 0, v___x_984_);
v___x_987_ = v___x_980_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_992_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v_snd_978_);
lean_ctor_set(v___x_988_, 2, v___x_985_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_988_);
v___x_990_ = v___x_975_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_finalizeImport_964_);
v_a_995_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_972_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_972_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_finalizeImport_964_);
lean_dec_ref(v_descr_959_);
v_a_1003_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_965_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_965_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
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
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1011_, lean_object* v_as_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1011_, v_as_1012_, v_a_1013_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_as_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_00_u03c3_1018_, lean_object* v_descr_1019_, lean_object* v_as_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1019_, v_as_1020_, v_a_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_00_u03c3_1026_, lean_object* v_descr_1027_, lean_object* v_as_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1024_, v_00_u03b2_1025_, v_00_u03c3_1026_, v_descr_1027_, v_as_1028_, v_a_1029_);
lean_dec_ref(v_a_1029_);
lean_dec_ref(v_as_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03c3_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_descr_1035_, lean_object* v_as_1036_, size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1035_, v_as_1036_, v_sz_1037_, v_i_1038_, v_b_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03c3_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_descr_1046_, lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
size_t v_sz_boxed_1053_; size_t v_i_boxed_1054_; lean_object* v_res_1055_; 
v_sz_boxed_1053_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1054_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1043_, v_00_u03c3_1044_, v_00_u03b2_1045_, v_descr_1046_, v_as_1047_, v_sz_boxed_1053_, v_i_boxed_1054_, v_b_1050_, v___y_1051_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_as_1047_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03c3_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_descr_1059_, lean_object* v_as_1060_, size_t v_sz_1061_, size_t v_i_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1059_, v_as_1060_, v_sz_1061_, v_i_1062_, v_b_1063_, v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03c3_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_descr_1070_, lean_object* v_as_1071_, lean_object* v_sz_1072_, lean_object* v_i_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1067_, v_00_u03c3_1068_, v_00_u03b2_1069_, v_descr_1070_, v_as_1071_, v_sz_boxed_1077_, v_i_boxed_1078_, v_b_1074_, v___y_1075_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v_as_1071_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1080_, lean_object* v_descr_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
if (lean_obj_tag(v_a_1083_) == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_a_1082_);
lean_dec_ref(v_descr_1081_);
v___x_1085_ = l_List_reverse___redArg(v_a_1084_);
return v___x_1085_;
}
else
{
lean_object* v_head_1086_; lean_object* v_tail_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1112_; 
v_head_1086_ = lean_ctor_get(v_a_1083_, 0);
v_tail_1087_ = lean_ctor_get(v_a_1083_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_a_1083_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1089_ = v_a_1083_;
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_tail_1087_);
lean_inc(v_head_1086_);
lean_dec(v_a_1083_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___y_1092_; lean_object* v_state_1097_; lean_object* v_activeScopes_1098_; uint8_t v_delimitsLocal_1099_; uint8_t v___x_1100_; 
v_state_1097_ = lean_ctor_get(v_head_1086_, 0);
v_activeScopes_1098_ = lean_ctor_get(v_head_1086_, 1);
v_delimitsLocal_1099_ = lean_ctor_get_uint8(v_head_1086_, sizeof(void*)*2);
v___x_1100_ = l_Lean_NameSet_contains(v_activeScopes_1098_, v_a_1080_);
if (v___x_1100_ == 0)
{
v___y_1092_ = v_head_1086_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
lean_inc(v_activeScopes_1098_);
lean_inc(v_state_1097_);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_head_1086_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1110_ = lean_ctor_get(v_head_1086_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_head_1086_, 0);
lean_dec(v_unused_1111_);
v___x_1102_ = v_head_1086_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_head_1086_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_addEntry_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v_addEntry_1104_ = lean_ctor_get(v_descr_1081_, 4);
lean_inc(v_addEntry_1104_);
lean_inc(v_a_1082_);
v___x_1105_ = lean_apply_2(v_addEntry_1104_, v_state_1097_, v_a_1082_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_activeScopes_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*2, v_delimitsLocal_1099_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v___y_1092_ = v___x_1107_;
goto v___jp_1091_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_a_1084_);
lean_ctor_set(v___x_1089_, 0, v___y_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___y_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1084_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_a_1083_ = v_tail_1087_;
v_a_1084_ = v___x_1094_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1113_, lean_object* v_descr_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1113_, v_descr_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_object* v___x_1123_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_descr_1119_);
v___x_1123_ = l_List_reverse___redArg(v_a_1122_);
return v___x_1123_;
}
else
{
lean_object* v_head_1124_; lean_object* v_tail_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1145_; 
v_head_1124_ = lean_ctor_get(v_a_1121_, 0);
v_tail_1125_ = lean_ctor_get(v_a_1121_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1127_ = v_a_1121_;
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_tail_1125_);
lean_inc(v_head_1124_);
lean_dec(v_a_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_addEntry_1129_; lean_object* v_state_1130_; lean_object* v_activeScopes_1131_; uint8_t v_delimitsLocal_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_addEntry_1129_ = lean_ctor_get(v_descr_1119_, 4);
v_state_1130_ = lean_ctor_get(v_head_1124_, 0);
v_activeScopes_1131_ = lean_ctor_get(v_head_1124_, 1);
v_delimitsLocal_1132_ = lean_ctor_get_uint8(v_head_1124_, sizeof(void*)*2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_head_1124_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_head_1124_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_activeScopes_1131_);
lean_inc(v_state_1130_);
lean_dec(v_head_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_inc(v_addEntry_1129_);
lean_inc(v_a_1120_);
v___x_1136_ = lean_apply_2(v_addEntry_1129_, v_state_1130_, v_a_1120_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_activeScopes_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*2, v_delimitsLocal_1132_);
v___x_1138_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v_a_1122_);
lean_ctor_set(v___x_1127_, 0, v___x_1138_);
v___x_1140_ = v___x_1127_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_a_1122_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v_a_1121_ = v_tail_1125_;
v_a_1122_ = v___x_1140_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1146_, lean_object* v_s_1147_, lean_object* v_e_1148_){
_start:
{
if (lean_obj_tag(v_e_1148_) == 0)
{
lean_object* v_stateStack_1149_; lean_object* v_scopedEntries_1150_; lean_object* v_newEntries_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1171_; 
v_stateStack_1149_ = lean_ctor_get(v_s_1147_, 0);
v_scopedEntries_1150_ = lean_ctor_get(v_s_1147_, 1);
v_newEntries_1151_ = lean_ctor_get(v_s_1147_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_s_1147_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1153_ = v_s_1147_;
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_newEntries_1151_);
lean_inc(v_scopedEntries_1150_);
lean_inc(v_stateStack_1149_);
lean_dec(v_s_1147_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1170_; 
v_a_1155_ = lean_ctor_get(v_e_1148_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_e_1148_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1157_ = v_e_1148_;
v_isShared_1158_ = v_isSharedCheck_1170_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v_e_1148_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1170_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_toOLeanEntry_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v_toOLeanEntry_1159_ = lean_ctor_get(v_descr_1146_, 3);
lean_inc(v_toOLeanEntry_1159_);
v___x_1160_ = lean_box(0);
lean_inc(v_a_1155_);
v___x_1161_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1146_, v_a_1155_, v_stateStack_1149_, v___x_1160_);
v___x_1162_ = lean_apply_1(v_toOLeanEntry_1159_, v_a_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1162_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_newEntries_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 2, v___x_1165_);
lean_ctor_set(v___x_1153_, 0, v___x_1161_);
v___x_1167_ = v___x_1153_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_scopedEntries_1150_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1172_; lean_object* v_scopedEntries_1173_; lean_object* v_newEntries_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1196_; 
v_stateStack_1172_ = lean_ctor_get(v_s_1147_, 0);
v_scopedEntries_1173_ = lean_ctor_get(v_s_1147_, 1);
v_newEntries_1174_ = lean_ctor_get(v_s_1147_, 2);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_s_1147_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1176_ = v_s_1147_;
v_isShared_1177_ = v_isSharedCheck_1196_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_newEntries_1174_);
lean_inc(v_scopedEntries_1173_);
lean_inc(v_stateStack_1172_);
lean_dec(v_s_1147_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1196_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1195_; 
v_a_1178_ = lean_ctor_get(v_e_1148_, 0);
v_a_1179_ = lean_ctor_get(v_e_1148_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_e_1148_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1181_ = v_e_1148_;
v_isShared_1182_ = v_isSharedCheck_1195_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_dec(v_e_1148_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1195_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_toOLeanEntry_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v_toOLeanEntry_1183_ = lean_ctor_get(v_descr_1146_, 3);
lean_inc(v_toOLeanEntry_1183_);
v___x_1184_ = lean_box(0);
lean_inc_n(v_a_1179_, 2);
v___x_1185_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1178_, v_descr_1146_, v_a_1179_, v_stateStack_1172_, v___x_1184_);
lean_inc(v_a_1178_);
v___x_1186_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1173_, v_a_1178_, v_a_1179_);
v___x_1187_ = lean_apply_1(v_toOLeanEntry_1183_, v_a_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1187_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_newEntries_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 2, v___x_1190_);
lean_ctor_set(v___x_1176_, 1, v___x_1186_);
lean_ctor_set(v___x_1176_, 0, v___x_1185_);
v___x_1192_ = v___x_1176_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_00_u03c3_1199_, lean_object* v_descr_1200_, lean_object* v_s_1201_, lean_object* v_e_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1200_, v_s_1201_, v_e_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_00_u03b1_1206_, lean_object* v_descr_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1212_, lean_object* v_a_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_00_u03b1_1215_, lean_object* v_descr_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1213_, v_descr_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1221_, lean_object* v_a_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_00_u03b1_1224_, lean_object* v_descr_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1221_, v_a_1222_, v_00_u03b2_1223_, v_00_u03b1_1224_, v_descr_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1222_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(lean_object* v_descr_1230_, uint8_t v_level_1231_, lean_object* v_as_1232_, size_t v_i_1233_, size_t v_stop_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v___y_1237_; uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_eq(v_i_1233_, v_stop_1234_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_array_uget(v_as_1232_, v_i_1233_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_exportEntry_x3f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_exportEntry_x3f_1247_ = lean_ctor_get(v_descr_1230_, 6);
v___x_1248_ = lean_box(v_level_1231_);
lean_inc_ref(v_exportEntry_x3f_1247_);
v___x_1249_ = lean_apply_2(v_exportEntry_x3f_1247_, v___x_1248_, v_a_1243_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_del_object(v___x_1245_);
v___y_1237_ = v_b_1235_;
goto v___jp_1236_;
}
else
{
lean_object* v_val_1250_; lean_object* v___x_1252_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref(v___x_1249_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_val_1250_);
v___x_1252_ = v___x_1245_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_val_1250_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_array_push(v_b_1235_, v___x_1252_);
v___y_1237_ = v___x_1253_;
goto v___jp_1236_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_a_1256_ = lean_ctor_get(v___x_1242_, 0);
v_a_1257_ = lean_ctor_get(v___x_1242_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v___x_1242_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_inc(v_a_1256_);
lean_dec(v___x_1242_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_exportEntry_x3f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_exportEntry_x3f_1261_ = lean_ctor_get(v_descr_1230_, 6);
v___x_1262_ = lean_box(v_level_1231_);
lean_inc_ref(v_exportEntry_x3f_1261_);
v___x_1263_ = lean_apply_2(v_exportEntry_x3f_1261_, v___x_1262_, v_a_1257_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_del_object(v___x_1259_);
lean_dec(v_a_1256_);
v___y_1237_ = v_b_1235_;
goto v___jp_1236_;
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1266_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref(v___x_1263_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_val_1264_);
v___x_1266_ = v___x_1259_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1256_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_val_1264_);
v___x_1266_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_array_push(v_b_1235_, v___x_1266_);
v___y_1237_ = v___x_1267_;
goto v___jp_1236_;
}
}
}
}
}
else
{
lean_dec_ref(v_descr_1230_);
return v_b_1235_;
}
v___jp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1233_, v___x_1238_);
v_i_1233_ = v___x_1239_;
v_b_1235_ = v___y_1237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg___boxed(lean_object* v_descr_1270_, lean_object* v_level_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_){
_start:
{
uint8_t v_level_boxed_1276_; size_t v_i_boxed_1277_; size_t v_stop_boxed_1278_; lean_object* v_res_1279_; 
v_level_boxed_1276_ = lean_unbox(v_level_1271_);
v_i_boxed_1277_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1278_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1270_, v_level_boxed_1276_, v_as_1272_, v_i_boxed_1277_, v_stop_boxed_1278_, v_b_1275_);
lean_dec_ref(v_as_1272_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1282_, uint8_t v_level_1283_, lean_object* v_as_1284_, lean_object* v_start_1285_, lean_object* v_stop_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
v___x_1288_ = lean_nat_dec_lt(v_start_1285_, v_stop_1286_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_descr_1282_);
return v___x_1287_;
}
else
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = lean_array_get_size(v_as_1284_);
v___x_1290_ = lean_nat_dec_le(v_stop_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_lt(v_start_1285_, v___x_1289_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v_descr_1282_);
return v___x_1287_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_usize_of_nat(v_start_1285_);
v___x_1293_ = lean_usize_of_nat(v___x_1289_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1282_, v_level_1283_, v_as_1284_, v___x_1292_, v___x_1293_, v___x_1287_);
return v___x_1294_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = lean_usize_of_nat(v_start_1285_);
v___x_1296_ = lean_usize_of_nat(v_stop_1286_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1282_, v_level_1283_, v_as_1284_, v___x_1295_, v___x_1296_, v___x_1287_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1298_, lean_object* v_level_1299_, lean_object* v_as_1300_, lean_object* v_start_1301_, lean_object* v_stop_1302_){
_start:
{
uint8_t v_level_boxed_1303_; lean_object* v_res_1304_; 
v_level_boxed_1303_ = lean_unbox(v_level_1299_);
v_res_1304_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1298_, v_level_boxed_1303_, v_as_1300_, v_start_1301_, v_stop_1302_);
lean_dec(v_stop_1302_);
lean_dec(v_start_1301_);
lean_dec_ref(v_as_1300_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(lean_object* v_s_1305_, lean_object* v_descr_1306_, uint8_t v_level_1307_){
_start:
{
lean_object* v_newEntries_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_newEntries_1308_ = lean_ctor_get(v_s_1305_, 2);
lean_inc(v_newEntries_1308_);
lean_dec_ref(v_s_1305_);
v___x_1309_ = lean_array_mk(v_newEntries_1308_);
v___x_1310_ = l_Array_reverse___redArg(v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v___x_1310_);
v___x_1313_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1306_, v_level_1307_, v___x_1310_, v___x_1311_, v___x_1312_);
lean_dec_ref(v___x_1310_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0___boxed(lean_object* v_s_1314_, lean_object* v_descr_1315_, lean_object* v_level_1316_){
_start:
{
uint8_t v_level_boxed_1317_; lean_object* v_res_1318_; 
v_level_boxed_1317_ = lean_unbox(v_level_1316_);
v_res_1318_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(v_s_1314_, v_descr_1315_, v_level_boxed_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1319_, lean_object* v_s_1320_){
_start:
{
uint8_t v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1321_ = 0;
lean_inc_ref_n(v_descr_1319_, 2);
lean_inc_ref_n(v_s_1320_, 2);
v___x_1322_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(v_s_1320_, v_descr_1319_, v___x_1321_);
v___x_1323_ = 1;
v___x_1324_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(v_s_1320_, v_descr_1319_, v___x_1323_);
v___x_1325_ = 2;
v___x_1326_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___lam__0(v_s_1320_, v_descr_1319_, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1322_);
lean_ctor_set(v___x_1327_, 1, v___x_1324_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_00_u03c3_1330_, lean_object* v_descr_1331_, lean_object* v_s_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1331_, v_s_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_00_u03c3_1336_, lean_object* v_descr_1337_, uint8_t v_level_1338_, lean_object* v_as_1339_, lean_object* v_start_1340_, lean_object* v_stop_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1337_, v_level_1338_, v_as_1339_, v_start_1340_, v_stop_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_00_u03c3_1345_, lean_object* v_descr_1346_, lean_object* v_level_1347_, lean_object* v_as_1348_, lean_object* v_start_1349_, lean_object* v_stop_1350_){
_start:
{
uint8_t v_level_boxed_1351_; lean_object* v_res_1352_; 
v_level_boxed_1351_ = lean_unbox(v_level_1347_);
v_res_1352_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1343_, v_00_u03b2_1344_, v_00_u03c3_1345_, v_descr_1346_, v_level_boxed_1351_, v_as_1348_, v_start_1349_, v_stop_1350_);
lean_dec(v_stop_1350_);
lean_dec(v_start_1349_);
lean_dec_ref(v_as_1348_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_00_u03c3_1355_, lean_object* v_descr_1356_, uint8_t v_level_1357_, lean_object* v_as_1358_, size_t v_i_1359_, size_t v_stop_1360_, lean_object* v_b_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___redArg(v_descr_1356_, v_level_1357_, v_as_1358_, v_i_1359_, v_stop_1360_, v_b_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_00_u03b2_1364_, lean_object* v_00_u03c3_1365_, lean_object* v_descr_1366_, lean_object* v_level_1367_, lean_object* v_as_1368_, lean_object* v_i_1369_, lean_object* v_stop_1370_, lean_object* v_b_1371_){
_start:
{
uint8_t v_level_boxed_1372_; size_t v_i_boxed_1373_; size_t v_stop_boxed_1374_; lean_object* v_res_1375_; 
v_level_boxed_1372_ = lean_unbox(v_level_1367_);
v_i_boxed_1373_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_stop_boxed_1374_ = lean_unbox_usize(v_stop_1370_);
lean_dec(v_stop_1370_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(v_00_u03b1_1363_, v_00_u03b2_1364_, v_00_u03c3_1365_, v_descr_1366_, v_level_boxed_1372_, v_as_1368_, v_i_boxed_1373_, v_stop_boxed_1374_, v_b_1371_);
lean_dec_ref(v_as_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1381_, v___y_1382_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_x_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1385_, lean_object* v_x_1386_){
_start:
{
lean_inc_ref(v_s_1385_);
return v_s_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1387_, v_x_1388_);
lean_dec_ref(v_x_1388_);
lean_dec_ref(v_s_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1395_, v_x_1396_);
lean_dec_ref(v_x_1396_);
lean_dec_ref(v_x_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1400_);
lean_dec_ref(v_x_1400_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___f_1407_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1408_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1409_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1410_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1413_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___x_1411_);
lean_ctor_set(v___x_1413_, 2, v___f_1410_);
lean_ctor_set(v___x_1413_, 3, v___f_1409_);
lean_ctor_set(v___x_1413_, 4, v___f_1408_);
lean_ctor_set(v___x_1413_, 5, v___f_1407_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1414_){
_start:
{
lean_object* v___f_1415_; lean_object* v___f_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___f_1415_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1416_, 0, v_inst_1414_);
v___f_1417_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1418_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1421_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1422_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1419_);
lean_ctor_set(v___x_1422_, 1, v___x_1420_);
lean_ctor_set(v___x_1422_, 2, v___f_1415_);
lean_ctor_set(v___x_1422_, 3, v___f_1416_);
lean_ctor_set(v___x_1422_, 4, v___f_1417_);
lean_ctor_set(v___x_1422_, 5, v___x_1421_);
lean_ctor_set(v___x_1422_, 6, v___f_1418_);
v___x_1423_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_00_u03c3_1427_, lean_object* v_inst_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1432_, lean_object* v_inst_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1433_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1441_ = lean_st_mk_ref(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_descr_1445_, lean_object* v_x_1446_, lean_object* v_s_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1445_, v_s_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_descr_1449_, lean_object* v_x_1450_, lean_object* v_s_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_descr_1449_, v_x_1450_, v_s_1451_);
lean_dec_ref(v_x_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1456_){
_start:
{
lean_object* v_newEntries_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_newEntries_1457_ = lean_ctor_get(v_s_1456_, 2);
v___x_1458_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1459_ = l_List_lengthTR___redArg(v_newEntries_1457_);
v___x_1460_ = l_Nat_reprFast(v___x_1459_);
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1458_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1463_);
lean_dec_ref(v_s_1463_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object* v_x_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(v_x_1467_);
lean_dec_ref(v_x_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1471_){
_start:
{
lean_object* v_name_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_name_1473_ = lean_ctor_get(v_descr_1471_, 0);
lean_inc_ref_n(v_descr_1471_, 4);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1474_, 0, v_descr_1471_);
v___f_1475_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1476_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
v___x_1477_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1477_, 0, lean_box(0));
lean_closure_set(v___x_1477_, 1, lean_box(0));
lean_closure_set(v___x_1477_, 2, lean_box(0));
lean_closure_set(v___x_1477_, 3, v_descr_1471_);
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1478_, 0, lean_box(0));
lean_closure_set(v___x_1478_, 1, lean_box(0));
lean_closure_set(v___x_1478_, 2, lean_box(0));
lean_closure_set(v___x_1478_, 3, v_descr_1471_);
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1479_, 0, lean_box(0));
lean_closure_set(v___x_1479_, 1, lean_box(0));
lean_closure_set(v___x_1479_, 2, lean_box(0));
lean_closure_set(v___x_1479_, 3, v_descr_1471_);
v___x_1480_ = lean_box(2);
v___x_1481_ = lean_box(0);
lean_inc(v_name_1473_);
v___x_1482_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1482_, 0, v_name_1473_);
lean_ctor_set(v___x_1482_, 1, v___x_1477_);
lean_ctor_set(v___x_1482_, 2, v___x_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1479_);
lean_ctor_set(v___x_1482_, 4, v___f_1474_);
lean_ctor_set(v___x_1482_, 5, v___f_1475_);
lean_ctor_set(v___x_1482_, 6, v___x_1480_);
lean_ctor_set(v___x_1482_, 7, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___f_1476_);
v___x_1484_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1497_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1497_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1497_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1489_ = l_Lean_scopedEnvExtensionsRef;
v___x_1490_ = lean_st_ref_take(v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_descr_1471_);
lean_ctor_set(v___x_1491_, 1, v_a_1485_);
lean_inc_ref(v___x_1491_);
v___x_1492_ = lean_array_push(v___x_1490_, v___x_1491_);
v___x_1493_ = lean_st_ref_set(v___x_1489_, v___x_1492_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1491_);
v___x_1495_ = v___x_1487_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1491_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_descr_1471_);
v_a_1498_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1484_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1484_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_00_u03c3_1511_, lean_object* v_descr_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_00_u03b2_1516_, lean_object* v_00_u03c3_1517_, lean_object* v_descr_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1515_, v_00_u03b2_1516_, v_00_u03c3_1517_, v_descr_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1521_){
_start:
{
lean_object* v_stateStack_1522_; 
v_stateStack_1522_ = lean_ctor_get(v_s_1521_, 0);
if (lean_obj_tag(v_stateStack_1522_) == 0)
{
return v_s_1521_;
}
else
{
lean_object* v_head_1523_; lean_object* v_scopedEntries_1524_; lean_object* v_newEntries_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1543_; 
lean_inc_ref(v_stateStack_1522_);
v_head_1523_ = lean_ctor_get(v_stateStack_1522_, 0);
lean_inc(v_head_1523_);
v_scopedEntries_1524_ = lean_ctor_get(v_s_1521_, 1);
v_newEntries_1525_ = lean_ctor_get(v_s_1521_, 2);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_s_1521_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_s_1521_, 0);
lean_dec(v_unused_1544_);
v___x_1527_ = v_s_1521_;
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_newEntries_1525_);
lean_inc(v_scopedEntries_1524_);
lean_dec(v_s_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_state_1529_; lean_object* v_activeScopes_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1542_; 
v_state_1529_ = lean_ctor_get(v_head_1523_, 0);
v_activeScopes_1530_ = lean_ctor_get(v_head_1523_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_head_1523_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1532_ = v_head_1523_;
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_activeScopes_1530_);
lean_inc(v_state_1529_);
lean_dec(v_head_1523_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = 1;
if (v_isShared_1533_ == 0)
{
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_state_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_activeScopes_1530_);
v___x_1536_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*2, v___x_1534_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v_stateStack_1522_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1537_);
v___x_1539_ = v___x_1527_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_scopedEntries_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_newEntries_1525_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1546_, lean_object* v_env_1547_){
_start:
{
lean_object* v_ext_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_ext_1548_ = lean_ctor_get(v_ext_1546_, 1);
lean_inc_ref(v_ext_1548_);
lean_dec_ref(v_ext_1546_);
v___f_1549_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1550_ = lean_box(1);
v___x_1551_ = lean_box(0);
v___x_1552_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1548_, v_env_1547_, v___f_1549_, v___x_1550_, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1553_, lean_object* v_00_u03b2_1554_, lean_object* v_00_u03c3_1555_, lean_object* v_ext_1556_, lean_object* v_env_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1556_, v_env_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1559_){
_start:
{
lean_object* v_stateStack_1560_; 
v_stateStack_1560_ = lean_ctor_get(v_s_1559_, 0);
if (lean_obj_tag(v_stateStack_1560_) == 1)
{
lean_object* v_tail_1561_; 
v_tail_1561_ = lean_ctor_get(v_stateStack_1560_, 1);
if (lean_obj_tag(v_tail_1561_) == 1)
{
lean_object* v_scopedEntries_1562_; lean_object* v_newEntries_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_inc_ref(v_tail_1561_);
v_scopedEntries_1562_ = lean_ctor_get(v_s_1559_, 1);
v_newEntries_1563_ = lean_ctor_get(v_s_1559_, 2);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_s_1559_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_s_1559_, 0);
lean_dec(v_unused_1571_);
v___x_1565_ = v_s_1559_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_newEntries_1563_);
lean_inc(v_scopedEntries_1562_);
lean_dec(v_s_1559_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_tail_1561_);
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_tail_1561_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_scopedEntries_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_newEntries_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
return v_s_1559_;
}
}
else
{
return v_s_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1573_, lean_object* v_env_1574_){
_start:
{
lean_object* v_ext_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_ext_1575_ = lean_ctor_get(v_ext_1573_, 1);
lean_inc_ref(v_ext_1575_);
lean_dec_ref(v_ext_1573_);
v___f_1576_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1577_ = lean_box(1);
v___x_1578_ = lean_box(0);
v___x_1579_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1575_, v_env_1574_, v___f_1576_, v___x_1577_, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_00_u03c3_1582_, lean_object* v_ext_1583_, lean_object* v_env_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1583_, v_env_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_s_1586_){
_start:
{
lean_object* v_stateStack_1587_; 
v_stateStack_1587_ = lean_ctor_get(v_s_1586_, 0);
lean_inc(v_stateStack_1587_);
if (lean_obj_tag(v_stateStack_1587_) == 0)
{
return v_s_1586_;
}
else
{
lean_object* v_head_1588_; lean_object* v_scopedEntries_1589_; lean_object* v_newEntries_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1616_; 
v_head_1588_ = lean_ctor_get(v_stateStack_1587_, 0);
lean_inc(v_head_1588_);
v_scopedEntries_1589_ = lean_ctor_get(v_s_1586_, 1);
v_newEntries_1590_ = lean_ctor_get(v_s_1586_, 2);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_s_1586_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v_s_1586_, 0);
lean_dec(v_unused_1617_);
v___x_1592_ = v_s_1586_;
v_isShared_1593_ = v_isSharedCheck_1616_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_newEntries_1590_);
lean_inc(v_scopedEntries_1589_);
lean_dec(v_s_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1616_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_tail_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1614_; 
v_tail_1594_ = lean_ctor_get(v_stateStack_1587_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_stateStack_1587_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_stateStack_1587_, 0);
lean_dec(v_unused_1615_);
v___x_1596_ = v_stateStack_1587_;
v_isShared_1597_ = v_isSharedCheck_1614_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_tail_1594_);
lean_dec(v_stateStack_1587_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1614_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_state_1598_; lean_object* v_activeScopes_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1613_; 
v_state_1598_ = lean_ctor_get(v_head_1588_, 0);
v_activeScopes_1599_ = lean_ctor_get(v_head_1588_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_head_1588_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1601_ = v_head_1588_;
v_isShared_1602_ = v_isSharedCheck_1613_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_activeScopes_1599_);
lean_inc(v_state_1598_);
lean_dec(v_head_1588_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1613_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
uint8_t v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = 0;
if (v_isShared_1602_ == 0)
{
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_state_1598_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_activeScopes_1599_);
v___x_1605_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*2, v___x_1603_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1605_);
v___x_1607_ = v___x_1596_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_tail_1594_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1607_);
v___x_1609_ = v___x_1592_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_scopedEntries_1589_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_newEntries_1590_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1619_, lean_object* v_env_1620_){
_start:
{
lean_object* v_ext_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_ext_1621_ = lean_ctor_get(v_ext_1619_, 1);
lean_inc_ref(v_ext_1621_);
lean_dec_ref(v_ext_1619_);
v___f_1622_ = ((lean_object*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0));
v___x_1623_ = lean_box(1);
v___x_1624_ = lean_box(0);
v___x_1625_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1621_, v_env_1620_, v___f_1622_, v___x_1623_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_00_u03c3_1628_, lean_object* v_ext_1629_, lean_object* v_env_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1629_, v_env_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1632_, lean_object* v_env_1633_, lean_object* v_b_1634_){
_start:
{
lean_object* v_ext_1635_; lean_object* v_toEnvExtension_1636_; lean_object* v_asyncMode_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_ext_1635_ = lean_ctor_get(v_ext_1632_, 1);
lean_inc_ref(v_ext_1635_);
lean_dec_ref(v_ext_1632_);
v_toEnvExtension_1636_ = lean_ctor_get(v_ext_1635_, 0);
v_asyncMode_1637_ = lean_ctor_get(v_toEnvExtension_1636_, 2);
lean_inc(v_asyncMode_1637_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_b_1634_);
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1635_, v_env_1633_, v___x_1638_, v_asyncMode_1637_, v___x_1639_);
lean_dec(v_asyncMode_1637_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_00_u03c3_1643_, lean_object* v_ext_1644_, lean_object* v_env_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1644_, v_env_1645_, v_b_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1648_, lean_object* v_env_1649_, lean_object* v_namespaceName_1650_, lean_object* v_b_1651_){
_start:
{
lean_object* v_ext_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1663_; 
v_ext_1652_ = lean_ctor_get(v_ext_1648_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_ext_1648_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v_ext_1648_, 0);
lean_dec(v_unused_1664_);
v___x_1654_ = v_ext_1648_;
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_ext_1652_);
lean_dec(v_ext_1648_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_toEnvExtension_1656_; lean_object* v_asyncMode_1657_; lean_object* v___x_1659_; 
v_toEnvExtension_1656_ = lean_ctor_get(v_ext_1652_, 0);
v_asyncMode_1657_ = lean_ctor_get(v_toEnvExtension_1656_, 2);
lean_inc(v_asyncMode_1657_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 1);
lean_ctor_set(v___x_1654_, 1, v_b_1651_);
lean_ctor_set(v___x_1654_, 0, v_namespaceName_1650_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_namespaceName_1650_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_b_1651_);
v___x_1659_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1652_, v_env_1649_, v___x_1659_, v_asyncMode_1657_, v___x_1660_);
lean_dec(v_asyncMode_1657_);
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_00_u03c3_1667_, lean_object* v_ext_1668_, lean_object* v_env_1669_, lean_object* v_namespaceName_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1668_, v_env_1669_, v_namespaceName_1670_, v_b_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1673_, lean_object* v_states_1674_, lean_object* v_b_1675_){
_start:
{
if (lean_obj_tag(v_states_1674_) == 0)
{
lean_dec(v_b_1675_);
lean_dec_ref(v_ext_1673_);
return v_states_1674_;
}
else
{
lean_object* v_descr_1676_; lean_object* v_head_1677_; lean_object* v_tail_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1701_; 
v_descr_1676_ = lean_ctor_get(v_ext_1673_, 0);
v_head_1677_ = lean_ctor_get(v_states_1674_, 0);
v_tail_1678_ = lean_ctor_get(v_states_1674_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_states_1674_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1680_ = v_states_1674_;
v_isShared_1681_ = v_isSharedCheck_1701_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_tail_1678_);
lean_inc(v_head_1677_);
lean_dec(v_states_1674_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1701_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_addEntry_1682_; lean_object* v_state_1683_; lean_object* v_activeScopes_1684_; uint8_t v_delimitsLocal_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1700_; 
v_addEntry_1682_ = lean_ctor_get(v_descr_1676_, 4);
v_state_1683_ = lean_ctor_get(v_head_1677_, 0);
v_activeScopes_1684_ = lean_ctor_get(v_head_1677_, 1);
v_delimitsLocal_1685_ = lean_ctor_get_uint8(v_head_1677_, sizeof(void*)*2);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_head_1677_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1687_ = v_head_1677_;
v_isShared_1688_ = v_isSharedCheck_1700_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_activeScopes_1684_);
lean_inc(v_state_1683_);
lean_dec(v_head_1677_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1700_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v_top_1691_; 
lean_inc(v_addEntry_1682_);
lean_inc(v_b_1675_);
v___x_1689_ = lean_apply_2(v_addEntry_1682_, v_state_1683_, v_b_1675_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1689_);
v_top_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_activeScopes_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*2, v_delimitsLocal_1685_);
v_top_1691_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
if (v_delimitsLocal_1685_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = l_Lean_stateStackModify___redArg(v_ext_1673_, v_tail_1678_, v_b_1675_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1692_);
lean_ctor_set(v___x_1680_, 0, v_top_1691_);
v___x_1694_ = v___x_1680_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_top_1691_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v___x_1697_; 
lean_dec(v_b_1675_);
lean_dec_ref(v_ext_1673_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_top_1691_);
v___x_1697_ = v___x_1680_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_top_1691_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_tail_1678_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_00_u03c3_1704_, lean_object* v_ext_1705_, lean_object* v_states_1706_, lean_object* v_b_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_stateStackModify___redArg(v_ext_1705_, v_states_1706_, v_b_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1709_, lean_object* v_b_1710_, lean_object* v_s_1711_){
_start:
{
lean_object* v_stateStack_1712_; lean_object* v_scopedEntries_1713_; lean_object* v_newEntries_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
v_stateStack_1712_ = lean_ctor_get(v_s_1711_, 0);
v_scopedEntries_1713_ = lean_ctor_get(v_s_1711_, 1);
v_newEntries_1714_ = lean_ctor_get(v_s_1711_, 2);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_s_1711_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v_s_1711_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_newEntries_1714_);
lean_inc(v_scopedEntries_1713_);
lean_inc(v_stateStack_1712_);
lean_dec(v_s_1711_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = l_Lean_stateStackModify___redArg(v_ext_1709_, v_stateStack_1712_, v_b_1710_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_scopedEntries_1713_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_newEntries_1714_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1723_, lean_object* v_env_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v_ext_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_ext_1726_ = lean_ctor_get(v_ext_1723_, 1);
lean_inc_ref(v_ext_1726_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1727_, 0, v_ext_1723_);
lean_closure_set(v___f_1727_, 1, v_b_1725_);
v___x_1728_ = lean_box(1);
v___x_1729_ = lean_box(0);
v___x_1730_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1726_, v_env_1724_, v___f_1727_, v___x_1728_, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_00_u03c3_1733_, lean_object* v_ext_1734_, lean_object* v_env_1735_, lean_object* v_b_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1734_, v_env_1735_, v_b_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1738_, lean_object* v_ext_1739_, lean_object* v_b_1740_, uint8_t v_kind_1741_, lean_object* v_namespaceName_1742_){
_start:
{
switch(v_kind_1741_)
{
case 0:
{
lean_object* v___x_1743_; 
lean_dec(v_namespaceName_1742_);
v___x_1743_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1739_, v_env_1738_, v_b_1740_);
return v___x_1743_;
}
case 1:
{
lean_object* v___x_1744_; 
lean_dec(v_namespaceName_1742_);
v___x_1744_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1739_, v_env_1738_, v_b_1740_);
return v___x_1744_;
}
default: 
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1739_, v_env_1738_, v_namespaceName_1742_, v_b_1740_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1746_, lean_object* v_ext_1747_, lean_object* v_b_1748_, lean_object* v_kind_1749_, lean_object* v_namespaceName_1750_){
_start:
{
uint8_t v_kind_boxed_1751_; lean_object* v_res_1752_; 
v_kind_boxed_1751_ = lean_unbox(v_kind_1749_);
v_res_1752_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1746_, v_ext_1747_, v_b_1748_, v_kind_boxed_1751_, v_namespaceName_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_00_u03c3_1755_, lean_object* v_env_1756_, lean_object* v_ext_1757_, lean_object* v_b_1758_, uint8_t v_kind_1759_, lean_object* v_namespaceName_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1756_, v_ext_1757_, v_b_1758_, v_kind_1759_, v_namespaceName_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_00_u03c3_1764_, lean_object* v_env_1765_, lean_object* v_ext_1766_, lean_object* v_b_1767_, lean_object* v_kind_1768_, lean_object* v_namespaceName_1769_){
_start:
{
uint8_t v_kind_boxed_1770_; lean_object* v_res_1771_; 
v_kind_boxed_1770_ = lean_unbox(v_kind_1768_);
v_res_1771_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1762_, v_00_u03b2_1763_, v_00_u03c3_1764_, v_env_1765_, v_ext_1766_, v_b_1767_, v_kind_boxed_1770_, v_namespaceName_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1772_, lean_object* v_b_1773_, uint8_t v_kind_1774_, lean_object* v_ns_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1776_, v_ext_1772_, v_b_1773_, v_kind_1774_, v_ns_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1778_, lean_object* v_b_1779_, lean_object* v_kind_1780_, lean_object* v_ns_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v_kind_boxed_1783_; lean_object* v_res_1784_; 
v_kind_boxed_1783_ = lean_unbox(v_kind_1780_);
v_res_1784_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1778_, v_b_1779_, v_kind_boxed_1783_, v_ns_1781_, v_x_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1785_, lean_object* v_ext_1786_, lean_object* v_b_1787_, uint8_t v_kind_1788_, lean_object* v_ns_1789_){
_start:
{
lean_object* v_modifyEnv_1790_; lean_object* v___x_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; 
v_modifyEnv_1790_ = lean_ctor_get(v_inst_1785_, 1);
lean_inc(v_modifyEnv_1790_);
lean_dec_ref(v_inst_1785_);
v___x_1791_ = lean_box(v_kind_1788_);
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1792_, 0, v_ext_1786_);
lean_closure_set(v___f_1792_, 1, v_b_1787_);
lean_closure_set(v___f_1792_, 2, v___x_1791_);
lean_closure_set(v___f_1792_, 3, v_ns_1789_);
v___x_1793_ = lean_apply_1(v_modifyEnv_1790_, v___f_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1794_, lean_object* v_ext_1795_, lean_object* v_b_1796_, lean_object* v_kind_1797_, lean_object* v_ns_1798_){
_start:
{
uint8_t v_kind_boxed_1799_; lean_object* v_res_1800_; 
v_kind_boxed_1799_ = lean_unbox(v_kind_1797_);
v_res_1800_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1794_, v_ext_1795_, v_b_1796_, v_kind_boxed_1799_, v_ns_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_ext_1804_, lean_object* v_b_1805_, uint8_t v_kind_1806_){
_start:
{
lean_object* v_toBind_1807_; lean_object* v_getCurrNamespace_1808_; lean_object* v___x_1809_; lean_object* v___f_1810_; lean_object* v___x_1811_; 
v_toBind_1807_ = lean_ctor_get(v_inst_1801_, 1);
lean_inc(v_toBind_1807_);
lean_dec_ref(v_inst_1801_);
v_getCurrNamespace_1808_ = lean_ctor_get(v_inst_1802_, 0);
lean_inc(v_getCurrNamespace_1808_);
lean_dec_ref(v_inst_1802_);
v___x_1809_ = lean_box(v_kind_1806_);
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1810_, 0, v_inst_1803_);
lean_closure_set(v___f_1810_, 1, v_ext_1804_);
lean_closure_set(v___f_1810_, 2, v_b_1805_);
lean_closure_set(v___f_1810_, 3, v___x_1809_);
v___x_1811_ = lean_apply_4(v_toBind_1807_, lean_box(0), lean_box(0), v_getCurrNamespace_1808_, v___f_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_ext_1815_, lean_object* v_b_1816_, lean_object* v_kind_1817_){
_start:
{
uint8_t v_kind_boxed_1818_; lean_object* v_res_1819_; 
v_kind_boxed_1818_ = lean_unbox(v_kind_1817_);
v_res_1819_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1812_, v_inst_1813_, v_inst_1814_, v_ext_1815_, v_b_1816_, v_kind_boxed_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1820_, lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_00_u03c3_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_ext_1827_, lean_object* v_b_1828_, uint8_t v_kind_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1824_, v_inst_1825_, v_inst_1826_, v_ext_1827_, v_b_1828_, v_kind_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1831_, lean_object* v_00_u03b1_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_00_u03c3_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_ext_1838_, lean_object* v_b_1839_, lean_object* v_kind_1840_){
_start:
{
uint8_t v_kind_boxed_1841_; lean_object* v_res_1842_; 
v_kind_boxed_1841_ = lean_unbox(v_kind_1840_);
v_res_1842_ = l_Lean_ScopedEnvExtension_add(v_m_1831_, v_00_u03b1_1832_, v_00_u03b2_1833_, v_00_u03c3_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_ext_1838_, v_b_1839_, v_kind_boxed_1841_);
return v_res_1842_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1846_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1847_ = lean_unsigned_to_nat(16u);
v___x_1848_ = lean_unsigned_to_nat(193u);
v___x_1849_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1850_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1851_ = l_mkPanicMessageWithDecl(v___x_1850_, v___x_1849_, v___x_1848_, v___x_1847_, v___x_1846_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1852_, lean_object* v_ext_1853_, lean_object* v_env_1854_, lean_object* v_asyncMode_1855_){
_start:
{
lean_object* v_ext_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_stateStack_1860_; 
v_ext_1856_ = lean_ctor_get(v_ext_1853_, 1);
v___x_1857_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1858_ = lean_box(0);
v___x_1859_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1857_, v_ext_1856_, v_env_1854_, v_asyncMode_1855_, v___x_1858_);
v_stateStack_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_stateStack_1860_);
lean_dec(v___x_1859_);
if (lean_obj_tag(v_stateStack_1860_) == 1)
{
lean_object* v_head_1861_; lean_object* v_state_1862_; 
v_head_1861_ = lean_ctor_get(v_stateStack_1860_, 0);
lean_inc(v_head_1861_);
lean_dec_ref(v_stateStack_1860_);
v_state_1862_ = lean_ctor_get(v_head_1861_, 0);
lean_inc(v_state_1862_);
lean_dec(v_head_1861_);
return v_state_1862_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v_stateStack_1860_);
v___x_1863_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1864_ = l_panic___redArg(v_inst_1852_, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1865_, lean_object* v_ext_1866_, lean_object* v_env_1867_, lean_object* v_asyncMode_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1865_, v_ext_1866_, v_env_1867_, v_asyncMode_1868_);
lean_dec(v_asyncMode_1868_);
lean_dec_ref(v_ext_1866_);
lean_dec(v_inst_1865_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1870_, lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_inst_1873_, lean_object* v_ext_1874_, lean_object* v_env_1875_, lean_object* v_asyncMode_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1873_, v_ext_1874_, v_env_1875_, v_asyncMode_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1878_, lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_inst_1881_, lean_object* v_ext_1882_, lean_object* v_env_1883_, lean_object* v_asyncMode_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1878_, v_00_u03b1_1879_, v_00_u03b2_1880_, v_inst_1881_, v_ext_1882_, v_env_1883_, v_asyncMode_1884_);
lean_dec(v_asyncMode_1884_);
lean_dec_ref(v_ext_1882_);
lean_dec(v_inst_1881_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1886_, lean_object* v_as_1887_, size_t v_sz_1888_, size_t v_i_1889_, lean_object* v_b_1890_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_usize_dec_lt(v_i_1889_, v_sz_1888_);
if (v___x_1891_ == 0)
{
lean_dec_ref(v_ext_1886_);
return v_b_1890_;
}
else
{
lean_object* v_descr_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1907_; 
v_descr_1892_ = lean_ctor_get(v_ext_1886_, 0);
v_snd_1893_ = lean_ctor_get(v_b_1890_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_b_1890_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v_b_1890_, 0);
lean_dec(v_unused_1908_);
v___x_1895_ = v_b_1890_;
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_dec(v_b_1890_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_addEntry_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v_state_1900_; lean_object* v___x_1902_; 
v_addEntry_1897_ = lean_ctor_get(v_descr_1892_, 4);
v___x_1898_ = lean_box(0);
v_a_1899_ = lean_array_uget_borrowed(v_as_1887_, v_i_1889_);
lean_inc(v_addEntry_1897_);
lean_inc(v_a_1899_);
v_state_1900_ = lean_apply_2(v_addEntry_1897_, v_snd_1893_, v_a_1899_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v_state_1900_);
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1902_ = v___x_1895_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_state_1900_);
v___x_1902_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
size_t v___x_1903_; size_t v___x_1904_; 
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1889_, v___x_1903_);
v_i_1889_ = v___x_1904_;
v_b_1890_ = v___x_1902_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1909_, lean_object* v_as_1910_, lean_object* v_sz_1911_, lean_object* v_i_1912_, lean_object* v_b_1913_){
_start:
{
size_t v_sz_boxed_1914_; size_t v_i_boxed_1915_; lean_object* v_res_1916_; 
v_sz_boxed_1914_ = lean_unbox_usize(v_sz_1911_);
lean_dec(v_sz_1911_);
v_i_boxed_1915_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1909_, v_as_1910_, v_sz_boxed_1914_, v_i_boxed_1915_, v_b_1913_);
lean_dec_ref(v_as_1910_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1917_, lean_object* v_as_1918_, size_t v_sz_1919_, size_t v_i_1920_, lean_object* v_b_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_lt(v_i_1920_, v_sz_1919_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_ext_1917_);
return v_b_1921_;
}
else
{
lean_object* v_descr_1923_; lean_object* v_snd_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1938_; 
v_descr_1923_ = lean_ctor_get(v_ext_1917_, 0);
v_snd_1924_ = lean_ctor_get(v_b_1921_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_b_1921_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_b_1921_, 0);
lean_dec(v_unused_1939_);
v___x_1926_ = v_b_1921_;
v_isShared_1927_ = v_isSharedCheck_1938_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_snd_1924_);
lean_dec(v_b_1921_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1938_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_addEntry_1928_; lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v_state_1931_; lean_object* v___x_1933_; 
v_addEntry_1928_ = lean_ctor_get(v_descr_1923_, 4);
v___x_1929_ = lean_box(0);
v_a_1930_ = lean_array_uget_borrowed(v_as_1918_, v_i_1920_);
lean_inc(v_addEntry_1928_);
lean_inc(v_a_1930_);
v_state_1931_ = lean_apply_2(v_addEntry_1928_, v_snd_1924_, v_a_1930_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v_state_1931_);
lean_ctor_set(v___x_1926_, 0, v___x_1929_);
v___x_1933_ = v___x_1926_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_state_1931_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1920_, v___x_1934_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1917_, v_as_1918_, v_sz_1919_, v___x_1935_, v___x_1933_);
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1940_, lean_object* v_as_1941_, lean_object* v_sz_1942_, lean_object* v_i_1943_, lean_object* v_b_1944_){
_start:
{
size_t v_sz_boxed_1945_; size_t v_i_boxed_1946_; lean_object* v_res_1947_; 
v_sz_boxed_1945_ = lean_unbox_usize(v_sz_1942_);
lean_dec(v_sz_1942_);
v_i_boxed_1946_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_res_1947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1940_, v_as_1941_, v_sz_boxed_1945_, v_i_boxed_1946_, v_b_1944_);
lean_dec_ref(v_as_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1948_, lean_object* v_ext_1949_, lean_object* v_n_1950_, lean_object* v_b_1951_){
_start:
{
if (lean_obj_tag(v_n_1950_) == 0)
{
lean_object* v_cs_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1967_; 
v_cs_1952_ = lean_ctor_get(v_n_1950_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_n_1950_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1954_ = v_n_1950_;
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_cs_1952_);
lean_dec(v_n_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v_fst_1961_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_b_1951_);
v_sz_1958_ = lean_array_size(v_cs_1952_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1948_, v_ext_1949_, v_cs_1952_, v_sz_1958_, v___x_1959_, v___x_1957_);
lean_dec_ref(v_cs_1952_);
v_fst_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_fst_1961_);
if (lean_obj_tag(v_fst_1961_) == 0)
{
lean_object* v_snd_1962_; lean_object* v___x_1964_; 
v_snd_1962_ = lean_ctor_get(v___x_1960_, 1);
lean_inc(v_snd_1962_);
lean_dec_ref(v___x_1960_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
lean_ctor_set(v___x_1954_, 0, v_snd_1962_);
v___x_1964_ = v___x_1954_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_snd_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v_val_1966_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1954_);
v_val_1966_ = lean_ctor_get(v_fst_1961_, 0);
lean_inc(v_val_1966_);
lean_dec_ref(v_fst_1961_);
return v_val_1966_;
}
}
}
else
{
lean_object* v_vs_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1983_; 
v_vs_1968_ = lean_ctor_get(v_n_1950_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_n_1950_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1970_ = v_n_1950_;
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_vs_1968_);
lean_dec(v_n_1950_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; size_t v_sz_1974_; size_t v___x_1975_; lean_object* v___x_1976_; lean_object* v_fst_1977_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v_b_1951_);
v_sz_1974_ = lean_array_size(v_vs_1968_);
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1949_, v_vs_1968_, v_sz_1974_, v___x_1975_, v___x_1973_);
lean_dec_ref(v_vs_1968_);
v_fst_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_fst_1977_);
if (lean_obj_tag(v_fst_1977_) == 0)
{
lean_object* v_snd_1978_; lean_object* v___x_1980_; 
v_snd_1978_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_snd_1978_);
lean_dec_ref(v___x_1976_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_snd_1978_);
v___x_1980_ = v___x_1970_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_snd_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v_val_1982_; 
lean_dec_ref(v___x_1976_);
lean_del_object(v___x_1970_);
v_val_1982_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_val_1982_);
lean_dec_ref(v_fst_1977_);
return v_val_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_1984_, lean_object* v_ext_1985_, lean_object* v_as_1986_, size_t v_sz_1987_, size_t v_i_1988_, lean_object* v_b_1989_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v_ext_1985_);
return v_b_1989_;
}
else
{
lean_object* v_snd_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2009_; 
v_snd_1991_ = lean_ctor_get(v_b_1989_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_b_1989_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_b_1989_, 0);
lean_dec(v_unused_2010_);
v___x_1993_ = v_b_1989_;
v_isShared_1994_ = v_isSharedCheck_2009_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_snd_1991_);
lean_dec(v_b_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2009_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_a_1995_; lean_object* v___x_1996_; 
v_a_1995_ = lean_array_uget_borrowed(v_as_1986_, v_i_1988_);
lean_inc(v_snd_1991_);
lean_inc(v_a_1995_);
lean_inc_ref(v_ext_1985_);
v___x_1996_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_1984_, v_ext_1985_, v_a_1995_, v_snd_1991_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec_ref(v_ext_1985_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1997_);
v___x_1999_ = v___x_1993_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_snd_1991_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_dec(v_snd_1991_);
v_a_2001_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_1996_);
v___x_2002_ = lean_box(0);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v_a_2001_);
lean_ctor_set(v___x_1993_, 0, v___x_2002_);
v___x_2004_ = v___x_1993_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_2001_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
size_t v___x_2005_; size_t v___x_2006_; 
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1988_, v___x_2005_);
v_i_1988_ = v___x_2006_;
v_b_1989_ = v___x_2004_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2011_, lean_object* v_ext_2012_, lean_object* v_as_2013_, lean_object* v_sz_2014_, lean_object* v_i_2015_, lean_object* v_b_2016_){
_start:
{
size_t v_sz_boxed_2017_; size_t v_i_boxed_2018_; lean_object* v_res_2019_; 
v_sz_boxed_2017_ = lean_unbox_usize(v_sz_2014_);
lean_dec(v_sz_2014_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2015_);
lean_dec(v_i_2015_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2011_, v_ext_2012_, v_as_2013_, v_sz_boxed_2017_, v_i_boxed_2018_, v_b_2016_);
lean_dec_ref(v_as_2013_);
lean_dec(v_init_2011_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2020_, lean_object* v_ext_2021_, lean_object* v_n_2022_, lean_object* v_b_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2020_, v_ext_2021_, v_n_2022_, v_b_2023_);
lean_dec(v_init_2020_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2025_, lean_object* v_as_2026_, size_t v_sz_2027_, size_t v_i_2028_, lean_object* v_b_2029_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = lean_usize_dec_lt(v_i_2028_, v_sz_2027_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v_ext_2025_);
return v_b_2029_;
}
else
{
lean_object* v_descr_2031_; lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2046_; 
v_descr_2031_ = lean_ctor_get(v_ext_2025_, 0);
v_snd_2032_ = lean_ctor_get(v_b_2029_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_b_2029_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_b_2029_, 0);
lean_dec(v_unused_2047_);
v___x_2034_ = v_b_2029_;
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_dec(v_b_2029_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2046_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_addEntry_2036_; lean_object* v___x_2037_; lean_object* v_a_2038_; lean_object* v_state_2039_; lean_object* v___x_2041_; 
v_addEntry_2036_ = lean_ctor_get(v_descr_2031_, 4);
v___x_2037_ = lean_box(0);
v_a_2038_ = lean_array_uget_borrowed(v_as_2026_, v_i_2028_);
lean_inc(v_addEntry_2036_);
lean_inc(v_a_2038_);
v_state_2039_ = lean_apply_2(v_addEntry_2036_, v_snd_2032_, v_a_2038_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_state_2039_);
lean_ctor_set(v___x_2034_, 0, v___x_2037_);
v___x_2041_ = v___x_2034_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_state_2039_);
v___x_2041_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
size_t v___x_2042_; size_t v___x_2043_; 
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_add(v_i_2028_, v___x_2042_);
v_i_2028_ = v___x_2043_;
v_b_2029_ = v___x_2041_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_){
_start:
{
size_t v_sz_boxed_2053_; size_t v_i_boxed_2054_; lean_object* v_res_2055_; 
v_sz_boxed_2053_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2054_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2048_, v_as_2049_, v_sz_boxed_2053_, v_i_boxed_2054_, v_b_2052_);
lean_dec_ref(v_as_2049_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_){
_start:
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_usize_dec_lt(v_i_2059_, v_sz_2058_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v_ext_2056_);
return v_b_2060_;
}
else
{
lean_object* v_descr_2062_; lean_object* v_snd_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2077_; 
v_descr_2062_ = lean_ctor_get(v_ext_2056_, 0);
v_snd_2063_ = lean_ctor_get(v_b_2060_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_b_2060_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_b_2060_, 0);
lean_dec(v_unused_2078_);
v___x_2065_ = v_b_2060_;
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_snd_2063_);
lean_dec(v_b_2060_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_addEntry_2067_; lean_object* v___x_2068_; lean_object* v_a_2069_; lean_object* v_state_2070_; lean_object* v___x_2072_; 
v_addEntry_2067_ = lean_ctor_get(v_descr_2062_, 4);
v___x_2068_ = lean_box(0);
v_a_2069_ = lean_array_uget_borrowed(v_as_2057_, v_i_2059_);
lean_inc(v_addEntry_2067_);
lean_inc(v_a_2069_);
v_state_2070_ = lean_apply_2(v_addEntry_2067_, v_snd_2063_, v_a_2069_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v_state_2070_);
lean_ctor_set(v___x_2065_, 0, v___x_2068_);
v___x_2072_ = v___x_2065_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_state_2070_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_add(v_i_2059_, v___x_2073_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2056_, v_as_2057_, v_sz_2058_, v___x_2074_, v___x_2072_);
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2079_, lean_object* v_as_2080_, lean_object* v_sz_2081_, lean_object* v_i_2082_, lean_object* v_b_2083_){
_start:
{
size_t v_sz_boxed_2084_; size_t v_i_boxed_2085_; lean_object* v_res_2086_; 
v_sz_boxed_2084_ = lean_unbox_usize(v_sz_2081_);
lean_dec(v_sz_2081_);
v_i_boxed_2085_ = lean_unbox_usize(v_i_2082_);
lean_dec(v_i_2082_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2079_, v_as_2080_, v_sz_boxed_2084_, v_i_boxed_2085_, v_b_2083_);
lean_dec_ref(v_as_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2087_, lean_object* v_t_2088_, lean_object* v_init_2089_){
_start:
{
lean_object* v_root_2090_; lean_object* v_tail_2091_; lean_object* v___x_2092_; 
v_root_2090_ = lean_ctor_get(v_t_2088_, 0);
lean_inc_ref(v_root_2090_);
v_tail_2091_ = lean_ctor_get(v_t_2088_, 1);
lean_inc_ref(v_tail_2091_);
lean_dec_ref(v_t_2088_);
lean_inc_ref(v_ext_2087_);
lean_inc(v_init_2089_);
v___x_2092_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2089_, v_ext_2087_, v_root_2090_, v_init_2089_);
lean_dec(v_init_2089_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
lean_dec_ref(v_tail_2091_);
lean_dec_ref(v_ext_2087_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
return v_a_2093_;
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v_fst_2100_; 
v_a_2094_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2092_);
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v_a_2094_);
v_sz_2097_ = lean_array_size(v_tail_2091_);
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2087_, v_tail_2091_, v_sz_2097_, v___x_2098_, v___x_2096_);
lean_dec_ref(v_tail_2091_);
v_fst_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_fst_2100_);
if (lean_obj_tag(v_fst_2100_) == 0)
{
lean_object* v_snd_2101_; 
v_snd_2101_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_snd_2101_);
lean_dec_ref(v___x_2099_);
return v_snd_2101_;
}
else
{
lean_object* v_val_2102_; 
lean_dec_ref(v___x_2099_);
v_val_2102_ = lean_ctor_get(v_fst_2100_, 0);
lean_inc(v_val_2102_);
lean_dec_ref(v_fst_2100_);
return v_val_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2103_, lean_object* v_ext_2104_, lean_object* v_s_2105_){
_start:
{
lean_object* v_stateStack_2106_; 
v_stateStack_2106_ = lean_ctor_get(v_s_2105_, 0);
lean_inc(v_stateStack_2106_);
if (lean_obj_tag(v_stateStack_2106_) == 1)
{
lean_object* v_scopedEntries_2107_; lean_object* v_newEntries_2108_; lean_object* v_head_2109_; lean_object* v_tail_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2139_; 
v_scopedEntries_2107_ = lean_ctor_get(v_s_2105_, 1);
v_newEntries_2108_ = lean_ctor_get(v_s_2105_, 2);
v_head_2109_ = lean_ctor_get(v_stateStack_2106_, 0);
v_tail_2110_ = lean_ctor_get(v_stateStack_2106_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_stateStack_2106_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2112_ = v_stateStack_2106_;
v_isShared_2113_ = v_isSharedCheck_2139_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_tail_2110_);
lean_inc(v_head_2109_);
lean_dec(v_stateStack_2106_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2139_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___y_2115_; lean_object* v_state_2120_; lean_object* v_activeScopes_2121_; uint8_t v_delimitsLocal_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2138_; 
v_state_2120_ = lean_ctor_get(v_head_2109_, 0);
v_activeScopes_2121_ = lean_ctor_get(v_head_2109_, 1);
v_delimitsLocal_2122_ = lean_ctor_get_uint8(v_head_2109_, sizeof(void*)*2);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_head_2109_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2124_ = v_head_2109_;
v_isShared_2125_ = v_isSharedCheck_2138_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_activeScopes_2121_);
lean_inc(v_state_2120_);
lean_dec(v_head_2109_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2138_;
goto v_resetjp_2123_;
}
v___jp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___y_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___y_2115_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_tail_2110_);
v___x_2117_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_scopedEntries_2107_);
lean_ctor_set(v___x_2118_, 2, v_newEntries_2108_);
return v___x_2118_;
}
}
v_resetjp_2123_:
{
uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_NameSet_contains(v_activeScopes_2121_, v_namespaceName_2103_);
if (v___x_2126_ == 0)
{
lean_object* v_activeScopes_2127_; lean_object* v___x_2128_; 
lean_inc(v_newEntries_2108_);
lean_inc_ref_n(v_scopedEntries_2107_, 2);
lean_dec_ref(v_s_2105_);
lean_inc(v_namespaceName_2103_);
v_activeScopes_2127_ = l_Lean_NameSet_insert(v_activeScopes_2121_, v_namespaceName_2103_);
v___x_2128_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2107_, v_namespaceName_2103_);
lean_dec(v_namespaceName_2103_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2130_; 
lean_dec_ref(v_ext_2104_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_activeScopes_2127_);
v___x_2130_ = v___x_2124_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_state_2120_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_activeScopes_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2131_, sizeof(void*)*2, v_delimitsLocal_2122_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v___y_2115_ = v___x_2130_;
goto v___jp_2114_;
}
}
else
{
lean_object* v_val_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v_val_2132_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_val_2132_);
lean_dec_ref(v___x_2128_);
v___x_2133_ = 1;
v___x_2134_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2104_, v_val_2132_, v_state_2120_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_activeScopes_2127_);
lean_ctor_set(v___x_2124_, 0, v___x_2134_);
v___x_2136_ = v___x_2124_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_activeScopes_2127_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*2, v___x_2133_);
v___y_2115_ = v___x_2136_;
goto v___jp_2114_;
}
}
}
else
{
lean_del_object(v___x_2124_);
lean_dec(v_activeScopes_2121_);
lean_dec(v_state_2120_);
lean_del_object(v___x_2112_);
lean_dec(v_tail_2110_);
lean_dec_ref(v_ext_2104_);
lean_dec(v_namespaceName_2103_);
return v_s_2105_;
}
}
}
}
else
{
lean_dec(v_stateStack_2106_);
lean_dec_ref(v_ext_2104_);
lean_dec(v_namespaceName_2103_);
return v_s_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2140_, lean_object* v_env_2141_, lean_object* v_namespaceName_2142_){
_start:
{
lean_object* v_ext_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_ext_2143_ = lean_ctor_get(v_ext_2140_, 1);
lean_inc_ref(v_ext_2143_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2144_, 0, v_namespaceName_2142_);
lean_closure_set(v___f_2144_, 1, v_ext_2140_);
v___x_2145_ = lean_box(1);
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2143_, v_env_2141_, v___f_2144_, v___x_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2148_, lean_object* v_00_u03b2_2149_, lean_object* v_00_u03c3_2150_, lean_object* v_ext_2151_, lean_object* v_env_2152_, lean_object* v_namespaceName_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2151_, v_env_2152_, v_namespaceName_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2155_, lean_object* v_00_u03c3_2156_, lean_object* v_00_u03b1_2157_, lean_object* v_ext_2158_, lean_object* v_t_2159_, lean_object* v_init_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2158_, v_t_2159_, v_init_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2162_, lean_object* v_00_u03c3_2163_, lean_object* v_init_2164_, lean_object* v_00_u03b1_2165_, lean_object* v_ext_2166_, lean_object* v_n_2167_, lean_object* v_b_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2164_, v_ext_2166_, v_n_2167_, v_b_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2170_, lean_object* v_00_u03c3_2171_, lean_object* v_init_2172_, lean_object* v_00_u03b1_2173_, lean_object* v_ext_2174_, lean_object* v_n_2175_, lean_object* v_b_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2170_, v_00_u03c3_2171_, v_init_2172_, v_00_u03b1_2173_, v_ext_2174_, v_n_2175_, v_b_2176_);
lean_dec(v_init_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2178_, lean_object* v_00_u03c3_2179_, lean_object* v_00_u03b1_2180_, lean_object* v_ext_2181_, lean_object* v_as_2182_, size_t v_sz_2183_, size_t v_i_2184_, lean_object* v_b_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2181_, v_as_2182_, v_sz_2183_, v_i_2184_, v_b_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_00_u03c3_2188_, lean_object* v_00_u03b1_2189_, lean_object* v_ext_2190_, lean_object* v_as_2191_, lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_b_2194_){
_start:
{
size_t v_sz_boxed_2195_; size_t v_i_boxed_2196_; lean_object* v_res_2197_; 
v_sz_boxed_2195_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2196_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2187_, v_00_u03c3_2188_, v_00_u03b1_2189_, v_ext_2190_, v_as_2191_, v_sz_boxed_2195_, v_i_boxed_2196_, v_b_2194_);
lean_dec_ref(v_as_2191_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2198_, lean_object* v_00_u03c3_2199_, lean_object* v_init_2200_, lean_object* v_00_u03b1_2201_, lean_object* v_ext_2202_, lean_object* v_as_2203_, size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_b_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2200_, v_ext_2202_, v_as_2203_, v_sz_2204_, v_i_2205_, v_b_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2208_, lean_object* v_00_u03c3_2209_, lean_object* v_init_2210_, lean_object* v_00_u03b1_2211_, lean_object* v_ext_2212_, lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_){
_start:
{
size_t v_sz_boxed_2217_; size_t v_i_boxed_2218_; lean_object* v_res_2219_; 
v_sz_boxed_2217_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2208_, v_00_u03c3_2209_, v_init_2210_, v_00_u03b1_2211_, v_ext_2212_, v_as_2213_, v_sz_boxed_2217_, v_i_boxed_2218_, v_b_2216_);
lean_dec_ref(v_as_2213_);
lean_dec(v_init_2210_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2220_, lean_object* v_00_u03c3_2221_, lean_object* v_00_u03b1_2222_, lean_object* v_ext_2223_, lean_object* v_as_2224_, size_t v_sz_2225_, size_t v_i_2226_, lean_object* v_b_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2223_, v_as_2224_, v_sz_2225_, v_i_2226_, v_b_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_00_u03c3_2230_, lean_object* v_00_u03b1_2231_, lean_object* v_ext_2232_, lean_object* v_as_2233_, lean_object* v_sz_2234_, lean_object* v_i_2235_, lean_object* v_b_2236_){
_start:
{
size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2234_);
lean_dec(v_sz_2234_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2229_, v_00_u03c3_2230_, v_00_u03b1_2231_, v_ext_2232_, v_as_2233_, v_sz_boxed_2237_, v_i_boxed_2238_, v_b_2236_);
lean_dec_ref(v_as_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2240_, lean_object* v_00_u03c3_2241_, lean_object* v_00_u03b1_2242_, lean_object* v_ext_2243_, lean_object* v_as_2244_, size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_b_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2243_, v_as_2244_, v_sz_2245_, v_i_2246_, v_b_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2249_, lean_object* v_00_u03c3_2250_, lean_object* v_00_u03b1_2251_, lean_object* v_ext_2252_, lean_object* v_as_2253_, lean_object* v_sz_2254_, lean_object* v_i_2255_, lean_object* v_b_2256_){
_start:
{
size_t v_sz_boxed_2257_; size_t v_i_boxed_2258_; lean_object* v_res_2259_; 
v_sz_boxed_2257_ = lean_unbox_usize(v_sz_2254_);
lean_dec(v_sz_2254_);
v_i_boxed_2258_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2249_, v_00_u03c3_2250_, v_00_u03b1_2251_, v_ext_2252_, v_as_2253_, v_sz_boxed_2257_, v_i_boxed_2258_, v_b_2256_);
lean_dec_ref(v_as_2253_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2260_, lean_object* v_00_u03c3_2261_, lean_object* v_00_u03b1_2262_, lean_object* v_ext_2263_, lean_object* v_as_2264_, size_t v_sz_2265_, size_t v_i_2266_, lean_object* v_b_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2263_, v_as_2264_, v_sz_2265_, v_i_2266_, v_b_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_00_u03c3_2270_, lean_object* v_00_u03b1_2271_, lean_object* v_ext_2272_, lean_object* v_as_2273_, lean_object* v_sz_2274_, lean_object* v_i_2275_, lean_object* v_b_2276_){
_start:
{
size_t v_sz_boxed_2277_; size_t v_i_boxed_2278_; lean_object* v_res_2279_; 
v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2274_);
lean_dec(v_sz_2274_);
v_i_boxed_2278_ = lean_unbox_usize(v_i_2275_);
lean_dec(v_i_2275_);
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2269_, v_00_u03c3_2270_, v_00_u03b1_2271_, v_ext_2272_, v_as_2273_, v_sz_boxed_2277_, v_i_boxed_2278_, v_b_2276_);
lean_dec_ref(v_as_2273_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2280_, lean_object* v_s_2281_){
_start:
{
lean_object* v_stateStack_2282_; 
v_stateStack_2282_ = lean_ctor_get(v_s_2281_, 0);
lean_inc(v_stateStack_2282_);
if (lean_obj_tag(v_stateStack_2282_) == 1)
{
lean_object* v_head_2283_; lean_object* v_scopedEntries_2284_; lean_object* v_newEntries_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2312_; 
v_head_2283_ = lean_ctor_get(v_stateStack_2282_, 0);
lean_inc(v_head_2283_);
v_scopedEntries_2284_ = lean_ctor_get(v_s_2281_, 1);
v_newEntries_2285_ = lean_ctor_get(v_s_2281_, 2);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_s_2281_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_s_2281_, 0);
lean_dec(v_unused_2313_);
v___x_2287_ = v_s_2281_;
v_isShared_2288_ = v_isSharedCheck_2312_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_newEntries_2285_);
lean_inc(v_scopedEntries_2284_);
lean_dec(v_s_2281_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2312_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_tail_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2310_; 
v_tail_2289_ = lean_ctor_get(v_stateStack_2282_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_stateStack_2282_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v_stateStack_2282_, 0);
lean_dec(v_unused_2311_);
v___x_2291_ = v_stateStack_2282_;
v_isShared_2292_ = v_isSharedCheck_2310_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_tail_2289_);
lean_dec(v_stateStack_2282_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2310_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_state_2293_; lean_object* v_activeScopes_2294_; uint8_t v_delimitsLocal_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_state_2293_ = lean_ctor_get(v_head_2283_, 0);
v_activeScopes_2294_ = lean_ctor_get(v_head_2283_, 1);
v_delimitsLocal_2295_ = lean_ctor_get_uint8(v_head_2283_, sizeof(void*)*2);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_head_2283_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v_head_2283_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_activeScopes_2294_);
lean_inc(v_state_2293_);
lean_dec(v_head_2283_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = lean_apply_1(v_f_2280_, v_state_2293_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2299_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_activeScopes_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*2, v_delimitsLocal_2295_);
v___x_2301_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2303_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2301_);
v___x_2303_ = v___x_2291_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_tail_2289_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2303_);
v___x_2305_ = v___x_2287_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_scopedEntries_2284_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_newEntries_2285_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2282_);
lean_dec(v_f_2280_);
return v_s_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2314_, lean_object* v_env_2315_, lean_object* v_f_2316_){
_start:
{
lean_object* v_ext_2317_; lean_object* v_toEnvExtension_2318_; lean_object* v_asyncMode_2319_; lean_object* v___f_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_ext_2317_ = lean_ctor_get(v_ext_2314_, 1);
lean_inc_ref(v_ext_2317_);
lean_dec_ref(v_ext_2314_);
v_toEnvExtension_2318_ = lean_ctor_get(v_ext_2317_, 0);
v_asyncMode_2319_ = lean_ctor_get(v_toEnvExtension_2318_, 2);
lean_inc(v_asyncMode_2319_);
v___f_2320_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2320_, 0, v_f_2316_);
v___x_2321_ = lean_box(0);
v___x_2322_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2317_, v_env_2315_, v___f_2320_, v_asyncMode_2319_, v___x_2321_);
lean_dec(v_asyncMode_2319_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2323_, lean_object* v_00_u03b2_2324_, lean_object* v_00_u03c3_2325_, lean_object* v_ext_2326_, lean_object* v_env_2327_, lean_object* v_f_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2326_, v_env_2327_, v_f_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2330_, lean_object* v_____s_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_apply_2(v_toPure_2330_, lean_box(0), v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2334_, lean_object* v_toPure_2335_, lean_object* v_r_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2334_);
v___x_2338_ = lean_apply_2(v_toPure_2335_, lean_box(0), v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2339_, lean_object* v_toBind_2340_, lean_object* v___f_2341_, lean_object* v_a_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_modifyEnv_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_modifyEnv_2345_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_modifyEnv_2345_);
lean_dec_ref(v_inst_2339_);
v___x_2346_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2346_, 0, lean_box(0));
lean_closure_set(v___x_2346_, 1, lean_box(0));
lean_closure_set(v___x_2346_, 2, lean_box(0));
lean_closure_set(v___x_2346_, 3, v_a_2342_);
v___x_2347_ = lean_apply_1(v_modifyEnv_2345_, v___x_2346_);
v___x_2348_ = lean_apply_4(v_toBind_2340_, lean_box(0), lean_box(0), v___x_2347_, v___f_2341_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2349_, lean_object* v_inst_2350_, lean_object* v_toBind_2351_, lean_object* v_inst_2352_, lean_object* v___f_2353_, lean_object* v_____do__lift_2354_){
_start:
{
lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; size_t v_sz_2358_; size_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2355_ = lean_box(0);
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2356_, 0, v___x_2355_);
lean_closure_set(v___f_2356_, 1, v_toPure_2349_);
lean_inc(v_toBind_2351_);
v___f_2357_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2357_, 0, v_inst_2350_);
lean_closure_set(v___f_2357_, 1, v_toBind_2351_);
lean_closure_set(v___f_2357_, 2, v___f_2356_);
v_sz_2358_ = lean_array_size(v_____do__lift_2354_);
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2352_, v_____do__lift_2354_, v___f_2357_, v_sz_2358_, v___x_2359_, v___x_2355_);
v___x_2361_ = lean_apply_4(v_toBind_2351_, lean_box(0), lean_box(0), v___x_2360_, v___f_2353_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = l_Lean_scopedEnvExtensionsRef;
v___x_2363_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2363_, 0, lean_box(0));
lean_closure_set(v___x_2363_, 1, lean_box(0));
lean_closure_set(v___x_2363_, 2, v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_){
_start:
{
lean_object* v_toApplicative_2367_; lean_object* v_toBind_2368_; lean_object* v_toPure_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; 
v_toApplicative_2367_ = lean_ctor_get(v_inst_2364_, 0);
v_toBind_2368_ = lean_ctor_get(v_inst_2364_, 1);
lean_inc_n(v_toBind_2368_, 2);
v_toPure_2369_ = lean_ctor_get(v_toApplicative_2367_, 1);
lean_inc_n(v_toPure_2369_, 2);
v___x_2370_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2371_ = lean_apply_2(v_inst_2366_, lean_box(0), v___x_2370_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2372_, 0, v_toPure_2369_);
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2373_, 0, v_toPure_2369_);
lean_closure_set(v___f_2373_, 1, v_inst_2365_);
lean_closure_set(v___f_2373_, 2, v_toBind_2368_);
lean_closure_set(v___f_2373_, 3, v_inst_2364_);
lean_closure_set(v___f_2373_, 4, v___f_2372_);
v___x_2374_ = lean_apply_4(v_toBind_2368_, lean_box(0), lean_box(0), v___x_2371_, v___f_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_pushScope___redArg(v_inst_2376_, v_inst_2377_, v_inst_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2380_, lean_object* v_toBind_2381_, lean_object* v___f_2382_, lean_object* v_a_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_modifyEnv_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_modifyEnv_2386_ = lean_ctor_get(v_inst_2380_, 1);
lean_inc(v_modifyEnv_2386_);
lean_dec_ref(v_inst_2380_);
v___x_2387_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2387_, 0, lean_box(0));
lean_closure_set(v___x_2387_, 1, lean_box(0));
lean_closure_set(v___x_2387_, 2, lean_box(0));
lean_closure_set(v___x_2387_, 3, v_a_2383_);
v___x_2388_ = lean_apply_1(v_modifyEnv_2386_, v___x_2387_);
v___x_2389_ = lean_apply_4(v_toBind_2381_, lean_box(0), lean_box(0), v___x_2388_, v___f_2382_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2390_, lean_object* v_inst_2391_, lean_object* v_toBind_2392_, lean_object* v_inst_2393_, lean_object* v___f_2394_, lean_object* v_____do__lift_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; size_t v_sz_2399_; size_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2396_ = lean_box(0);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2397_, 0, v___x_2396_);
lean_closure_set(v___f_2397_, 1, v_toPure_2390_);
lean_inc(v_toBind_2392_);
v___f_2398_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2398_, 0, v_inst_2391_);
lean_closure_set(v___f_2398_, 1, v_toBind_2392_);
lean_closure_set(v___f_2398_, 2, v___f_2397_);
v_sz_2399_ = lean_array_size(v_____do__lift_2395_);
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2393_, v_____do__lift_2395_, v___f_2398_, v_sz_2399_, v___x_2400_, v___x_2396_);
v___x_2402_ = lean_apply_4(v_toBind_2392_, lean_box(0), lean_box(0), v___x_2401_, v___f_2394_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_){
_start:
{
lean_object* v_toApplicative_2406_; lean_object* v_toBind_2407_; lean_object* v_toPure_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; 
v_toApplicative_2406_ = lean_ctor_get(v_inst_2403_, 0);
v_toBind_2407_ = lean_ctor_get(v_inst_2403_, 1);
lean_inc_n(v_toBind_2407_, 2);
v_toPure_2408_ = lean_ctor_get(v_toApplicative_2406_, 1);
lean_inc_n(v_toPure_2408_, 2);
v___x_2409_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2410_ = lean_apply_2(v_inst_2405_, lean_box(0), v___x_2409_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2411_, 0, v_toPure_2408_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2412_, 0, v_toPure_2408_);
lean_closure_set(v___f_2412_, 1, v_inst_2404_);
lean_closure_set(v___f_2412_, 2, v_toBind_2407_);
lean_closure_set(v___f_2412_, 3, v_inst_2403_);
lean_closure_set(v___f_2412_, 4, v___f_2411_);
v___x_2413_ = lean_apply_4(v_toBind_2407_, lean_box(0), lean_box(0), v___x_2410_, v___f_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_popScope___redArg(v_inst_2415_, v_inst_2416_, v_inst_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2419_, v_x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2422_, lean_object* v_toBind_2423_, lean_object* v___f_2424_, lean_object* v_a_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_modifyEnv_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_modifyEnv_2428_ = lean_ctor_get(v_inst_2422_, 1);
lean_inc(v_modifyEnv_2428_);
lean_dec_ref(v_inst_2422_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2429_, 0, v_a_2425_);
v___x_2430_ = lean_apply_1(v_modifyEnv_2428_, v___f_2429_);
v___x_2431_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2430_, v___f_2424_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2432_, lean_object* v_inst_2433_, lean_object* v_toBind_2434_, lean_object* v_inst_2435_, lean_object* v___f_2436_, lean_object* v_____do__lift_2437_){
_start:
{
lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2438_ = lean_box(0);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2439_, 0, v___x_2438_);
lean_closure_set(v___f_2439_, 1, v_toPure_2432_);
lean_inc(v_toBind_2434_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2440_, 0, v_inst_2433_);
lean_closure_set(v___f_2440_, 1, v_toBind_2434_);
lean_closure_set(v___f_2440_, 2, v___f_2439_);
v_sz_2441_ = lean_array_size(v_____do__lift_2437_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2435_, v_____do__lift_2437_, v___f_2440_, v_sz_2441_, v___x_2442_, v___x_2438_);
v___x_2444_ = lean_apply_4(v_toBind_2434_, lean_box(0), lean_box(0), v___x_2443_, v___f_2436_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_){
_start:
{
lean_object* v_toApplicative_2448_; lean_object* v_toBind_2449_; lean_object* v_toPure_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v_toApplicative_2448_ = lean_ctor_get(v_inst_2445_, 0);
v_toBind_2449_ = lean_ctor_get(v_inst_2445_, 1);
lean_inc_n(v_toBind_2449_, 2);
v_toPure_2450_ = lean_ctor_get(v_toApplicative_2448_, 1);
lean_inc_n(v_toPure_2450_, 2);
v___x_2451_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2452_ = lean_apply_2(v_inst_2447_, lean_box(0), v___x_2451_);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2453_, 0, v_toPure_2450_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2454_, 0, v_toPure_2450_);
lean_closure_set(v___f_2454_, 1, v_inst_2446_);
lean_closure_set(v___f_2454_, 2, v_toBind_2449_);
lean_closure_set(v___f_2454_, 3, v_inst_2445_);
lean_closure_set(v___f_2454_, 4, v___f_2453_);
v___x_2455_ = lean_apply_4(v_toBind_2449_, lean_box(0), lean_box(0), v___x_2452_, v___f_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_setDelimitsLocal___redArg(v_inst_2457_, v_inst_2458_, v_inst_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2461_, lean_object* v_namespaceName_2462_, lean_object* v_x_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2461_, v_x_2463_, v_namespaceName_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2465_, lean_object* v_namespaceName_2466_, lean_object* v_toBind_2467_, lean_object* v___f_2468_, lean_object* v_a_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_modifyEnv_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_modifyEnv_2472_ = lean_ctor_get(v_inst_2465_, 1);
lean_inc(v_modifyEnv_2472_);
lean_dec_ref(v_inst_2465_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2473_, 0, v_a_2469_);
lean_closure_set(v___f_2473_, 1, v_namespaceName_2466_);
v___x_2474_ = lean_apply_1(v_modifyEnv_2472_, v___f_2473_);
v___x_2475_ = lean_apply_4(v_toBind_2467_, lean_box(0), lean_box(0), v___x_2474_, v___f_2468_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2476_, lean_object* v_inst_2477_, lean_object* v_namespaceName_2478_, lean_object* v_toBind_2479_, lean_object* v_inst_2480_, lean_object* v___f_2481_, lean_object* v_____do__lift_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2483_ = lean_box(0);
v___f_2484_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2484_, 0, v___x_2483_);
lean_closure_set(v___f_2484_, 1, v_toPure_2476_);
lean_inc(v_toBind_2479_);
v___f_2485_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2485_, 0, v_inst_2477_);
lean_closure_set(v___f_2485_, 1, v_namespaceName_2478_);
lean_closure_set(v___f_2485_, 2, v_toBind_2479_);
lean_closure_set(v___f_2485_, 3, v___f_2484_);
v_sz_2486_ = lean_array_size(v_____do__lift_2482_);
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2480_, v_____do__lift_2482_, v___f_2485_, v_sz_2486_, v___x_2487_, v___x_2483_);
v___x_2489_ = lean_apply_4(v_toBind_2479_, lean_box(0), lean_box(0), v___x_2488_, v___f_2481_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_namespaceName_2493_){
_start:
{
lean_object* v_toApplicative_2494_; lean_object* v_toBind_2495_; lean_object* v_toPure_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___f_2499_; lean_object* v___f_2500_; lean_object* v___x_2501_; 
v_toApplicative_2494_ = lean_ctor_get(v_inst_2490_, 0);
v_toBind_2495_ = lean_ctor_get(v_inst_2490_, 1);
lean_inc_n(v_toBind_2495_, 2);
v_toPure_2496_ = lean_ctor_get(v_toApplicative_2494_, 1);
lean_inc_n(v_toPure_2496_, 2);
v___x_2497_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2498_ = lean_apply_2(v_inst_2492_, lean_box(0), v___x_2497_);
v___f_2499_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2499_, 0, v_toPure_2496_);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2500_, 0, v_toPure_2496_);
lean_closure_set(v___f_2500_, 1, v_inst_2491_);
lean_closure_set(v___f_2500_, 2, v_namespaceName_2493_);
lean_closure_set(v___f_2500_, 3, v_toBind_2495_);
lean_closure_set(v___f_2500_, 4, v_inst_2490_);
lean_closure_set(v___f_2500_, 5, v___f_2499_);
v___x_2501_ = lean_apply_4(v_toBind_2495_, lean_box(0), lean_box(0), v___x_2498_, v___f_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_namespaceName_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_activateScoped___redArg(v_inst_2503_, v_inst_2504_, v_inst_2505_, v_namespaceName_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2509_){
_start:
{
lean_inc(v___y_2509_);
return v___y_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2510_);
lean_dec(v___y_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2512_, lean_object* v_a_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2517_, lean_object* v_a_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2517_, v_a_2518_, v___y_2519_);
lean_dec_ref(v___y_2519_);
lean_dec(v_x_2517_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_initial_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2525_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2530_){
_start:
{
lean_object* v_name_2532_; lean_object* v_addEntry_2533_; lean_object* v_initial_2534_; lean_object* v_finalizeImport_2535_; lean_object* v_exportEntry_x3f_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_name_2532_ = lean_ctor_get(v_descr_2530_, 0);
lean_inc(v_name_2532_);
v_addEntry_2533_ = lean_ctor_get(v_descr_2530_, 1);
lean_inc(v_addEntry_2533_);
v_initial_2534_ = lean_ctor_get(v_descr_2530_, 2);
lean_inc(v_initial_2534_);
v_finalizeImport_2535_ = lean_ctor_get(v_descr_2530_, 3);
lean_inc(v_finalizeImport_2535_);
v_exportEntry_x3f_2536_ = lean_ctor_get(v_descr_2530_, 4);
lean_inc_ref(v_exportEntry_x3f_2536_);
lean_dec_ref(v_descr_2530_);
v___f_2537_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2538_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2539_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2539_, 0, v_initial_2534_);
v___x_2540_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2540_, 0, v_name_2532_);
lean_ctor_set(v___x_2540_, 1, v___f_2539_);
lean_ctor_set(v___x_2540_, 2, v___f_2538_);
lean_ctor_set(v___x_2540_, 3, v___f_2537_);
lean_ctor_set(v___x_2540_, 4, v_addEntry_2533_);
lean_ctor_set(v___x_2540_, 5, v_finalizeImport_2535_);
lean_ctor_set(v___x_2540_, 6, v_exportEntry_x3f_2536_);
v___x_2541_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03c3_2546_, lean_object* v_descr_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2547_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2550_, lean_object* v_00_u03c3_2551_, lean_object* v_descr_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2550_, v_00_u03c3_2551_, v_descr_2552_);
return v_res_2554_;
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
