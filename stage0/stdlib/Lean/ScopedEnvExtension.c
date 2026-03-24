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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
lean_inc(v_a_1179_);
v___x_1185_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1178_, v_descr_1146_, v_a_1179_, v_stateStack_1172_, v___x_1184_);
lean_inc(v_a_1179_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1305_, uint8_t v_level_1306_, lean_object* v_s_1307_){
_start:
{
lean_object* v_newEntries_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_newEntries_1308_ = lean_ctor_get(v_s_1307_, 2);
lean_inc(v_newEntries_1308_);
lean_dec_ref(v_s_1307_);
v___x_1309_ = lean_array_mk(v_newEntries_1308_);
v___x_1310_ = l_Array_reverse___redArg(v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v___x_1310_);
v___x_1313_ = l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1305_, v_level_1306_, v___x_1310_, v___x_1311_, v___x_1312_);
lean_dec_ref(v___x_1310_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___boxed(lean_object* v_descr_1314_, lean_object* v_level_1315_, lean_object* v_s_1316_){
_start:
{
uint8_t v_level_boxed_1317_; lean_object* v_res_1318_; 
v_level_boxed_1317_ = lean_unbox(v_level_1315_);
v_res_1318_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1314_, v_level_boxed_1317_, v_s_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_00_u03c3_1321_, lean_object* v_descr_1322_, uint8_t v_level_1323_, lean_object* v_s_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1322_, v_level_1323_, v_s_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_00_u03c3_1328_, lean_object* v_descr_1329_, lean_object* v_level_1330_, lean_object* v_s_1331_){
_start:
{
uint8_t v_level_boxed_1332_; lean_object* v_res_1333_; 
v_level_boxed_1332_ = lean_unbox(v_level_1330_);
v_res_1333_ = l_Lean_ScopedEnvExtension_exportEntriesFn(v_00_u03b1_1326_, v_00_u03b2_1327_, v_00_u03c3_1328_, v_descr_1329_, v_level_boxed_1332_, v_s_1331_);
return v_res_1333_;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1390_, lean_object* v_x_1391_, uint8_t v_x_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
uint8_t v_x_114__boxed_1397_; lean_object* v_res_1398_; 
v_x_114__boxed_1397_ = lean_unbox(v_x_1396_);
v_res_1398_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1394_, v_x_1395_, v_x_114__boxed_1397_);
lean_dec_ref(v_x_1395_);
lean_dec_ref(v_x_1394_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1401_);
lean_dec_ref(v_x_1401_);
return v_res_1402_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___f_1408_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1409_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1410_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1411_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1414_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1412_);
lean_ctor_set(v___x_1414_, 2, v___f_1411_);
lean_ctor_set(v___x_1414_, 3, v___f_1410_);
lean_ctor_set(v___x_1414_, 4, v___f_1409_);
lean_ctor_set(v___x_1414_, 5, v___f_1408_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1415_){
_start:
{
lean_object* v___f_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___f_1416_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1417_, 0, v_inst_1415_);
v___f_1418_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1419_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1422_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1423_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v___f_1416_);
lean_ctor_set(v___x_1423_, 3, v___f_1417_);
lean_ctor_set(v___x_1423_, 4, v___f_1418_);
lean_ctor_set(v___x_1423_, 5, v___x_1422_);
lean_ctor_set(v___x_1423_, 6, v___f_1419_);
v___x_1424_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_a_1426_, lean_object* v_inst_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1433_, lean_object* v_inst_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1442_ = lean_st_mk_ref(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_descr_1446_, lean_object* v_x_1447_, lean_object* v_s_1448_, uint8_t v_level_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1446_, v_level_1449_, v_s_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_descr_1451_, lean_object* v_x_1452_, lean_object* v_s_1453_, lean_object* v_level_1454_){
_start:
{
uint8_t v_level_boxed_1455_; lean_object* v_res_1456_; 
v_level_boxed_1455_ = lean_unbox(v_level_1454_);
v_res_1456_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_descr_1451_, v_x_1452_, v_s_1453_, v_level_boxed_1455_);
lean_dec_ref(v_x_1452_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1460_){
_start:
{
lean_object* v_newEntries_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_newEntries_1461_ = lean_ctor_get(v_s_1460_, 2);
v___x_1462_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1463_ = l_List_lengthTR___redArg(v_newEntries_1461_);
v___x_1464_ = l_Nat_reprFast(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1462_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1467_);
lean_dec_ref(v_s_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(lean_object* v_x_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___closed__0));
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object* v_x_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__2(v_x_1471_);
lean_dec_ref(v_x_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1475_){
_start:
{
lean_object* v_name_1477_; lean_object* v___f_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_name_1477_ = lean_ctor_get(v_descr_1475_, 0);
lean_inc_ref(v_descr_1475_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1478_, 0, v_descr_1475_);
v___f_1479_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1480_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref(v_descr_1475_);
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1481_, 0, lean_box(0));
lean_closure_set(v___x_1481_, 1, lean_box(0));
lean_closure_set(v___x_1481_, 2, lean_box(0));
lean_closure_set(v___x_1481_, 3, v_descr_1475_);
lean_inc_ref(v_descr_1475_);
v___x_1482_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1482_, 0, lean_box(0));
lean_closure_set(v___x_1482_, 1, lean_box(0));
lean_closure_set(v___x_1482_, 2, lean_box(0));
lean_closure_set(v___x_1482_, 3, v_descr_1475_);
lean_inc_ref(v_descr_1475_);
v___x_1483_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1483_, 0, lean_box(0));
lean_closure_set(v___x_1483_, 1, lean_box(0));
lean_closure_set(v___x_1483_, 2, lean_box(0));
lean_closure_set(v___x_1483_, 3, v_descr_1475_);
v___x_1484_ = lean_box(2);
v___x_1485_ = lean_box(0);
lean_inc(v_name_1477_);
v___x_1486_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1486_, 0, v_name_1477_);
lean_ctor_set(v___x_1486_, 1, v___x_1481_);
lean_ctor_set(v___x_1486_, 2, v___x_1482_);
lean_ctor_set(v___x_1486_, 3, v___x_1483_);
lean_ctor_set(v___x_1486_, 4, v___f_1478_);
lean_ctor_set(v___x_1486_, 5, v___f_1479_);
lean_ctor_set(v___x_1486_, 6, v___x_1484_);
lean_ctor_set(v___x_1486_, 7, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___f_1480_);
v___x_1488_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1501_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1501_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1501_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1493_ = l_Lean_scopedEnvExtensionsRef;
v___x_1494_ = lean_st_ref_take(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_descr_1475_);
lean_ctor_set(v___x_1495_, 1, v_a_1489_);
lean_inc_ref(v___x_1495_);
v___x_1496_ = lean_array_push(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_st_ref_set(v___x_1493_, v___x_1496_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1499_ = v___x_1491_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1495_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec_ref(v_descr_1475_);
v_a_1502_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1488_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1488_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_00_u03c3_1515_, lean_object* v_descr_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_00_u03b2_1520_, lean_object* v_00_u03c3_1521_, lean_object* v_descr_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1519_, v_00_u03b2_1520_, v_00_u03c3_1521_, v_descr_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1525_){
_start:
{
lean_object* v_stateStack_1526_; 
v_stateStack_1526_ = lean_ctor_get(v_s_1525_, 0);
if (lean_obj_tag(v_stateStack_1526_) == 0)
{
return v_s_1525_;
}
else
{
lean_object* v_head_1527_; lean_object* v_scopedEntries_1528_; lean_object* v_newEntries_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1547_; 
lean_inc_ref(v_stateStack_1526_);
v_head_1527_ = lean_ctor_get(v_stateStack_1526_, 0);
lean_inc(v_head_1527_);
v_scopedEntries_1528_ = lean_ctor_get(v_s_1525_, 1);
v_newEntries_1529_ = lean_ctor_get(v_s_1525_, 2);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_s_1525_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_s_1525_, 0);
lean_dec(v_unused_1548_);
v___x_1531_ = v_s_1525_;
v_isShared_1532_ = v_isSharedCheck_1547_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_newEntries_1529_);
lean_inc(v_scopedEntries_1528_);
lean_dec(v_s_1525_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1547_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_state_1533_; lean_object* v_activeScopes_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1546_; 
v_state_1533_ = lean_ctor_get(v_head_1527_, 0);
v_activeScopes_1534_ = lean_ctor_get(v_head_1527_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_head_1527_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1536_ = v_head_1527_;
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_activeScopes_1534_);
lean_inc(v_state_1533_);
lean_dec(v_head_1527_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = 1;
if (v_isShared_1537_ == 0)
{
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_state_1533_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_activeScopes_1534_);
v___x_1540_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*2, v___x_1538_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_stateStack_1526_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1541_);
v___x_1543_ = v___x_1531_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_scopedEntries_1528_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_newEntries_1529_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1550_, lean_object* v_env_1551_){
_start:
{
lean_object* v_ext_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_ext_1552_ = lean_ctor_get(v_ext_1550_, 1);
lean_inc_ref(v_ext_1552_);
lean_dec_ref(v_ext_1550_);
v___f_1553_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1554_ = lean_box(1);
v___x_1555_ = lean_box(0);
v___x_1556_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1552_, v_env_1551_, v___f_1553_, v___x_1554_, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_00_u03c3_1559_, lean_object* v_ext_1560_, lean_object* v_env_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1560_, v_env_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1563_){
_start:
{
lean_object* v_stateStack_1564_; 
v_stateStack_1564_ = lean_ctor_get(v_s_1563_, 0);
if (lean_obj_tag(v_stateStack_1564_) == 1)
{
lean_object* v_tail_1565_; 
v_tail_1565_ = lean_ctor_get(v_stateStack_1564_, 1);
if (lean_obj_tag(v_tail_1565_) == 1)
{
lean_object* v_scopedEntries_1566_; lean_object* v_newEntries_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_inc_ref(v_tail_1565_);
v_scopedEntries_1566_ = lean_ctor_get(v_s_1563_, 1);
v_newEntries_1567_ = lean_ctor_get(v_s_1563_, 2);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_s_1563_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_s_1563_, 0);
lean_dec(v_unused_1575_);
v___x_1569_ = v_s_1563_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_newEntries_1567_);
lean_inc(v_scopedEntries_1566_);
lean_dec(v_s_1563_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_tail_1565_);
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_tail_1565_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_scopedEntries_1566_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_newEntries_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
return v_s_1563_;
}
}
else
{
return v_s_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1577_, lean_object* v_env_1578_){
_start:
{
lean_object* v_ext_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_ext_1579_ = lean_ctor_get(v_ext_1577_, 1);
lean_inc_ref(v_ext_1579_);
lean_dec_ref(v_ext_1577_);
v___f_1580_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1581_ = lean_box(1);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1579_, v_env_1578_, v___f_1580_, v___x_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_00_u03c3_1586_, lean_object* v_ext_1587_, lean_object* v_env_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1587_, v_env_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_s_1590_){
_start:
{
lean_object* v_stateStack_1591_; 
v_stateStack_1591_ = lean_ctor_get(v_s_1590_, 0);
lean_inc(v_stateStack_1591_);
if (lean_obj_tag(v_stateStack_1591_) == 0)
{
return v_s_1590_;
}
else
{
lean_object* v_head_1592_; lean_object* v_scopedEntries_1593_; lean_object* v_newEntries_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1620_; 
v_head_1592_ = lean_ctor_get(v_stateStack_1591_, 0);
lean_inc(v_head_1592_);
v_scopedEntries_1593_ = lean_ctor_get(v_s_1590_, 1);
v_newEntries_1594_ = lean_ctor_get(v_s_1590_, 2);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_s_1590_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v_s_1590_, 0);
lean_dec(v_unused_1621_);
v___x_1596_ = v_s_1590_;
v_isShared_1597_ = v_isSharedCheck_1620_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_newEntries_1594_);
lean_inc(v_scopedEntries_1593_);
lean_dec(v_s_1590_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1620_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_tail_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1618_; 
v_tail_1598_ = lean_ctor_get(v_stateStack_1591_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_stateStack_1591_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_stateStack_1591_, 0);
lean_dec(v_unused_1619_);
v___x_1600_ = v_stateStack_1591_;
v_isShared_1601_ = v_isSharedCheck_1618_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_tail_1598_);
lean_dec(v_stateStack_1591_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1618_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_state_1602_; lean_object* v_activeScopes_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1617_; 
v_state_1602_ = lean_ctor_get(v_head_1592_, 0);
v_activeScopes_1603_ = lean_ctor_get(v_head_1592_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_head_1592_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1605_ = v_head_1592_;
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_activeScopes_1603_);
lean_inc(v_state_1602_);
lean_dec(v_head_1592_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
uint8_t v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = 0;
if (v_isShared_1606_ == 0)
{
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_state_1602_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_activeScopes_1603_);
v___x_1609_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
lean_ctor_set_uint8(v___x_1609_, sizeof(void*)*2, v___x_1607_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1609_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_tail_1598_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1611_);
v___x_1613_ = v___x_1596_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_scopedEntries_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_newEntries_1594_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1623_, lean_object* v_env_1624_){
_start:
{
lean_object* v_ext_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_ext_1625_ = lean_ctor_get(v_ext_1623_, 1);
lean_inc_ref(v_ext_1625_);
lean_dec_ref(v_ext_1623_);
v___f_1626_ = ((lean_object*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___closed__0));
v___x_1627_ = lean_box(1);
v___x_1628_ = lean_box(0);
v___x_1629_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1625_, v_env_1624_, v___f_1626_, v___x_1627_, v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_00_u03c3_1632_, lean_object* v_ext_1633_, lean_object* v_env_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1633_, v_env_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1636_, lean_object* v_env_1637_, lean_object* v_b_1638_){
_start:
{
lean_object* v_ext_1639_; lean_object* v_toEnvExtension_1640_; lean_object* v_asyncMode_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_ext_1639_ = lean_ctor_get(v_ext_1636_, 1);
lean_inc_ref(v_ext_1639_);
lean_dec_ref(v_ext_1636_);
v_toEnvExtension_1640_ = lean_ctor_get(v_ext_1639_, 0);
v_asyncMode_1641_ = lean_ctor_get(v_toEnvExtension_1640_, 2);
lean_inc(v_asyncMode_1641_);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_b_1638_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1639_, v_env_1637_, v___x_1642_, v_asyncMode_1641_, v___x_1643_);
lean_dec(v_asyncMode_1641_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_00_u03c3_1647_, lean_object* v_ext_1648_, lean_object* v_env_1649_, lean_object* v_b_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1648_, v_env_1649_, v_b_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1652_, lean_object* v_env_1653_, lean_object* v_namespaceName_1654_, lean_object* v_b_1655_){
_start:
{
lean_object* v_ext_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1667_; 
v_ext_1656_ = lean_ctor_get(v_ext_1652_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_ext_1652_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_ext_1652_, 0);
lean_dec(v_unused_1668_);
v___x_1658_ = v_ext_1652_;
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_ext_1656_);
lean_dec(v_ext_1652_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_toEnvExtension_1660_; lean_object* v_asyncMode_1661_; lean_object* v___x_1663_; 
v_toEnvExtension_1660_ = lean_ctor_get(v_ext_1656_, 0);
v_asyncMode_1661_ = lean_ctor_get(v_toEnvExtension_1660_, 2);
lean_inc(v_asyncMode_1661_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
lean_ctor_set(v___x_1658_, 1, v_b_1655_);
lean_ctor_set(v___x_1658_, 0, v_namespaceName_1654_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_namespaceName_1654_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_b_1655_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1656_, v_env_1653_, v___x_1663_, v_asyncMode_1661_, v___x_1664_);
lean_dec(v_asyncMode_1661_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_00_u03c3_1671_, lean_object* v_ext_1672_, lean_object* v_env_1673_, lean_object* v_namespaceName_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1672_, v_env_1673_, v_namespaceName_1674_, v_b_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1677_, lean_object* v_states_1678_, lean_object* v_b_1679_){
_start:
{
if (lean_obj_tag(v_states_1678_) == 0)
{
lean_dec(v_b_1679_);
lean_dec_ref(v_ext_1677_);
return v_states_1678_;
}
else
{
lean_object* v_descr_1680_; lean_object* v_head_1681_; lean_object* v_tail_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1705_; 
v_descr_1680_ = lean_ctor_get(v_ext_1677_, 0);
v_head_1681_ = lean_ctor_get(v_states_1678_, 0);
v_tail_1682_ = lean_ctor_get(v_states_1678_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_states_1678_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1684_ = v_states_1678_;
v_isShared_1685_ = v_isSharedCheck_1705_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_tail_1682_);
lean_inc(v_head_1681_);
lean_dec(v_states_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1705_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_addEntry_1686_; lean_object* v_state_1687_; lean_object* v_activeScopes_1688_; uint8_t v_delimitsLocal_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1704_; 
v_addEntry_1686_ = lean_ctor_get(v_descr_1680_, 4);
v_state_1687_ = lean_ctor_get(v_head_1681_, 0);
v_activeScopes_1688_ = lean_ctor_get(v_head_1681_, 1);
v_delimitsLocal_1689_ = lean_ctor_get_uint8(v_head_1681_, sizeof(void*)*2);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_head_1681_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1691_ = v_head_1681_;
v_isShared_1692_ = v_isSharedCheck_1704_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_activeScopes_1688_);
lean_inc(v_state_1687_);
lean_dec(v_head_1681_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1704_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v_top_1695_; 
lean_inc(v_addEntry_1686_);
lean_inc(v_b_1679_);
v___x_1693_ = lean_apply_2(v_addEntry_1686_, v_state_1687_, v_b_1679_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1693_);
v_top_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_activeScopes_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*2, v_delimitsLocal_1689_);
v_top_1695_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
if (v_delimitsLocal_1689_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = l_Lean_stateStackModify___redArg(v_ext_1677_, v_tail_1682_, v_b_1679_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1696_);
lean_ctor_set(v___x_1684_, 0, v_top_1695_);
v___x_1698_ = v___x_1684_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_top_1695_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
else
{
lean_object* v___x_1701_; 
lean_dec(v_b_1679_);
lean_dec_ref(v_ext_1677_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v_top_1695_);
v___x_1701_ = v___x_1684_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_top_1695_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_tail_1682_);
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
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_00_u03c3_1708_, lean_object* v_ext_1709_, lean_object* v_states_1710_, lean_object* v_b_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_stateStackModify___redArg(v_ext_1709_, v_states_1710_, v_b_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1713_, lean_object* v_b_1714_, lean_object* v_s_1715_){
_start:
{
lean_object* v_stateStack_1716_; lean_object* v_scopedEntries_1717_; lean_object* v_newEntries_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_stateStack_1716_ = lean_ctor_get(v_s_1715_, 0);
v_scopedEntries_1717_ = lean_ctor_get(v_s_1715_, 1);
v_newEntries_1718_ = lean_ctor_get(v_s_1715_, 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_s_1715_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v_s_1715_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_newEntries_1718_);
lean_inc(v_scopedEntries_1717_);
lean_inc(v_stateStack_1716_);
lean_dec(v_s_1715_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_stateStackModify___redArg(v_ext_1713_, v_stateStack_1716_, v_b_1714_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_scopedEntries_1717_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_newEntries_1718_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1727_, lean_object* v_env_1728_, lean_object* v_b_1729_){
_start:
{
lean_object* v_ext_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_ext_1730_ = lean_ctor_get(v_ext_1727_, 1);
lean_inc_ref(v_ext_1730_);
v___f_1731_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1731_, 0, v_ext_1727_);
lean_closure_set(v___f_1731_, 1, v_b_1729_);
v___x_1732_ = lean_box(1);
v___x_1733_ = lean_box(0);
v___x_1734_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1730_, v_env_1728_, v___f_1731_, v___x_1732_, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_00_u03c3_1737_, lean_object* v_ext_1738_, lean_object* v_env_1739_, lean_object* v_b_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1738_, v_env_1739_, v_b_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1742_, lean_object* v_ext_1743_, lean_object* v_b_1744_, uint8_t v_kind_1745_, lean_object* v_namespaceName_1746_){
_start:
{
switch(v_kind_1745_)
{
case 0:
{
lean_object* v___x_1747_; 
lean_dec(v_namespaceName_1746_);
v___x_1747_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1743_, v_env_1742_, v_b_1744_);
return v___x_1747_;
}
case 1:
{
lean_object* v___x_1748_; 
lean_dec(v_namespaceName_1746_);
v___x_1748_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1743_, v_env_1742_, v_b_1744_);
return v___x_1748_;
}
default: 
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1743_, v_env_1742_, v_namespaceName_1746_, v_b_1744_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1750_, lean_object* v_ext_1751_, lean_object* v_b_1752_, lean_object* v_kind_1753_, lean_object* v_namespaceName_1754_){
_start:
{
uint8_t v_kind_boxed_1755_; lean_object* v_res_1756_; 
v_kind_boxed_1755_ = lean_unbox(v_kind_1753_);
v_res_1756_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1750_, v_ext_1751_, v_b_1752_, v_kind_boxed_1755_, v_namespaceName_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_00_u03c3_1759_, lean_object* v_env_1760_, lean_object* v_ext_1761_, lean_object* v_b_1762_, uint8_t v_kind_1763_, lean_object* v_namespaceName_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1760_, v_ext_1761_, v_b_1762_, v_kind_1763_, v_namespaceName_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_00_u03c3_1768_, lean_object* v_env_1769_, lean_object* v_ext_1770_, lean_object* v_b_1771_, lean_object* v_kind_1772_, lean_object* v_namespaceName_1773_){
_start:
{
uint8_t v_kind_boxed_1774_; lean_object* v_res_1775_; 
v_kind_boxed_1774_ = lean_unbox(v_kind_1772_);
v_res_1775_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1766_, v_00_u03b2_1767_, v_00_u03c3_1768_, v_env_1769_, v_ext_1770_, v_b_1771_, v_kind_boxed_1774_, v_namespaceName_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1776_, lean_object* v_b_1777_, uint8_t v_kind_1778_, lean_object* v_ns_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1780_, v_ext_1776_, v_b_1777_, v_kind_1778_, v_ns_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1782_, lean_object* v_b_1783_, lean_object* v_kind_1784_, lean_object* v_ns_1785_, lean_object* v_x_1786_){
_start:
{
uint8_t v_kind_boxed_1787_; lean_object* v_res_1788_; 
v_kind_boxed_1787_ = lean_unbox(v_kind_1784_);
v_res_1788_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1782_, v_b_1783_, v_kind_boxed_1787_, v_ns_1785_, v_x_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1789_, lean_object* v_ext_1790_, lean_object* v_b_1791_, uint8_t v_kind_1792_, lean_object* v_ns_1793_){
_start:
{
lean_object* v_modifyEnv_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v_modifyEnv_1794_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc(v_modifyEnv_1794_);
lean_dec_ref(v_inst_1789_);
v___x_1795_ = lean_box(v_kind_1792_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1796_, 0, v_ext_1790_);
lean_closure_set(v___f_1796_, 1, v_b_1791_);
lean_closure_set(v___f_1796_, 2, v___x_1795_);
lean_closure_set(v___f_1796_, 3, v_ns_1793_);
v___x_1797_ = lean_apply_1(v_modifyEnv_1794_, v___f_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1798_, lean_object* v_ext_1799_, lean_object* v_b_1800_, lean_object* v_kind_1801_, lean_object* v_ns_1802_){
_start:
{
uint8_t v_kind_boxed_1803_; lean_object* v_res_1804_; 
v_kind_boxed_1803_ = lean_unbox(v_kind_1801_);
v_res_1804_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1798_, v_ext_1799_, v_b_1800_, v_kind_boxed_1803_, v_ns_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_ext_1808_, lean_object* v_b_1809_, uint8_t v_kind_1810_){
_start:
{
lean_object* v_toBind_1811_; lean_object* v_getCurrNamespace_1812_; lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; 
v_toBind_1811_ = lean_ctor_get(v_inst_1805_, 1);
lean_inc(v_toBind_1811_);
lean_dec_ref(v_inst_1805_);
v_getCurrNamespace_1812_ = lean_ctor_get(v_inst_1806_, 0);
lean_inc(v_getCurrNamespace_1812_);
lean_dec_ref(v_inst_1806_);
v___x_1813_ = lean_box(v_kind_1810_);
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1814_, 0, v_inst_1807_);
lean_closure_set(v___f_1814_, 1, v_ext_1808_);
lean_closure_set(v___f_1814_, 2, v_b_1809_);
lean_closure_set(v___f_1814_, 3, v___x_1813_);
v___x_1815_ = lean_apply_4(v_toBind_1811_, lean_box(0), lean_box(0), v_getCurrNamespace_1812_, v___f_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_ext_1819_, lean_object* v_b_1820_, lean_object* v_kind_1821_){
_start:
{
uint8_t v_kind_boxed_1822_; lean_object* v_res_1823_; 
v_kind_boxed_1822_ = lean_unbox(v_kind_1821_);
v_res_1823_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1816_, v_inst_1817_, v_inst_1818_, v_ext_1819_, v_b_1820_, v_kind_boxed_1822_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1824_, lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_00_u03c3_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_ext_1831_, lean_object* v_b_1832_, uint8_t v_kind_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1828_, v_inst_1829_, v_inst_1830_, v_ext_1831_, v_b_1832_, v_kind_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1835_, lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_00_u03c3_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_ext_1842_, lean_object* v_b_1843_, lean_object* v_kind_1844_){
_start:
{
uint8_t v_kind_boxed_1845_; lean_object* v_res_1846_; 
v_kind_boxed_1845_ = lean_unbox(v_kind_1844_);
v_res_1846_ = l_Lean_ScopedEnvExtension_add(v_m_1835_, v_00_u03b1_1836_, v_00_u03b2_1837_, v_00_u03c3_1838_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_ext_1842_, v_b_1843_, v_kind_boxed_1845_);
return v_res_1846_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1851_ = lean_unsigned_to_nat(16u);
v___x_1852_ = lean_unsigned_to_nat(191u);
v___x_1853_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1854_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1855_ = l_mkPanicMessageWithDecl(v___x_1854_, v___x_1853_, v___x_1852_, v___x_1851_, v___x_1850_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1856_, lean_object* v_ext_1857_, lean_object* v_env_1858_, lean_object* v_asyncMode_1859_){
_start:
{
lean_object* v_ext_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_stateStack_1864_; 
v_ext_1860_ = lean_ctor_get(v_ext_1857_, 1);
v___x_1861_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1862_ = lean_box(0);
v___x_1863_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1861_, v_ext_1860_, v_env_1858_, v_asyncMode_1859_, v___x_1862_);
v_stateStack_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_stateStack_1864_);
lean_dec(v___x_1863_);
if (lean_obj_tag(v_stateStack_1864_) == 1)
{
lean_object* v_head_1865_; lean_object* v_state_1866_; 
lean_dec(v_inst_1856_);
v_head_1865_ = lean_ctor_get(v_stateStack_1864_, 0);
lean_inc(v_head_1865_);
lean_dec_ref(v_stateStack_1864_);
v_state_1866_ = lean_ctor_get(v_head_1865_, 0);
lean_inc(v_state_1866_);
lean_dec(v_head_1865_);
return v_state_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec(v_stateStack_1864_);
v___x_1867_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1868_ = l_panic___redArg(v_inst_1856_, v___x_1867_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1869_, lean_object* v_ext_1870_, lean_object* v_env_1871_, lean_object* v_asyncMode_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1869_, v_ext_1870_, v_env_1871_, v_asyncMode_1872_);
lean_dec(v_asyncMode_1872_);
lean_dec_ref(v_ext_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1874_, lean_object* v_00_u03b1_1875_, lean_object* v_00_u03b2_1876_, lean_object* v_inst_1877_, lean_object* v_ext_1878_, lean_object* v_env_1879_, lean_object* v_asyncMode_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1877_, v_ext_1878_, v_env_1879_, v_asyncMode_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1882_, lean_object* v_00_u03b1_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_inst_1885_, lean_object* v_ext_1886_, lean_object* v_env_1887_, lean_object* v_asyncMode_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1882_, v_00_u03b1_1883_, v_00_u03b2_1884_, v_inst_1885_, v_ext_1886_, v_env_1887_, v_asyncMode_1888_);
lean_dec(v_asyncMode_1888_);
lean_dec_ref(v_ext_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1890_, lean_object* v_as_1891_, size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_b_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1893_, v_sz_1892_);
if (v___x_1895_ == 0)
{
lean_dec_ref(v_ext_1890_);
return v_b_1894_;
}
else
{
lean_object* v_descr_1896_; lean_object* v_snd_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1911_; 
v_descr_1896_ = lean_ctor_get(v_ext_1890_, 0);
v_snd_1897_ = lean_ctor_get(v_b_1894_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_b_1894_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_b_1894_, 0);
lean_dec(v_unused_1912_);
v___x_1899_ = v_b_1894_;
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snd_1897_);
lean_dec(v_b_1894_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_addEntry_1901_; lean_object* v___x_1902_; lean_object* v_a_1903_; lean_object* v_state_1904_; lean_object* v___x_1906_; 
v_addEntry_1901_ = lean_ctor_get(v_descr_1896_, 4);
v___x_1902_ = lean_box(0);
v_a_1903_ = lean_array_uget_borrowed(v_as_1891_, v_i_1893_);
lean_inc(v_addEntry_1901_);
lean_inc(v_a_1903_);
v_state_1904_ = lean_apply_2(v_addEntry_1901_, v_snd_1897_, v_a_1903_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v_state_1904_);
lean_ctor_set(v___x_1899_, 0, v___x_1902_);
v___x_1906_ = v___x_1899_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_state_1904_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
size_t v___x_1907_; size_t v___x_1908_; 
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1893_, v___x_1907_);
v_i_1893_ = v___x_1908_;
v_b_1894_ = v___x_1906_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1913_, lean_object* v_as_1914_, lean_object* v_sz_1915_, lean_object* v_i_1916_, lean_object* v_b_1917_){
_start:
{
size_t v_sz_boxed_1918_; size_t v_i_boxed_1919_; lean_object* v_res_1920_; 
v_sz_boxed_1918_ = lean_unbox_usize(v_sz_1915_);
lean_dec(v_sz_1915_);
v_i_boxed_1919_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1913_, v_as_1914_, v_sz_boxed_1918_, v_i_boxed_1919_, v_b_1917_);
lean_dec_ref(v_as_1914_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1921_, lean_object* v_as_1922_, size_t v_sz_1923_, size_t v_i_1924_, lean_object* v_b_1925_){
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
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_add(v_i_1924_, v___x_1938_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1921_, v_as_1922_, v_sz_1923_, v___x_1939_, v___x_1937_);
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1944_, v_as_1945_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1948_);
lean_dec_ref(v_as_1945_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_ext_1952_, lean_object* v_inh_1953_, lean_object* v_n_1954_, lean_object* v_b_1955_){
_start:
{
if (lean_obj_tag(v_n_1954_) == 0)
{
lean_object* v_cs_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1971_; 
v_cs_1956_ = lean_ctor_get(v_n_1954_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_n_1954_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1958_ = v_n_1954_;
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_cs_1956_);
lean_dec(v_n_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1971_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v_fst_1965_; 
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_b_1955_);
v_sz_1962_ = lean_array_size(v_cs_1956_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_1952_, v_inh_1953_, v_cs_1956_, v_sz_1962_, v___x_1963_, v___x_1961_);
lean_dec_ref(v_cs_1956_);
v_fst_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_fst_1965_);
if (lean_obj_tag(v_fst_1965_) == 0)
{
lean_object* v_snd_1966_; lean_object* v___x_1968_; 
v_snd_1966_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_snd_1966_);
lean_dec_ref(v___x_1964_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
lean_ctor_set(v___x_1958_, 0, v_snd_1966_);
v___x_1968_ = v___x_1958_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_snd_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v_val_1970_; 
lean_dec_ref(v___x_1964_);
lean_del_object(v___x_1958_);
v_val_1970_ = lean_ctor_get(v_fst_1965_, 0);
lean_inc(v_val_1970_);
lean_dec_ref(v_fst_1965_);
return v_val_1970_;
}
}
}
else
{
lean_object* v_vs_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1987_; 
v_vs_1972_ = lean_ctor_get(v_n_1954_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_n_1954_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1974_ = v_n_1954_;
v_isShared_1975_ = v_isSharedCheck_1987_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_vs_1972_);
lean_dec(v_n_1954_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1987_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v_fst_1981_; 
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_b_1955_);
v_sz_1978_ = lean_array_size(v_vs_1972_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1952_, v_vs_1972_, v_sz_1978_, v___x_1979_, v___x_1977_);
lean_dec_ref(v_vs_1972_);
v_fst_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_fst_1981_);
if (lean_obj_tag(v_fst_1981_) == 0)
{
lean_object* v_snd_1982_; lean_object* v___x_1984_; 
v_snd_1982_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_snd_1982_);
lean_dec_ref(v___x_1980_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v_snd_1982_);
v___x_1984_ = v___x_1974_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_snd_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v_val_1986_; 
lean_dec_ref(v___x_1980_);
lean_del_object(v___x_1974_);
v_val_1986_ = lean_ctor_get(v_fst_1981_, 0);
lean_inc(v_val_1986_);
lean_dec_ref(v_fst_1981_);
return v_val_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_ext_1988_, lean_object* v_inh_1989_, lean_object* v_as_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_b_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v_ext_1988_);
return v_b_1993_;
}
else
{
lean_object* v_snd_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2013_; 
v_snd_1995_ = lean_ctor_get(v_b_1993_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_b_1993_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v_b_1993_, 0);
lean_dec(v_unused_2014_);
v___x_1997_ = v_b_1993_;
v_isShared_1998_ = v_isSharedCheck_2013_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1995_);
lean_dec(v_b_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2013_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_array_uget_borrowed(v_as_1990_, v_i_1992_);
lean_inc(v_snd_1995_);
lean_inc(v_a_1999_);
lean_inc_ref(v_ext_1988_);
v___x_2000_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_1988_, v_inh_1989_, v_a_1999_, v_snd_1995_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_dec_ref(v_ext_1988_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_snd_1995_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_dec(v_snd_1995_);
v_a_2005_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2000_);
v___x_2006_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v_a_2005_);
lean_ctor_set(v___x_1997_, 0, v___x_2006_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_a_2005_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
size_t v___x_2009_; size_t v___x_2010_; 
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_1992_, v___x_2009_);
v_i_1992_ = v___x_2010_;
v_b_1993_ = v___x_2008_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2015_, lean_object* v_inh_2016_, lean_object* v_as_2017_, lean_object* v_sz_2018_, lean_object* v_i_2019_, lean_object* v_b_2020_){
_start:
{
size_t v_sz_boxed_2021_; size_t v_i_boxed_2022_; lean_object* v_res_2023_; 
v_sz_boxed_2021_ = lean_unbox_usize(v_sz_2018_);
lean_dec(v_sz_2018_);
v_i_boxed_2022_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_2015_, v_inh_2016_, v_as_2017_, v_sz_boxed_2021_, v_i_boxed_2022_, v_b_2020_);
lean_dec_ref(v_as_2017_);
lean_dec(v_inh_2016_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_ext_2024_, lean_object* v_inh_2025_, lean_object* v_n_2026_, lean_object* v_b_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2024_, v_inh_2025_, v_n_2026_, v_b_2027_);
lean_dec(v_inh_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2029_, lean_object* v_as_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_b_2033_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_ext_2029_);
return v_b_2033_;
}
else
{
lean_object* v_descr_2035_; lean_object* v_snd_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2050_; 
v_descr_2035_ = lean_ctor_get(v_ext_2029_, 0);
v_snd_2036_ = lean_ctor_get(v_b_2033_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_b_2033_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_b_2033_, 0);
lean_dec(v_unused_2051_);
v___x_2038_ = v_b_2033_;
v_isShared_2039_ = v_isSharedCheck_2050_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_snd_2036_);
lean_dec(v_b_2033_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2050_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_addEntry_2040_; lean_object* v___x_2041_; lean_object* v_a_2042_; lean_object* v_state_2043_; lean_object* v___x_2045_; 
v_addEntry_2040_ = lean_ctor_get(v_descr_2035_, 4);
v___x_2041_ = lean_box(0);
v_a_2042_ = lean_array_uget_borrowed(v_as_2030_, v_i_2032_);
lean_inc(v_addEntry_2040_);
lean_inc(v_a_2042_);
v_state_2043_ = lean_apply_2(v_addEntry_2040_, v_snd_2036_, v_a_2042_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v_state_2043_);
lean_ctor_set(v___x_2038_, 0, v___x_2041_);
v___x_2045_ = v___x_2038_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_state_2043_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2032_, v___x_2046_);
v_i_2032_ = v___x_2047_;
v_b_2033_ = v___x_2045_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2052_, lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_){
_start:
{
size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2052_, v_as_2053_, v_sz_boxed_2057_, v_i_boxed_2058_, v_b_2056_);
lean_dec_ref(v_as_2053_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2060_, lean_object* v_as_2061_, size_t v_sz_2062_, size_t v_i_2063_, lean_object* v_b_2064_){
_start:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_usize_dec_lt(v_i_2063_, v_sz_2062_);
if (v___x_2065_ == 0)
{
lean_dec_ref(v_ext_2060_);
return v_b_2064_;
}
else
{
lean_object* v_descr_2066_; lean_object* v_snd_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2081_; 
v_descr_2066_ = lean_ctor_get(v_ext_2060_, 0);
v_snd_2067_ = lean_ctor_get(v_b_2064_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_b_2064_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_b_2064_, 0);
lean_dec(v_unused_2082_);
v___x_2069_ = v_b_2064_;
v_isShared_2070_ = v_isSharedCheck_2081_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_snd_2067_);
lean_dec(v_b_2064_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2081_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_addEntry_2071_; lean_object* v___x_2072_; lean_object* v_a_2073_; lean_object* v_state_2074_; lean_object* v___x_2076_; 
v_addEntry_2071_ = lean_ctor_get(v_descr_2066_, 4);
v___x_2072_ = lean_box(0);
v_a_2073_ = lean_array_uget_borrowed(v_as_2061_, v_i_2063_);
lean_inc(v_addEntry_2071_);
lean_inc(v_a_2073_);
v_state_2074_ = lean_apply_2(v_addEntry_2071_, v_snd_2067_, v_a_2073_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v_state_2074_);
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_state_2074_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_add(v_i_2063_, v___x_2077_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2060_, v_as_2061_, v_sz_2062_, v___x_2078_, v___x_2076_);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2083_, lean_object* v_as_2084_, lean_object* v_sz_2085_, lean_object* v_i_2086_, lean_object* v_b_2087_){
_start:
{
size_t v_sz_boxed_2088_; size_t v_i_boxed_2089_; lean_object* v_res_2090_; 
v_sz_boxed_2088_ = lean_unbox_usize(v_sz_2085_);
lean_dec(v_sz_2085_);
v_i_boxed_2089_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_res_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2083_, v_as_2084_, v_sz_boxed_2088_, v_i_boxed_2089_, v_b_2087_);
lean_dec_ref(v_as_2084_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2091_, lean_object* v_t_2092_, lean_object* v_init_2093_){
_start:
{
lean_object* v_root_2094_; lean_object* v_tail_2095_; lean_object* v___x_2096_; 
v_root_2094_ = lean_ctor_get(v_t_2092_, 0);
lean_inc_ref(v_root_2094_);
v_tail_2095_ = lean_ctor_get(v_t_2092_, 1);
lean_inc_ref(v_tail_2095_);
lean_dec_ref(v_t_2092_);
lean_inc(v_init_2093_);
lean_inc_ref(v_ext_2091_);
v___x_2096_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2091_, v_init_2093_, v_root_2094_, v_init_2093_);
lean_dec(v_init_2093_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
lean_dec_ref(v_tail_2095_);
lean_dec_ref(v_ext_2091_);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
return v_a_2097_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; size_t v_sz_2101_; size_t v___x_2102_; lean_object* v___x_2103_; lean_object* v_fst_2104_; 
v_a_2098_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2096_);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_a_2098_);
v_sz_2101_ = lean_array_size(v_tail_2095_);
v___x_2102_ = ((size_t)0ULL);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2091_, v_tail_2095_, v_sz_2101_, v___x_2102_, v___x_2100_);
lean_dec_ref(v_tail_2095_);
v_fst_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_fst_2104_);
if (lean_obj_tag(v_fst_2104_) == 0)
{
lean_object* v_snd_2105_; 
v_snd_2105_ = lean_ctor_get(v___x_2103_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2103_);
return v_snd_2105_;
}
else
{
lean_object* v_val_2106_; 
lean_dec_ref(v___x_2103_);
v_val_2106_ = lean_ctor_get(v_fst_2104_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v_fst_2104_);
return v_val_2106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2107_, lean_object* v_ext_2108_, lean_object* v_s_2109_){
_start:
{
lean_object* v_stateStack_2110_; 
v_stateStack_2110_ = lean_ctor_get(v_s_2109_, 0);
lean_inc(v_stateStack_2110_);
if (lean_obj_tag(v_stateStack_2110_) == 1)
{
lean_object* v_scopedEntries_2111_; lean_object* v_newEntries_2112_; lean_object* v_head_2113_; lean_object* v_tail_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2143_; 
v_scopedEntries_2111_ = lean_ctor_get(v_s_2109_, 1);
v_newEntries_2112_ = lean_ctor_get(v_s_2109_, 2);
v_head_2113_ = lean_ctor_get(v_stateStack_2110_, 0);
v_tail_2114_ = lean_ctor_get(v_stateStack_2110_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_stateStack_2110_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2116_ = v_stateStack_2110_;
v_isShared_2117_ = v_isSharedCheck_2143_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_tail_2114_);
lean_inc(v_head_2113_);
lean_dec(v_stateStack_2110_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2143_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___y_2119_; lean_object* v_state_2124_; lean_object* v_activeScopes_2125_; uint8_t v_delimitsLocal_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2142_; 
v_state_2124_ = lean_ctor_get(v_head_2113_, 0);
v_activeScopes_2125_ = lean_ctor_get(v_head_2113_, 1);
v_delimitsLocal_2126_ = lean_ctor_get_uint8(v_head_2113_, sizeof(void*)*2);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_head_2113_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2128_ = v_head_2113_;
v_isShared_2129_ = v_isSharedCheck_2142_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_activeScopes_2125_);
lean_inc(v_state_2124_);
lean_dec(v_head_2113_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2142_;
goto v_resetjp_2127_;
}
v___jp_2118_:
{
lean_object* v___x_2121_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___y_2119_);
v___x_2121_ = v___x_2116_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___y_2119_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_tail_2114_);
v___x_2121_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_scopedEntries_2111_);
lean_ctor_set(v___x_2122_, 2, v_newEntries_2112_);
return v___x_2122_;
}
}
v_resetjp_2127_:
{
uint8_t v___x_2130_; 
v___x_2130_ = l_Lean_NameSet_contains(v_activeScopes_2125_, v_namespaceName_2107_);
if (v___x_2130_ == 0)
{
lean_object* v_activeScopes_2131_; lean_object* v___x_2132_; 
lean_inc(v_newEntries_2112_);
lean_inc_ref(v_scopedEntries_2111_);
lean_dec_ref(v_s_2109_);
lean_inc(v_namespaceName_2107_);
v_activeScopes_2131_ = l_Lean_NameSet_insert(v_activeScopes_2125_, v_namespaceName_2107_);
lean_inc_ref(v_scopedEntries_2111_);
v___x_2132_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2111_, v_namespaceName_2107_);
lean_dec(v_namespaceName_2107_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2134_; 
lean_dec_ref(v_ext_2108_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_activeScopes_2131_);
v___x_2134_ = v___x_2128_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_state_2124_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_activeScopes_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2135_, sizeof(void*)*2, v_delimitsLocal_2126_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v___y_2119_ = v___x_2134_;
goto v___jp_2118_;
}
}
else
{
lean_object* v_val_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v_val_2136_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2136_);
lean_dec_ref(v___x_2132_);
v___x_2137_ = 1;
v___x_2138_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2108_, v_val_2136_, v_state_2124_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_activeScopes_2131_);
lean_ctor_set(v___x_2128_, 0, v___x_2138_);
v___x_2140_ = v___x_2128_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_activeScopes_2131_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*2, v___x_2137_);
v___y_2119_ = v___x_2140_;
goto v___jp_2118_;
}
}
}
else
{
lean_del_object(v___x_2128_);
lean_dec(v_activeScopes_2125_);
lean_dec(v_state_2124_);
lean_del_object(v___x_2116_);
lean_dec(v_tail_2114_);
lean_dec_ref(v_ext_2108_);
lean_dec(v_namespaceName_2107_);
return v_s_2109_;
}
}
}
}
else
{
lean_dec(v_stateStack_2110_);
lean_dec_ref(v_ext_2108_);
lean_dec(v_namespaceName_2107_);
return v_s_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2144_, lean_object* v_env_2145_, lean_object* v_namespaceName_2146_){
_start:
{
lean_object* v_ext_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_ext_2147_ = lean_ctor_get(v_ext_2144_, 1);
lean_inc_ref(v_ext_2147_);
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2148_, 0, v_namespaceName_2146_);
lean_closure_set(v___f_2148_, 1, v_ext_2144_);
v___x_2149_ = lean_box(1);
v___x_2150_ = lean_box(0);
v___x_2151_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2147_, v_env_2145_, v___f_2148_, v___x_2149_, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_00_u03c3_2154_, lean_object* v_ext_2155_, lean_object* v_env_2156_, lean_object* v_namespaceName_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2155_, v_env_2156_, v_namespaceName_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2159_, lean_object* v_00_u03c3_2160_, lean_object* v_00_u03b1_2161_, lean_object* v_ext_2162_, lean_object* v_t_2163_, lean_object* v_init_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2162_, v_t_2163_, v_init_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2166_, lean_object* v_00_u03c3_2167_, lean_object* v_00_u03b1_2168_, lean_object* v_ext_2169_, lean_object* v_inh_2170_, lean_object* v_n_2171_, lean_object* v_b_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_ext_2169_, v_inh_2170_, v_n_2171_, v_b_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2174_, lean_object* v_00_u03c3_2175_, lean_object* v_00_u03b1_2176_, lean_object* v_ext_2177_, lean_object* v_inh_2178_, lean_object* v_n_2179_, lean_object* v_b_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2174_, v_00_u03c3_2175_, v_00_u03b1_2176_, v_ext_2177_, v_inh_2178_, v_n_2179_, v_b_2180_);
lean_dec(v_inh_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2182_, lean_object* v_00_u03c3_2183_, lean_object* v_00_u03b1_2184_, lean_object* v_ext_2185_, lean_object* v_as_2186_, size_t v_sz_2187_, size_t v_i_2188_, lean_object* v_b_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2185_, v_as_2186_, v_sz_2187_, v_i_2188_, v_b_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_00_u03c3_2192_, lean_object* v_00_u03b1_2193_, lean_object* v_ext_2194_, lean_object* v_as_2195_, lean_object* v_sz_2196_, lean_object* v_i_2197_, lean_object* v_b_2198_){
_start:
{
size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2196_);
lean_dec(v_sz_2196_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2191_, v_00_u03c3_2192_, v_00_u03b1_2193_, v_ext_2194_, v_as_2195_, v_sz_boxed_2199_, v_i_boxed_2200_, v_b_2198_);
lean_dec_ref(v_as_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2202_, lean_object* v_00_u03c3_2203_, lean_object* v_00_u03b1_2204_, lean_object* v_ext_2205_, lean_object* v_inh_2206_, lean_object* v_as_2207_, size_t v_sz_2208_, size_t v_i_2209_, lean_object* v_b_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_ext_2205_, v_inh_2206_, v_as_2207_, v_sz_2208_, v_i_2209_, v_b_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2212_, lean_object* v_00_u03c3_2213_, lean_object* v_00_u03b1_2214_, lean_object* v_ext_2215_, lean_object* v_inh_2216_, lean_object* v_as_2217_, lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_b_2220_){
_start:
{
size_t v_sz_boxed_2221_; size_t v_i_boxed_2222_; lean_object* v_res_2223_; 
v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2222_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2212_, v_00_u03c3_2213_, v_00_u03b1_2214_, v_ext_2215_, v_inh_2216_, v_as_2217_, v_sz_boxed_2221_, v_i_boxed_2222_, v_b_2220_);
lean_dec_ref(v_as_2217_);
lean_dec(v_inh_2216_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2224_, lean_object* v_00_u03c3_2225_, lean_object* v_00_u03b1_2226_, lean_object* v_ext_2227_, lean_object* v_as_2228_, size_t v_sz_2229_, size_t v_i_2230_, lean_object* v_b_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2227_, v_as_2228_, v_sz_2229_, v_i_2230_, v_b_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2233_, lean_object* v_00_u03c3_2234_, lean_object* v_00_u03b1_2235_, lean_object* v_ext_2236_, lean_object* v_as_2237_, lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_b_2240_){
_start:
{
size_t v_sz_boxed_2241_; size_t v_i_boxed_2242_; lean_object* v_res_2243_; 
v_sz_boxed_2241_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2242_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2233_, v_00_u03c3_2234_, v_00_u03b1_2235_, v_ext_2236_, v_as_2237_, v_sz_boxed_2241_, v_i_boxed_2242_, v_b_2240_);
lean_dec_ref(v_as_2237_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2244_, lean_object* v_00_u03c3_2245_, lean_object* v_00_u03b1_2246_, lean_object* v_ext_2247_, lean_object* v_as_2248_, size_t v_sz_2249_, size_t v_i_2250_, lean_object* v_b_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2247_, v_as_2248_, v_sz_2249_, v_i_2250_, v_b_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2253_, lean_object* v_00_u03c3_2254_, lean_object* v_00_u03b1_2255_, lean_object* v_ext_2256_, lean_object* v_as_2257_, lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_b_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2253_, v_00_u03c3_2254_, v_00_u03b1_2255_, v_ext_2256_, v_as_2257_, v_sz_boxed_2261_, v_i_boxed_2262_, v_b_2260_);
lean_dec_ref(v_as_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2264_, lean_object* v_00_u03c3_2265_, lean_object* v_00_u03b1_2266_, lean_object* v_ext_2267_, lean_object* v_as_2268_, size_t v_sz_2269_, size_t v_i_2270_, lean_object* v_b_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2267_, v_as_2268_, v_sz_2269_, v_i_2270_, v_b_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2273_, lean_object* v_00_u03c3_2274_, lean_object* v_00_u03b1_2275_, lean_object* v_ext_2276_, lean_object* v_as_2277_, lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_b_2280_){
_start:
{
size_t v_sz_boxed_2281_; size_t v_i_boxed_2282_; lean_object* v_res_2283_; 
v_sz_boxed_2281_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2282_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2273_, v_00_u03c3_2274_, v_00_u03b1_2275_, v_ext_2276_, v_as_2277_, v_sz_boxed_2281_, v_i_boxed_2282_, v_b_2280_);
lean_dec_ref(v_as_2277_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2284_, lean_object* v_s_2285_){
_start:
{
lean_object* v_stateStack_2286_; 
v_stateStack_2286_ = lean_ctor_get(v_s_2285_, 0);
lean_inc(v_stateStack_2286_);
if (lean_obj_tag(v_stateStack_2286_) == 1)
{
lean_object* v_head_2287_; lean_object* v_scopedEntries_2288_; lean_object* v_newEntries_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2316_; 
v_head_2287_ = lean_ctor_get(v_stateStack_2286_, 0);
lean_inc(v_head_2287_);
v_scopedEntries_2288_ = lean_ctor_get(v_s_2285_, 1);
v_newEntries_2289_ = lean_ctor_get(v_s_2285_, 2);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_s_2285_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_s_2285_, 0);
lean_dec(v_unused_2317_);
v___x_2291_ = v_s_2285_;
v_isShared_2292_ = v_isSharedCheck_2316_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_newEntries_2289_);
lean_inc(v_scopedEntries_2288_);
lean_dec(v_s_2285_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2316_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_tail_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2314_; 
v_tail_2293_ = lean_ctor_get(v_stateStack_2286_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_stateStack_2286_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_stateStack_2286_, 0);
lean_dec(v_unused_2315_);
v___x_2295_ = v_stateStack_2286_;
v_isShared_2296_ = v_isSharedCheck_2314_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_tail_2293_);
lean_dec(v_stateStack_2286_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2314_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_state_2297_; lean_object* v_activeScopes_2298_; uint8_t v_delimitsLocal_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2313_; 
v_state_2297_ = lean_ctor_get(v_head_2287_, 0);
v_activeScopes_2298_ = lean_ctor_get(v_head_2287_, 1);
v_delimitsLocal_2299_ = lean_ctor_get_uint8(v_head_2287_, sizeof(void*)*2);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_head_2287_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2301_ = v_head_2287_;
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_activeScopes_2298_);
lean_inc(v_state_2297_);
lean_dec(v_head_2287_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = lean_apply_1(v_f_2284_, v_state_2297_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_activeScopes_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*2, v_delimitsLocal_2299_);
v___x_2305_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2305_);
v___x_2307_ = v___x_2295_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_tail_2293_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2307_);
v___x_2309_ = v___x_2291_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_scopedEntries_2288_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_newEntries_2289_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2286_);
lean_dec(v_f_2284_);
return v_s_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2318_, lean_object* v_env_2319_, lean_object* v_f_2320_){
_start:
{
lean_object* v_ext_2321_; lean_object* v_toEnvExtension_2322_; lean_object* v_asyncMode_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_ext_2321_ = lean_ctor_get(v_ext_2318_, 1);
lean_inc_ref(v_ext_2321_);
lean_dec_ref(v_ext_2318_);
v_toEnvExtension_2322_ = lean_ctor_get(v_ext_2321_, 0);
v_asyncMode_2323_ = lean_ctor_get(v_toEnvExtension_2322_, 2);
lean_inc(v_asyncMode_2323_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2324_, 0, v_f_2320_);
v___x_2325_ = lean_box(0);
v___x_2326_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2321_, v_env_2319_, v___f_2324_, v_asyncMode_2323_, v___x_2325_);
lean_dec(v_asyncMode_2323_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2327_, lean_object* v_00_u03b2_2328_, lean_object* v_00_u03c3_2329_, lean_object* v_ext_2330_, lean_object* v_env_2331_, lean_object* v_f_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2330_, v_env_2331_, v_f_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2334_, lean_object* v_____s_2335_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_apply_2(v_toPure_2334_, lean_box(0), v___x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2338_, lean_object* v_toPure_2339_, lean_object* v_r_2340_){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2338_);
v___x_2342_ = lean_apply_2(v_toPure_2339_, lean_box(0), v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2343_, lean_object* v_toBind_2344_, lean_object* v___f_2345_, lean_object* v_a_2346_, lean_object* v_x_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_modifyEnv_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_modifyEnv_2349_ = lean_ctor_get(v_inst_2343_, 1);
lean_inc(v_modifyEnv_2349_);
lean_dec_ref(v_inst_2343_);
v___x_2350_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2350_, 0, lean_box(0));
lean_closure_set(v___x_2350_, 1, lean_box(0));
lean_closure_set(v___x_2350_, 2, lean_box(0));
lean_closure_set(v___x_2350_, 3, v_a_2346_);
v___x_2351_ = lean_apply_1(v_modifyEnv_2349_, v___x_2350_);
v___x_2352_ = lean_apply_4(v_toBind_2344_, lean_box(0), lean_box(0), v___x_2351_, v___f_2345_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2353_, lean_object* v_inst_2354_, lean_object* v_toBind_2355_, lean_object* v_inst_2356_, lean_object* v___f_2357_, lean_object* v_____do__lift_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___f_2360_; lean_object* v___f_2361_; size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2359_ = lean_box(0);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2360_, 0, v___x_2359_);
lean_closure_set(v___f_2360_, 1, v_toPure_2353_);
lean_inc(v_toBind_2355_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2361_, 0, v_inst_2354_);
lean_closure_set(v___f_2361_, 1, v_toBind_2355_);
lean_closure_set(v___f_2361_, 2, v___f_2360_);
v_sz_2362_ = lean_array_size(v_____do__lift_2358_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2356_, v_____do__lift_2358_, v___f_2361_, v_sz_2362_, v___x_2363_, v___x_2359_);
v___x_2365_ = lean_apply_4(v_toBind_2355_, lean_box(0), lean_box(0), v___x_2364_, v___f_2357_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_Lean_scopedEnvExtensionsRef;
v___x_2367_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2367_, 0, lean_box(0));
lean_closure_set(v___x_2367_, 1, lean_box(0));
lean_closure_set(v___x_2367_, 2, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_){
_start:
{
lean_object* v_toApplicative_2371_; lean_object* v_toBind_2372_; lean_object* v_toPure_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; 
v_toApplicative_2371_ = lean_ctor_get(v_inst_2368_, 0);
v_toBind_2372_ = lean_ctor_get(v_inst_2368_, 1);
lean_inc(v_toBind_2372_);
v_toPure_2373_ = lean_ctor_get(v_toApplicative_2371_, 1);
lean_inc(v_toPure_2373_);
v___x_2374_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2375_ = lean_apply_2(v_inst_2370_, lean_box(0), v___x_2374_);
lean_inc(v_toPure_2373_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2376_, 0, v_toPure_2373_);
lean_inc(v_toBind_2372_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2377_, 0, v_toPure_2373_);
lean_closure_set(v___f_2377_, 1, v_inst_2369_);
lean_closure_set(v___f_2377_, 2, v_toBind_2372_);
lean_closure_set(v___f_2377_, 3, v_inst_2368_);
lean_closure_set(v___f_2377_, 4, v___f_2376_);
v___x_2378_ = lean_apply_4(v_toBind_2372_, lean_box(0), lean_box(0), v___x_2375_, v___f_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_pushScope___redArg(v_inst_2380_, v_inst_2381_, v_inst_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2384_, lean_object* v_toBind_2385_, lean_object* v___f_2386_, lean_object* v_a_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_modifyEnv_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_modifyEnv_2390_ = lean_ctor_get(v_inst_2384_, 1);
lean_inc(v_modifyEnv_2390_);
lean_dec_ref(v_inst_2384_);
v___x_2391_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2391_, 0, lean_box(0));
lean_closure_set(v___x_2391_, 1, lean_box(0));
lean_closure_set(v___x_2391_, 2, lean_box(0));
lean_closure_set(v___x_2391_, 3, v_a_2387_);
v___x_2392_ = lean_apply_1(v_modifyEnv_2390_, v___x_2391_);
v___x_2393_ = lean_apply_4(v_toBind_2385_, lean_box(0), lean_box(0), v___x_2392_, v___f_2386_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2394_, lean_object* v_inst_2395_, lean_object* v_toBind_2396_, lean_object* v_inst_2397_, lean_object* v___f_2398_, lean_object* v_____do__lift_2399_){
_start:
{
lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___f_2402_; size_t v_sz_2403_; size_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2400_ = lean_box(0);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2401_, 0, v___x_2400_);
lean_closure_set(v___f_2401_, 1, v_toPure_2394_);
lean_inc(v_toBind_2396_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2402_, 0, v_inst_2395_);
lean_closure_set(v___f_2402_, 1, v_toBind_2396_);
lean_closure_set(v___f_2402_, 2, v___f_2401_);
v_sz_2403_ = lean_array_size(v_____do__lift_2399_);
v___x_2404_ = ((size_t)0ULL);
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2397_, v_____do__lift_2399_, v___f_2402_, v_sz_2403_, v___x_2404_, v___x_2400_);
v___x_2406_ = lean_apply_4(v_toBind_2396_, lean_box(0), lean_box(0), v___x_2405_, v___f_2398_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_){
_start:
{
lean_object* v_toApplicative_2410_; lean_object* v_toBind_2411_; lean_object* v_toPure_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___f_2416_; lean_object* v___x_2417_; 
v_toApplicative_2410_ = lean_ctor_get(v_inst_2407_, 0);
v_toBind_2411_ = lean_ctor_get(v_inst_2407_, 1);
lean_inc(v_toBind_2411_);
v_toPure_2412_ = lean_ctor_get(v_toApplicative_2410_, 1);
lean_inc(v_toPure_2412_);
v___x_2413_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2414_ = lean_apply_2(v_inst_2409_, lean_box(0), v___x_2413_);
lean_inc(v_toPure_2412_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2415_, 0, v_toPure_2412_);
lean_inc(v_toBind_2411_);
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2416_, 0, v_toPure_2412_);
lean_closure_set(v___f_2416_, 1, v_inst_2408_);
lean_closure_set(v___f_2416_, 2, v_toBind_2411_);
lean_closure_set(v___f_2416_, 3, v_inst_2407_);
lean_closure_set(v___f_2416_, 4, v___f_2415_);
v___x_2417_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2414_, v___f_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_popScope___redArg(v_inst_2419_, v_inst_2420_, v_inst_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2423_, v_x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2426_, lean_object* v_toBind_2427_, lean_object* v___f_2428_, lean_object* v_a_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_modifyEnv_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_modifyEnv_2432_ = lean_ctor_get(v_inst_2426_, 1);
lean_inc(v_modifyEnv_2432_);
lean_dec_ref(v_inst_2426_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2433_, 0, v_a_2429_);
v___x_2434_ = lean_apply_1(v_modifyEnv_2432_, v___f_2433_);
v___x_2435_ = lean_apply_4(v_toBind_2427_, lean_box(0), lean_box(0), v___x_2434_, v___f_2428_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2436_, lean_object* v_inst_2437_, lean_object* v_toBind_2438_, lean_object* v_inst_2439_, lean_object* v___f_2440_, lean_object* v_____do__lift_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; size_t v_sz_2445_; size_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2442_ = lean_box(0);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2443_, 0, v___x_2442_);
lean_closure_set(v___f_2443_, 1, v_toPure_2436_);
lean_inc(v_toBind_2438_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2444_, 0, v_inst_2437_);
lean_closure_set(v___f_2444_, 1, v_toBind_2438_);
lean_closure_set(v___f_2444_, 2, v___f_2443_);
v_sz_2445_ = lean_array_size(v_____do__lift_2441_);
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2439_, v_____do__lift_2441_, v___f_2444_, v_sz_2445_, v___x_2446_, v___x_2442_);
v___x_2448_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2447_, v___f_2440_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_){
_start:
{
lean_object* v_toApplicative_2452_; lean_object* v_toBind_2453_; lean_object* v_toPure_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; 
v_toApplicative_2452_ = lean_ctor_get(v_inst_2449_, 0);
v_toBind_2453_ = lean_ctor_get(v_inst_2449_, 1);
lean_inc(v_toBind_2453_);
v_toPure_2454_ = lean_ctor_get(v_toApplicative_2452_, 1);
lean_inc(v_toPure_2454_);
v___x_2455_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2456_ = lean_apply_2(v_inst_2451_, lean_box(0), v___x_2455_);
lean_inc(v_toPure_2454_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2457_, 0, v_toPure_2454_);
lean_inc(v_toBind_2453_);
v___f_2458_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2458_, 0, v_toPure_2454_);
lean_closure_set(v___f_2458_, 1, v_inst_2450_);
lean_closure_set(v___f_2458_, 2, v_toBind_2453_);
lean_closure_set(v___f_2458_, 3, v_inst_2449_);
lean_closure_set(v___f_2458_, 4, v___f_2457_);
v___x_2459_ = lean_apply_4(v_toBind_2453_, lean_box(0), lean_box(0), v___x_2456_, v___f_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_setDelimitsLocal___redArg(v_inst_2461_, v_inst_2462_, v_inst_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2465_, lean_object* v_namespaceName_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2465_, v_x_2467_, v_namespaceName_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2469_, lean_object* v_namespaceName_2470_, lean_object* v_toBind_2471_, lean_object* v___f_2472_, lean_object* v_a_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_modifyEnv_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_modifyEnv_2476_ = lean_ctor_get(v_inst_2469_, 1);
lean_inc(v_modifyEnv_2476_);
lean_dec_ref(v_inst_2469_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2477_, 0, v_a_2473_);
lean_closure_set(v___f_2477_, 1, v_namespaceName_2470_);
v___x_2478_ = lean_apply_1(v_modifyEnv_2476_, v___f_2477_);
v___x_2479_ = lean_apply_4(v_toBind_2471_, lean_box(0), lean_box(0), v___x_2478_, v___f_2472_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2480_, lean_object* v_inst_2481_, lean_object* v_namespaceName_2482_, lean_object* v_toBind_2483_, lean_object* v_inst_2484_, lean_object* v___f_2485_, lean_object* v_____do__lift_2486_){
_start:
{
lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; size_t v_sz_2490_; size_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2487_ = lean_box(0);
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2488_, 0, v___x_2487_);
lean_closure_set(v___f_2488_, 1, v_toPure_2480_);
lean_inc(v_toBind_2483_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2489_, 0, v_inst_2481_);
lean_closure_set(v___f_2489_, 1, v_namespaceName_2482_);
lean_closure_set(v___f_2489_, 2, v_toBind_2483_);
lean_closure_set(v___f_2489_, 3, v___f_2488_);
v_sz_2490_ = lean_array_size(v_____do__lift_2486_);
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2484_, v_____do__lift_2486_, v___f_2489_, v_sz_2490_, v___x_2491_, v___x_2487_);
v___x_2493_ = lean_apply_4(v_toBind_2483_, lean_box(0), lean_box(0), v___x_2492_, v___f_2485_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_namespaceName_2497_){
_start:
{
lean_object* v_toApplicative_2498_; lean_object* v_toBind_2499_; lean_object* v_toPure_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; 
v_toApplicative_2498_ = lean_ctor_get(v_inst_2494_, 0);
v_toBind_2499_ = lean_ctor_get(v_inst_2494_, 1);
lean_inc(v_toBind_2499_);
v_toPure_2500_ = lean_ctor_get(v_toApplicative_2498_, 1);
lean_inc(v_toPure_2500_);
v___x_2501_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2502_ = lean_apply_2(v_inst_2496_, lean_box(0), v___x_2501_);
lean_inc(v_toPure_2500_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2503_, 0, v_toPure_2500_);
lean_inc(v_toBind_2499_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2504_, 0, v_toPure_2500_);
lean_closure_set(v___f_2504_, 1, v_inst_2495_);
lean_closure_set(v___f_2504_, 2, v_namespaceName_2497_);
lean_closure_set(v___f_2504_, 3, v_toBind_2499_);
lean_closure_set(v___f_2504_, 4, v_inst_2494_);
lean_closure_set(v___f_2504_, 5, v___f_2503_);
v___x_2505_ = lean_apply_4(v_toBind_2499_, lean_box(0), lean_box(0), v___x_2502_, v___f_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_namespaceName_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_activateScoped___redArg(v_inst_2507_, v_inst_2508_, v_inst_2509_, v_namespaceName_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2513_){
_start:
{
lean_inc(v___y_2513_);
return v___y_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2514_);
lean_dec(v___y_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2516_, lean_object* v_a_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2517_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2521_, lean_object* v_a_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2521_, v_a_2522_, v___y_2523_);
lean_dec_ref(v___y_2523_);
lean_dec(v_x_2521_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_initial_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2534_){
_start:
{
lean_object* v_name_2536_; lean_object* v_addEntry_2537_; lean_object* v_initial_2538_; lean_object* v_finalizeImport_2539_; lean_object* v_exportEntry_x3f_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_name_2536_ = lean_ctor_get(v_descr_2534_, 0);
lean_inc(v_name_2536_);
v_addEntry_2537_ = lean_ctor_get(v_descr_2534_, 1);
lean_inc(v_addEntry_2537_);
v_initial_2538_ = lean_ctor_get(v_descr_2534_, 2);
lean_inc(v_initial_2538_);
v_finalizeImport_2539_ = lean_ctor_get(v_descr_2534_, 3);
lean_inc(v_finalizeImport_2539_);
v_exportEntry_x3f_2540_ = lean_ctor_get(v_descr_2534_, 4);
lean_inc_ref(v_exportEntry_x3f_2540_);
lean_dec_ref(v_descr_2534_);
v___f_2541_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2542_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2543_, 0, v_initial_2538_);
v___x_2544_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2544_, 0, v_name_2536_);
lean_ctor_set(v___x_2544_, 1, v___f_2543_);
lean_ctor_set(v___x_2544_, 2, v___f_2542_);
lean_ctor_set(v___x_2544_, 3, v___f_2541_);
lean_ctor_set(v___x_2544_, 4, v_addEntry_2537_);
lean_ctor_set(v___x_2544_, 5, v_finalizeImport_2539_);
lean_ctor_set(v___x_2544_, 6, v_exportEntry_x3f_2540_);
v___x_2545_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2546_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2549_, lean_object* v_00_u03c3_2550_, lean_object* v_descr_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2554_, lean_object* v_00_u03c3_2555_, lean_object* v_descr_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2554_, v_00_u03c3_2555_, v_descr_2556_);
return v_res_2558_;
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
