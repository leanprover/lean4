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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_317_; lean_object* v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v_j_322_; lean_object* v___x_323_; 
v_es_317_ = lean_ctor_get(v_x_314_, 0);
v___x_318_ = lean_box(2);
v___x_319_ = ((size_t)5ULL);
v___x_320_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_321_ = lean_usize_land(v_x_315_, v___x_320_);
v_j_322_ = lean_usize_to_nat(v___x_321_);
v___x_323_ = lean_array_get_borrowed(v___x_318_, v_es_317_, v_j_322_);
lean_dec(v_j_322_);
switch(lean_obj_tag(v___x_323_))
{
case 0:
{
lean_object* v_key_324_; lean_object* v_val_325_; uint8_t v___x_326_; 
v_key_324_ = lean_ctor_get(v___x_323_, 0);
v_val_325_ = lean_ctor_get(v___x_323_, 1);
v___x_326_ = lean_name_eq(v_x_316_, v_key_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(0);
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
lean_inc(v_val_325_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_val_325_);
return v___x_328_;
}
}
case 1:
{
lean_object* v_node_329_; size_t v___x_330_; 
v_node_329_ = lean_ctor_get(v___x_323_, 0);
v___x_330_ = lean_usize_shift_right(v_x_315_, v___x_319_);
v_x_314_ = v_node_329_;
v_x_315_ = v___x_330_;
goto _start;
}
default: 
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
}
else
{
lean_object* v_ks_333_; lean_object* v_vs_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_ks_333_ = lean_ctor_get(v_x_314_, 0);
v_vs_334_ = lean_ctor_get(v_x_314_, 1);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_333_, v_vs_334_, v___x_335_, v_x_316_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
size_t v_x_1076__boxed_340_; lean_object* v_res_341_; 
v_x_1076__boxed_340_ = lean_unbox_usize(v_x_338_);
lean_dec(v_x_338_);
v_res_341_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_337_, v_x_1076__boxed_340_, v_x_339_);
lean_dec(v_x_339_);
lean_dec_ref(v_x_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint64_t v___y_345_; 
if (lean_obj_tag(v_x_343_) == 0)
{
uint64_t v___x_348_; 
v___x_348_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_345_ = v___x_348_;
goto v___jp_344_;
}
else
{
uint64_t v_hash_349_; 
v_hash_349_ = lean_ctor_get_uint64(v_x_343_, sizeof(void*)*2);
v___y_345_ = v_hash_349_;
goto v___jp_344_;
}
v___jp_344_:
{
size_t v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_uint64_to_usize(v___y_345_);
v___x_347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_342_, v___x_346_, v_x_343_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec_ref(v_x_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_stage_u2081_355_; 
v_stage_u2081_355_ = lean_ctor_get_uint8(v_x_353_, sizeof(void*)*2);
if (v_stage_u2081_355_ == 0)
{
lean_object* v_map_u2081_356_; lean_object* v_map_u2082_357_; lean_object* v___x_358_; 
v_map_u2081_356_ = lean_ctor_get(v_x_353_, 0);
v_map_u2082_357_ = lean_ctor_get(v_x_353_, 1);
v___x_358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_357_, v_x_354_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_356_, v_x_354_);
return v___x_359_;
}
else
{
return v___x_358_;
}
}
else
{
lean_object* v_map_u2081_360_; lean_object* v___x_361_; 
v_map_u2081_360_ = lean_ctor_get(v_x_353_, 0);
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_360_, v_x_354_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec_ref(v_x_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_365_, lean_object* v_b_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_dec(v_b_366_);
lean_dec(v_a_365_);
return v_x_367_;
}
else
{
lean_object* v_key_368_; lean_object* v_value_369_; lean_object* v_tail_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
v_key_368_ = lean_ctor_get(v_x_367_, 0);
v_value_369_ = lean_ctor_get(v_x_367_, 1);
v_tail_370_ = lean_ctor_get(v_x_367_, 2);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_367_);
if (v_isSharedCheck_382_ == 0)
{
v___x_372_ = v_x_367_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_tail_370_);
lean_inc(v_value_369_);
lean_inc(v_key_368_);
lean_dec(v_x_367_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_name_eq(v_key_368_, v_a_365_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_365_, v_b_366_, v_tail_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 2, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_key_368_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_value_369_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
else
{
lean_object* v___x_380_; 
lean_dec(v_value_369_);
lean_dec(v_key_368_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v_b_366_);
lean_ctor_set(v___x_372_, 0, v_a_365_);
v___x_380_ = v___x_372_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_365_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_b_366_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_tail_370_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
return v_x_383_;
}
else
{
lean_object* v_key_385_; lean_object* v_value_386_; lean_object* v_tail_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_413_; 
v_key_385_ = lean_ctor_get(v_x_384_, 0);
v_value_386_ = lean_ctor_get(v_x_384_, 1);
v_tail_387_ = lean_ctor_get(v_x_384_, 2);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_413_ == 0)
{
v___x_389_ = v_x_384_;
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_tail_387_);
lean_inc(v_value_386_);
lean_inc(v_key_385_);
lean_dec(v_x_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; uint64_t v___y_393_; 
v___x_391_ = lean_array_get_size(v_x_383_);
if (lean_obj_tag(v_key_385_) == 0)
{
uint64_t v___x_411_; 
v___x_411_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_393_ = v___x_411_;
goto v___jp_392_;
}
else
{
uint64_t v_hash_412_; 
v_hash_412_ = lean_ctor_get_uint64(v_key_385_, sizeof(void*)*2);
v___y_393_ = v_hash_412_;
goto v___jp_392_;
}
v___jp_392_:
{
uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v_fold_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_394_ = 32ULL;
v___x_395_ = lean_uint64_shift_right(v___y_393_, v___x_394_);
v_fold_396_ = lean_uint64_xor(v___y_393_, v___x_395_);
v___x_397_ = 16ULL;
v___x_398_ = lean_uint64_shift_right(v_fold_396_, v___x_397_);
v___x_399_ = lean_uint64_xor(v_fold_396_, v___x_398_);
v___x_400_ = lean_uint64_to_usize(v___x_399_);
v___x_401_ = lean_usize_of_nat(v___x_391_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_sub(v___x_401_, v___x_402_);
v___x_404_ = lean_usize_land(v___x_400_, v___x_403_);
v___x_405_ = lean_array_uget_borrowed(v_x_383_, v___x_404_);
lean_inc(v___x_405_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 2, v___x_405_);
v___x_407_ = v___x_389_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_key_385_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_value_386_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v___x_405_);
v___x_407_ = v_reuseFailAlloc_410_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; 
v___x_408_ = lean_array_uset(v_x_383_, v___x_404_, v___x_407_);
v_x_383_ = v___x_408_;
v_x_384_ = v_tail_387_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_414_, lean_object* v_source_415_, lean_object* v_target_416_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_array_get_size(v_source_415_);
v___x_418_ = lean_nat_dec_lt(v_i_414_, v___x_417_);
if (v___x_418_ == 0)
{
lean_dec_ref(v_source_415_);
lean_dec(v_i_414_);
return v_target_416_;
}
else
{
lean_object* v_es_419_; lean_object* v___x_420_; lean_object* v_source_421_; lean_object* v_target_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_es_419_ = lean_array_fget(v_source_415_, v_i_414_);
v___x_420_ = lean_box(0);
v_source_421_ = lean_array_fset(v_source_415_, v_i_414_, v___x_420_);
v_target_422_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_416_, v_es_419_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_add(v_i_414_, v___x_423_);
lean_dec(v_i_414_);
v_i_414_ = v___x_424_;
v_source_415_ = v_source_421_;
v_target_416_ = v_target_422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_nbuckets_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_427_ = lean_array_get_size(v_data_426_);
v___x_428_ = lean_unsigned_to_nat(2u);
v_nbuckets_429_ = lean_nat_mul(v___x_427_, v___x_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_box(0);
v___x_432_ = lean_mk_array(v_nbuckets_429_, v___x_431_);
v___x_433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_430_, v_data_426_, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
else
{
lean_object* v_key_437_; lean_object* v_tail_438_; uint8_t v___x_439_; 
v_key_437_ = lean_ctor_get(v_x_435_, 0);
v_tail_438_ = lean_ctor_get(v_x_435_, 2);
v___x_439_ = lean_name_eq(v_key_437_, v_a_434_);
if (v___x_439_ == 0)
{
v_x_435_ = v_tail_438_;
goto _start;
}
else
{
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_441_, v_x_442_);
lean_dec(v_x_442_);
lean_dec(v_a_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_size_448_; lean_object* v_buckets_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_495_; 
v_size_448_ = lean_ctor_get(v_m_445_, 0);
v_buckets_449_ = lean_ctor_get(v_m_445_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_m_445_);
if (v_isSharedCheck_495_ == 0)
{
v___x_451_ = v_m_445_;
v_isShared_452_ = v_isSharedCheck_495_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_buckets_449_);
lean_inc(v_size_448_);
lean_dec(v_m_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_495_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint64_t v___y_455_; 
v___x_453_ = lean_array_get_size(v_buckets_449_);
if (lean_obj_tag(v_a_446_) == 0)
{
uint64_t v___x_493_; 
v___x_493_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_455_ = v___x_493_;
goto v___jp_454_;
}
else
{
uint64_t v_hash_494_; 
v_hash_494_ = lean_ctor_get_uint64(v_a_446_, sizeof(void*)*2);
v___y_455_ = v_hash_494_;
goto v___jp_454_;
}
v___jp_454_:
{
uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v_fold_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v_bkt_467_; uint8_t v___x_468_; 
v___x_456_ = 32ULL;
v___x_457_ = lean_uint64_shift_right(v___y_455_, v___x_456_);
v_fold_458_ = lean_uint64_xor(v___y_455_, v___x_457_);
v___x_459_ = 16ULL;
v___x_460_ = lean_uint64_shift_right(v_fold_458_, v___x_459_);
v___x_461_ = lean_uint64_xor(v_fold_458_, v___x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = lean_usize_of_nat(v___x_453_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_sub(v___x_463_, v___x_464_);
v___x_466_ = lean_usize_land(v___x_462_, v___x_465_);
v_bkt_467_ = lean_array_uget_borrowed(v_buckets_449_, v___x_466_);
v___x_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_446_, v_bkt_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v_size_x27_470_; lean_object* v___x_471_; lean_object* v_buckets_x27_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v_size_x27_470_ = lean_nat_add(v_size_448_, v___x_469_);
lean_dec(v_size_448_);
lean_inc(v_bkt_467_);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v_a_446_);
lean_ctor_set(v___x_471_, 1, v_b_447_);
lean_ctor_set(v___x_471_, 2, v_bkt_467_);
v_buckets_x27_472_ = lean_array_uset(v_buckets_449_, v___x_466_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(4u);
v___x_474_ = lean_nat_mul(v_size_x27_470_, v___x_473_);
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_nat_div(v___x_474_, v___x_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_array_get_size(v_buckets_x27_472_);
v___x_478_ = lean_nat_dec_le(v___x_476_, v___x_477_);
lean_dec(v___x_476_);
if (v___x_478_ == 0)
{
lean_object* v_val_479_; lean_object* v___x_481_; 
v_val_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_472_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_val_479_);
lean_ctor_set(v___x_451_, 0, v_size_x27_470_);
v___x_481_ = v___x_451_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_size_x27_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_val_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_484_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v_buckets_x27_472_);
lean_ctor_set(v___x_451_, 0, v_size_x27_470_);
v___x_484_ = v___x_451_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_size_x27_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_buckets_x27_472_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v___x_486_; lean_object* v_buckets_x27_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
lean_inc(v_bkt_467_);
v___x_486_ = lean_box(0);
v_buckets_x27_487_ = lean_array_uset(v_buckets_449_, v___x_466_, v___x_486_);
v___x_488_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_446_, v_b_447_, v_bkt_467_);
v___x_489_ = lean_array_uset(v_buckets_x27_487_, v___x_466_, v___x_488_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_489_);
v___x_491_ = v___x_451_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_448_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_ks_500_; lean_object* v_vs_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_525_; 
v_ks_500_ = lean_ctor_get(v_x_496_, 0);
v_vs_501_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_525_ == 0)
{
v___x_503_ = v_x_496_;
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_vs_501_);
lean_inc(v_ks_500_);
lean_dec(v_x_496_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_get_size(v_ks_500_);
v___x_506_ = lean_nat_dec_lt(v_x_497_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_x_497_);
v___x_507_ = lean_array_push(v_ks_500_, v_x_498_);
v___x_508_ = lean_array_push(v_vs_501_, v_x_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_k_x27_512_; uint8_t v___x_513_; 
v_k_x27_512_ = lean_array_fget_borrowed(v_ks_500_, v_x_497_);
v___x_513_ = lean_name_eq(v_x_498_, v_k_x27_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_515_; 
if (v_isShared_504_ == 0)
{
v___x_515_ = v___x_503_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_ks_500_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_vs_501_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_x_497_, v___x_516_);
lean_dec(v_x_497_);
v_x_496_ = v___x_515_;
v_x_497_ = v___x_517_;
goto _start;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_array_fset(v_ks_500_, v_x_497_, v_x_498_);
v___x_521_ = lean_array_fset(v_vs_501_, v_x_497_, v_x_499_);
lean_dec(v_x_497_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_521_);
lean_ctor_set(v___x_503_, 0, v___x_520_);
v___x_523_ = v___x_503_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_526_, lean_object* v_k_527_, lean_object* v_v_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_526_, v___x_529_, v_k_527_, v_v_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_532_, size_t v_x_533_, size_t v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_es_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v_j_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_es_537_ = lean_ctor_get(v_x_532_, 0);
v___x_538_ = ((size_t)5ULL);
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_541_ = lean_usize_land(v_x_533_, v___x_540_);
v_j_542_ = lean_usize_to_nat(v___x_541_);
v___x_543_ = lean_array_get_size(v_es_537_);
v___x_544_ = lean_nat_dec_lt(v_j_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec(v_j_542_);
lean_dec(v_x_536_);
lean_dec(v_x_535_);
return v_x_532_;
}
else
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_537_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_532_, 0);
lean_dec(v_unused_582_);
v___x_546_ = v_x_532_;
v_isShared_547_ = v_isSharedCheck_581_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_x_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_581_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_v_548_; lean_object* v___x_549_; lean_object* v_xs_x27_550_; lean_object* v___y_552_; 
v_v_548_ = lean_array_fget(v_es_537_, v_j_542_);
v___x_549_ = lean_box(0);
v_xs_x27_550_ = lean_array_fset(v_es_537_, v_j_542_, v___x_549_);
switch(lean_obj_tag(v_v_548_))
{
case 0:
{
lean_object* v_key_557_; lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_key_557_ = lean_ctor_get(v_v_548_, 0);
v_val_558_ = lean_ctor_get(v_v_548_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_v_548_);
if (v_isSharedCheck_568_ == 0)
{
v___x_560_ = v_v_548_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_inc(v_key_557_);
lean_dec(v_v_548_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; 
v___x_562_ = lean_name_eq(v_x_535_, v_key_557_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_560_);
v___x_563_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_557_, v_val_558_, v_x_535_, v_x_536_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___y_552_ = v___x_564_;
goto v___jp_551_;
}
else
{
lean_object* v___x_566_; 
lean_dec(v_val_558_);
lean_dec(v_key_557_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_x_536_);
lean_ctor_set(v___x_560_, 0, v_x_535_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_x_535_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_x_536_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v___y_552_ = v___x_566_;
goto v___jp_551_;
}
}
}
}
case 1:
{
lean_object* v_node_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_node_569_ = lean_ctor_get(v_v_548_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_548_);
if (v_isSharedCheck_579_ == 0)
{
v___x_571_ = v_v_548_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_node_569_);
lean_dec(v_v_548_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_573_ = lean_usize_shift_right(v_x_533_, v___x_538_);
v___x_574_ = lean_usize_add(v_x_534_, v___x_539_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_569_, v___x_573_, v___x_574_, v_x_535_, v_x_536_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_552_ = v___x_577_;
goto v___jp_551_;
}
}
}
default: 
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_535_);
lean_ctor_set(v___x_580_, 1, v_x_536_);
v___y_552_ = v___x_580_;
goto v___jp_551_;
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_array_fset(v_xs_x27_550_, v_j_542_, v___y_552_);
lean_dec(v_j_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_553_);
v___x_555_ = v___x_546_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_ks_583_ = lean_ctor_get(v_x_532_, 0);
v_vs_584_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v_x_532_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_532_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_ks_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_vs_584_);
v___x_589_ = v_reuseFailAlloc_603_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v_newNode_590_; uint8_t v___y_592_; size_t v___x_598_; uint8_t v___x_599_; 
v_newNode_590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_589_, v_x_535_, v_x_536_);
v___x_598_ = ((size_t)7ULL);
v___x_599_ = lean_usize_dec_le(v___x_598_, v_x_534_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_590_);
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_599_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_ks_593_ = lean_ctor_get(v_newNode_590_, 0);
lean_inc_ref(v_ks_593_);
v_vs_594_ = lean_ctor_get(v_newNode_590_, 1);
lean_inc_ref(v_vs_594_);
lean_dec_ref(v_newNode_590_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_534_, v_ks_593_, v_vs_594_, v___x_595_, v___x_596_);
lean_dec_ref(v_vs_594_);
lean_dec_ref(v_ks_593_);
return v___x_597_;
}
else
{
return v_newNode_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_i_608_, lean_object* v_entries_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v_entries_609_;
}
else
{
lean_object* v_k_612_; lean_object* v_v_613_; uint64_t v___y_615_; 
v_k_612_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v_v_613_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
if (lean_obj_tag(v_k_612_) == 0)
{
uint64_t v___x_626_; 
v___x_626_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_615_ = v___x_626_;
goto v___jp_614_;
}
else
{
uint64_t v_hash_627_; 
v_hash_627_ = lean_ctor_get_uint64(v_k_612_, sizeof(void*)*2);
v___y_615_ = v_hash_627_;
goto v___jp_614_;
}
v___jp_614_:
{
size_t v_h_616_; size_t v___x_617_; lean_object* v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v_h_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_h_616_ = lean_uint64_to_usize(v___y_615_);
v___x_617_ = ((size_t)5ULL);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_sub(v_depth_605_, v___x_619_);
v___x_621_ = lean_usize_mul(v___x_617_, v___x_620_);
v_h_622_ = lean_usize_shift_right(v_h_616_, v___x_621_);
v___x_623_ = lean_nat_add(v_i_608_, v___x_618_);
lean_dec(v_i_608_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
v___x_624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_609_, v_h_622_, v_depth_605_, v_k_612_, v_v_613_);
v_i_608_ = v___x_623_;
v_entries_609_ = v___x_624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_628_, lean_object* v_keys_629_, lean_object* v_vals_630_, lean_object* v_i_631_, lean_object* v_entries_632_){
_start:
{
size_t v_depth_boxed_633_; lean_object* v_res_634_; 
v_depth_boxed_633_ = lean_unbox_usize(v_depth_628_);
lean_dec(v_depth_628_);
v_res_634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_633_, v_keys_629_, v_vals_630_, v_i_631_, v_entries_632_);
lean_dec_ref(v_vals_630_);
lean_dec_ref(v_keys_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_1474__boxed_640_; size_t v_x_1475__boxed_641_; lean_object* v_res_642_; 
v_x_1474__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_x_1475__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_635_, v_x_1474__boxed_640_, v_x_1475__boxed_641_, v_x_638_, v_x_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint64_t v___y_647_; 
if (lean_obj_tag(v_x_644_) == 0)
{
uint64_t v___x_651_; 
v___x_651_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_647_ = v___x_651_;
goto v___jp_646_;
}
else
{
uint64_t v_hash_652_; 
v_hash_652_ = lean_ctor_get_uint64(v_x_644_, sizeof(void*)*2);
v___y_647_ = v_hash_652_;
goto v___jp_646_;
}
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_uint64_to_usize(v___y_647_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_643_, v___x_648_, v___x_649_, v_x_644_, v_x_645_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
uint8_t v_stage_u2081_656_; 
v_stage_u2081_656_ = lean_ctor_get_uint8(v_x_653_, sizeof(void*)*2);
if (v_stage_u2081_656_ == 0)
{
lean_object* v_map_u2081_657_; lean_object* v_map_u2082_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_map_u2081_657_ = lean_ctor_get(v_x_653_, 0);
v_map_u2082_658_ = lean_ctor_get(v_x_653_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v_x_653_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_map_u2082_658_);
lean_inc(v_map_u2081_657_);
lean_dec(v_x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_658_, v_x_654_, v_x_655_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_map_u2081_657_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_665_, sizeof(void*)*2, v_stage_u2081_656_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_map_u2081_667_; lean_object* v_map_u2082_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_map_u2081_667_ = lean_ctor_get(v_x_653_, 0);
v_map_u2082_668_ = lean_ctor_get(v_x_653_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_676_ == 0)
{
v___x_670_ = v_x_653_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_map_u2082_668_);
lean_inc(v_map_u2081_667_);
lean_dec(v_x_653_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_667_, v_x_654_, v_x_655_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_map_u2082_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*2, v_stage_u2081_656_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(32u);
v___x_678_ = lean_mk_empty_array_with_capacity(v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = ((size_t)5ULL);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_unsigned_to_nat(32u);
v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
v___x_684_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_685_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_681_);
lean_ctor_set(v___x_685_, 3, v___x_681_);
lean_ctor_set_usize(v___x_685_, 4, v___x_680_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_686_, lean_object* v_ns_687_, lean_object* v_b_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_686_, v_ns_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_691_ = l_Lean_PersistentArray_push___redArg(v___x_690_, v_b_688_);
v___x_692_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_686_, v_ns_687_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_val_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_val_693_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v___x_689_);
v___x_694_ = l_Lean_PersistentArray_push___redArg(v_val_693_, v_b_688_);
v___x_695_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_686_, v_ns_687_, v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_696_, lean_object* v_scopedEntries_697_, lean_object* v_ns_698_, lean_object* v_b_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_697_, v_ns_698_, v_b_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_702_, v_x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_705_, v_x_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_x_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_710_, v_x_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_718_, v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_722_, lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_723_, v_a_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_726_, lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_726_, v_m_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_m_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_731_, v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_735_, lean_object* v_m_736_, lean_object* v_a_737_, lean_object* v_b_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_736_, v_a_737_, v_b_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, size_t v_x_742_, lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_741_, v_x_742_, v_x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
size_t v_x_1782__boxed_749_; lean_object* v_res_750_; 
v_x_1782__boxed_749_ = lean_unbox_usize(v_x_747_);
lean_dec(v_x_747_);
v_res_750_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_745_, v_x_746_, v_x_1782__boxed_749_, v_x_748_);
lean_dec(v_x_748_);
lean_dec_ref(v_x_746_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_751_, lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_755_, lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_755_, v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, size_t v_x_761_, size_t v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_760_, v_x_761_, v_x_762_, v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
size_t v_x_1798__boxed_772_; size_t v_x_1799__boxed_773_; lean_object* v_res_774_; 
v_x_1798__boxed_772_ = lean_unbox_usize(v_x_768_);
lean_dec(v_x_768_);
v_x_1799__boxed_773_ = lean_unbox_usize(v_x_769_);
lean_dec(v_x_769_);
v_res_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_766_, v_x_767_, v_x_1798__boxed_772_, v_x_1799__boxed_773_, v_x_770_, v_x_771_);
return v_res_774_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_775_, lean_object* v_a_776_, lean_object* v_x_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_779_, lean_object* v_a_780_, lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_779_, v_a_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec(v_a_780_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_784_, lean_object* v_data_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_787_, lean_object* v_a_788_, lean_object* v_b_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_788_, v_b_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_792_, lean_object* v_keys_793_, lean_object* v_vals_794_, lean_object* v_heq_795_, lean_object* v_i_796_, lean_object* v_k_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_793_, v_vals_794_, v_i_796_, v_k_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_799_, lean_object* v_keys_800_, lean_object* v_vals_801_, lean_object* v_heq_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_799_, v_keys_800_, v_vals_801_, v_heq_802_, v_i_803_, v_k_804_);
lean_dec(v_k_804_);
lean_dec_ref(v_vals_801_);
lean_dec_ref(v_keys_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_806_, lean_object* v_n_807_, lean_object* v_k_808_, lean_object* v_v_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_807_, v_k_808_, v_v_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_811_, size_t v_depth_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_heq_815_, lean_object* v_i_816_, lean_object* v_entries_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_812_, v_keys_813_, v_vals_814_, v_i_816_, v_entries_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_819_, lean_object* v_depth_820_, lean_object* v_keys_821_, lean_object* v_vals_822_, lean_object* v_heq_823_, lean_object* v_i_824_, lean_object* v_entries_825_){
_start:
{
size_t v_depth_boxed_826_; lean_object* v_res_827_; 
v_depth_boxed_826_ = lean_unbox_usize(v_depth_820_);
lean_dec(v_depth_820_);
v_res_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_819_, v_depth_boxed_826_, v_keys_821_, v_vals_822_, v_heq_823_, v_i_824_, v_entries_825_);
lean_dec_ref(v_vals_822_);
lean_dec_ref(v_keys_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_828_, lean_object* v_i_829_, lean_object* v_source_830_, lean_object* v_target_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_829_, v_source_830_, v_target_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_843_, lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_a_851_; uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v_descr_843_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_847_);
return v___x_856_;
}
else
{
lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_897_; 
v_fst_857_ = lean_ctor_get(v_b_847_, 0);
v_snd_858_ = lean_ctor_get(v_b_847_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_b_847_);
if (v_isSharedCheck_897_ == 0)
{
v___x_860_ = v_b_847_;
v_isShared_861_ = v_isSharedCheck_897_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_snd_858_);
lean_inc(v_fst_857_);
lean_dec(v_b_847_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_897_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_a_862_; 
v_a_862_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
if (lean_obj_tag(v_a_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_ofOLeanEntry_864_; lean_object* v_addEntry_865_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v_a_862_, 0);
v_ofOLeanEntry_864_ = lean_ctor_get(v_descr_843_, 2);
v_addEntry_865_ = lean_ctor_get(v_descr_843_, 4);
lean_inc_ref(v_ofOLeanEntry_864_);
lean_inc_ref(v___y_848_);
lean_inc(v_a_863_);
lean_inc(v_fst_857_);
v___x_866_ = lean_apply_4(v_ofOLeanEntry_864_, v_fst_857_, v_a_863_, v___y_848_, lean_box(0));
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
lean_inc(v_addEntry_865_);
v___x_868_ = lean_apply_2(v_addEntry_865_, v_fst_857_, v_a_867_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_868_);
v___x_870_ = v___x_860_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_858_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_851_ = v___x_870_;
goto v___jp_850_;
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_del_object(v___x_860_);
lean_dec(v_snd_858_);
lean_dec(v_fst_857_);
lean_dec_ref(v_descr_843_);
v_a_872_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_866_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_866_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v_a_881_; lean_object* v_ofOLeanEntry_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v_a_862_, 0);
v_a_881_ = lean_ctor_get(v_a_862_, 1);
v_ofOLeanEntry_882_ = lean_ctor_get(v_descr_843_, 2);
lean_inc_ref(v_ofOLeanEntry_882_);
lean_inc_ref(v___y_848_);
lean_inc(v_a_881_);
lean_inc(v_fst_857_);
v___x_883_ = lean_apply_4(v_ofOLeanEntry_882_, v_fst_857_, v_a_881_, v___y_848_, lean_box(0));
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
lean_inc(v_a_880_);
v___x_885_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_858_, v_a_880_, v_a_884_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_885_);
v___x_887_ = v___x_860_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_857_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
v_a_851_ = v___x_887_;
goto v___jp_850_;
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_860_);
lean_dec(v_snd_858_);
lean_dec(v_fst_857_);
lean_dec_ref(v_descr_843_);
v_a_889_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_883_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_883_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
v___jp_850_:
{
size_t v___x_852_; size_t v___x_853_; 
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_846_, v___x_852_);
v_i_846_ = v___x_853_;
v_b_847_ = v_a_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_898_, lean_object* v_as_899_, lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
size_t v_sz_boxed_905_; size_t v_i_boxed_906_; lean_object* v_res_907_; 
v_sz_boxed_905_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_906_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_898_, v_as_899_, v_sz_boxed_905_, v_i_boxed_906_, v_b_902_, v___y_903_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v_as_899_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_908_, lean_object* v_as_909_, size_t v_sz_910_, size_t v_i_911_, lean_object* v_b_912_, lean_object* v___y_913_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_lt(v_i_911_, v_sz_910_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec_ref(v_descr_908_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v_b_912_);
return v___x_916_;
}
else
{
lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_942_; 
v_fst_917_ = lean_ctor_get(v_b_912_, 0);
v_snd_918_ = lean_ctor_get(v_b_912_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_b_912_);
if (v_isSharedCheck_942_ == 0)
{
v___x_920_ = v_b_912_;
v_isShared_921_ = v_isSharedCheck_942_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_snd_918_);
lean_inc(v_fst_917_);
lean_dec(v_b_912_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_942_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_a_922_; lean_object* v___x_924_; 
v_a_922_ = lean_array_uget_borrowed(v_as_909_, v_i_911_);
if (v_isShared_921_ == 0)
{
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_fst_917_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_snd_918_);
v___x_924_ = v_reuseFailAlloc_941_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
size_t v_sz_925_; size_t v___x_926_; lean_object* v___x_927_; 
v_sz_925_ = lean_array_size(v_a_922_);
v___x_926_ = ((size_t)0ULL);
lean_inc_ref(v_descr_908_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_908_, v_a_922_, v_sz_925_, v___x_926_, v___x_924_, v___y_913_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
v_fst_929_ = lean_ctor_get(v_a_928_, 0);
v_snd_930_ = lean_ctor_get(v_a_928_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_940_ == 0)
{
v___x_932_ = v_a_928_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snd_930_);
lean_inc(v_fst_929_);
lean_dec(v_a_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_fst_929_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_snd_930_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
size_t v___x_936_; size_t v___x_937_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_911_, v___x_936_);
v_i_911_ = v___x_937_;
v_b_912_ = v___x_935_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_908_);
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_943_, lean_object* v_as_944_, lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_951_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_943_, v_as_944_, v_sz_boxed_950_, v_i_boxed_951_, v_b_947_, v___y_948_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_as_944_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_953_, lean_object* v_as_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_mkInitial_957_; lean_object* v_finalizeImport_958_; lean_object* v___x_959_; 
v_mkInitial_957_ = lean_ctor_get(v_descr_953_, 1);
v_finalizeImport_958_ = lean_ctor_get(v_descr_953_, 5);
lean_inc(v_finalizeImport_958_);
lean_inc_ref(v_mkInitial_957_);
v___x_959_ = lean_apply_1(v_mkInitial_957_, lean_box(0));
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = 1;
v___x_962_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_a_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v_sz_964_ = lean_array_size(v_as_954_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_953_, v_as_954_, v_sz_964_, v___x_965_, v___x_963_, v_a_955_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_988_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_988_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_988_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_988_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_fst_971_; lean_object* v_snd_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_987_; 
v_fst_971_ = lean_ctor_get(v_a_967_, 0);
v_snd_972_ = lean_ctor_get(v_a_967_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_987_ == 0)
{
v___x_974_ = v_a_967_;
v_isShared_975_ = v_isSharedCheck_987_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_972_);
lean_inc(v_fst_971_);
lean_dec(v_a_967_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_987_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_976_ = lean_apply_1(v_finalizeImport_958_, v_fst_971_);
v___x_977_ = l_Lean_NameSet_empty;
v___x_978_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*2, v___x_961_);
v___x_979_ = lean_box(0);
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 1, v___x_979_);
lean_ctor_set(v___x_974_, 0, v___x_978_);
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_986_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_snd_972_);
lean_ctor_set(v___x_982_, 2, v___x_979_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_982_);
v___x_984_ = v___x_969_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_finalizeImport_958_);
v_a_989_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_966_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_966_);
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
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_finalizeImport_958_);
lean_dec_ref(v_descr_953_);
v_a_997_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_959_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_959_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1005_, lean_object* v_as_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1005_, v_as_1006_, v_a_1007_);
lean_dec_ref(v_a_1007_);
lean_dec_ref(v_as_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_00_u03c3_1012_, lean_object* v_descr_1013_, lean_object* v_as_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1013_, v_as_1014_, v_a_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_00_u03c3_1020_, lean_object* v_descr_1021_, lean_object* v_as_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1018_, v_00_u03b2_1019_, v_00_u03c3_1020_, v_descr_1021_, v_as_1022_, v_a_1023_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_as_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03c3_1027_, lean_object* v_00_u03b2_1028_, lean_object* v_descr_1029_, lean_object* v_as_1030_, size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1029_, v_as_1030_, v_sz_1031_, v_i_1032_, v_b_1033_, v___y_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_00_u03c3_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_descr_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_sz_boxed_1047_; size_t v_i_boxed_1048_; lean_object* v_res_1049_; 
v_sz_boxed_1047_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1048_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1037_, v_00_u03c3_1038_, v_00_u03b2_1039_, v_descr_1040_, v_as_1041_, v_sz_boxed_1047_, v_i_boxed_1048_, v_b_1044_, v___y_1045_);
lean_dec_ref(v___y_1045_);
lean_dec_ref(v_as_1041_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03c3_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_descr_1053_, lean_object* v_as_1054_, size_t v_sz_1055_, size_t v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1053_, v_as_1054_, v_sz_1055_, v_i_1056_, v_b_1057_, v___y_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03c3_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_descr_1064_, lean_object* v_as_1065_, lean_object* v_sz_1066_, lean_object* v_i_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1066_);
lean_dec(v_sz_1066_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1067_);
lean_dec(v_i_1067_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1061_, v_00_u03c3_1062_, v_00_u03b2_1063_, v_descr_1064_, v_as_1065_, v_sz_boxed_1071_, v_i_boxed_1072_, v_b_1068_, v___y_1069_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_as_1065_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1074_, lean_object* v_descr_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
if (lean_obj_tag(v_a_1077_) == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_a_1076_);
lean_dec_ref(v_descr_1075_);
v___x_1079_ = l_List_reverse___redArg(v_a_1078_);
return v___x_1079_;
}
else
{
lean_object* v_head_1080_; lean_object* v_tail_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1106_; 
v_head_1080_ = lean_ctor_get(v_a_1077_, 0);
v_tail_1081_ = lean_ctor_get(v_a_1077_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1083_ = v_a_1077_;
v_isShared_1084_ = v_isSharedCheck_1106_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_tail_1081_);
lean_inc(v_head_1080_);
lean_dec(v_a_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1106_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___y_1086_; lean_object* v_state_1091_; lean_object* v_activeScopes_1092_; uint8_t v_delimitsLocal_1093_; uint8_t v___x_1094_; 
v_state_1091_ = lean_ctor_get(v_head_1080_, 0);
v_activeScopes_1092_ = lean_ctor_get(v_head_1080_, 1);
v_delimitsLocal_1093_ = lean_ctor_get_uint8(v_head_1080_, sizeof(void*)*2);
v___x_1094_ = l_Lean_NameSet_contains(v_activeScopes_1092_, v_a_1074_);
if (v___x_1094_ == 0)
{
v___y_1086_ = v_head_1080_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1103_; 
lean_inc(v_activeScopes_1092_);
lean_inc(v_state_1091_);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_head_1080_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1104_ = lean_ctor_get(v_head_1080_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_head_1080_, 0);
lean_dec(v_unused_1105_);
v___x_1096_ = v_head_1080_;
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v_head_1080_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_addEntry_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_addEntry_1098_ = lean_ctor_get(v_descr_1075_, 4);
lean_inc(v_addEntry_1098_);
lean_inc(v_a_1076_);
v___x_1099_ = lean_apply_2(v_addEntry_1098_, v_state_1091_, v_a_1076_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_activeScopes_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*2, v_delimitsLocal_1093_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
v___y_1086_ = v___x_1101_;
goto v___jp_1085_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_a_1078_);
lean_ctor_set(v___x_1083_, 0, v___y_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___y_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_a_1078_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v_a_1077_ = v_tail_1081_;
v_a_1078_ = v___x_1088_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1107_, lean_object* v_descr_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1107_, v_descr_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
if (lean_obj_tag(v_a_1115_) == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_a_1114_);
lean_dec_ref(v_descr_1113_);
v___x_1117_ = l_List_reverse___redArg(v_a_1116_);
return v___x_1117_;
}
else
{
lean_object* v_head_1118_; lean_object* v_tail_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1139_; 
v_head_1118_ = lean_ctor_get(v_a_1115_, 0);
v_tail_1119_ = lean_ctor_get(v_a_1115_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_a_1115_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1121_ = v_a_1115_;
v_isShared_1122_ = v_isSharedCheck_1139_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_tail_1119_);
lean_inc(v_head_1118_);
lean_dec(v_a_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1139_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_addEntry_1123_; lean_object* v_state_1124_; lean_object* v_activeScopes_1125_; uint8_t v_delimitsLocal_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1138_; 
v_addEntry_1123_ = lean_ctor_get(v_descr_1113_, 4);
v_state_1124_ = lean_ctor_get(v_head_1118_, 0);
v_activeScopes_1125_ = lean_ctor_get(v_head_1118_, 1);
v_delimitsLocal_1126_ = lean_ctor_get_uint8(v_head_1118_, sizeof(void*)*2);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_head_1118_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1128_ = v_head_1118_;
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_activeScopes_1125_);
lean_inc(v_state_1124_);
lean_dec(v_head_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1138_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_inc(v_addEntry_1123_);
lean_inc(v_a_1114_);
v___x_1130_ = lean_apply_2(v_addEntry_1123_, v_state_1124_, v_a_1114_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_activeScopes_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*2, v_delimitsLocal_1126_);
v___x_1132_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_a_1116_);
lean_ctor_set(v___x_1121_, 0, v___x_1132_);
v___x_1134_ = v___x_1121_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_a_1116_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v_a_1115_ = v_tail_1119_;
v_a_1116_ = v___x_1134_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1140_, lean_object* v_s_1141_, lean_object* v_e_1142_){
_start:
{
if (lean_obj_tag(v_e_1142_) == 0)
{
lean_object* v_stateStack_1143_; lean_object* v_scopedEntries_1144_; lean_object* v_newEntries_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1165_; 
v_stateStack_1143_ = lean_ctor_get(v_s_1141_, 0);
v_scopedEntries_1144_ = lean_ctor_get(v_s_1141_, 1);
v_newEntries_1145_ = lean_ctor_get(v_s_1141_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_s_1141_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1147_ = v_s_1141_;
v_isShared_1148_ = v_isSharedCheck_1165_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_newEntries_1145_);
lean_inc(v_scopedEntries_1144_);
lean_inc(v_stateStack_1143_);
lean_dec(v_s_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1165_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1164_; 
v_a_1149_ = lean_ctor_get(v_e_1142_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_e_1142_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1151_ = v_e_1142_;
v_isShared_1152_ = v_isSharedCheck_1164_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_e_1142_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1164_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_toOLeanEntry_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v_toOLeanEntry_1153_ = lean_ctor_get(v_descr_1140_, 3);
lean_inc(v_toOLeanEntry_1153_);
v___x_1154_ = lean_box(0);
lean_inc(v_a_1149_);
v___x_1155_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1140_, v_a_1149_, v_stateStack_1143_, v___x_1154_);
v___x_1156_ = lean_apply_1(v_toOLeanEntry_1153_, v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1156_);
v___x_1158_ = v___x_1151_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v_newEntries_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 2, v___x_1159_);
lean_ctor_set(v___x_1147_, 0, v___x_1155_);
v___x_1161_ = v___x_1147_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_scopedEntries_1144_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1166_; lean_object* v_scopedEntries_1167_; lean_object* v_newEntries_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1190_; 
v_stateStack_1166_ = lean_ctor_get(v_s_1141_, 0);
v_scopedEntries_1167_ = lean_ctor_get(v_s_1141_, 1);
v_newEntries_1168_ = lean_ctor_get(v_s_1141_, 2);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_s_1141_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1170_ = v_s_1141_;
v_isShared_1171_ = v_isSharedCheck_1190_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_newEntries_1168_);
lean_inc(v_scopedEntries_1167_);
lean_inc(v_stateStack_1166_);
lean_dec(v_s_1141_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1190_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_a_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1189_; 
v_a_1172_ = lean_ctor_get(v_e_1142_, 0);
v_a_1173_ = lean_ctor_get(v_e_1142_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_e_1142_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1175_ = v_e_1142_;
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_inc(v_a_1172_);
lean_dec(v_e_1142_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_toOLeanEntry_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_toOLeanEntry_1177_ = lean_ctor_get(v_descr_1140_, 3);
lean_inc(v_toOLeanEntry_1177_);
v___x_1178_ = lean_box(0);
lean_inc_n(v_a_1173_, 2);
v___x_1179_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1172_, v_descr_1140_, v_a_1173_, v_stateStack_1166_, v___x_1178_);
lean_inc(v_a_1172_);
v___x_1180_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1167_, v_a_1172_, v_a_1173_);
v___x_1181_ = lean_apply_1(v_toOLeanEntry_1177_, v_a_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1181_);
v___x_1183_ = v___x_1175_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1172_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_newEntries_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 2, v___x_1184_);
lean_ctor_set(v___x_1170_, 1, v___x_1180_);
lean_ctor_set(v___x_1170_, 0, v___x_1179_);
v___x_1186_ = v___x_1170_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_00_u03c3_1193_, lean_object* v_descr_1194_, lean_object* v_s_1195_, lean_object* v_e_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1194_, v_s_1195_, v_e_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_00_u03b1_1200_, lean_object* v_descr_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1206_, lean_object* v_a_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_00_u03b1_1209_, lean_object* v_descr_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1207_, v_descr_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1215_, lean_object* v_a_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_00_u03b1_1218_, lean_object* v_descr_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1215_, v_a_1216_, v_00_u03b2_1217_, v_00_u03b1_1218_, v_descr_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1224_, lean_object* v_env_1225_, lean_object* v_as_1226_, size_t v_sz_1227_, size_t v_i_1228_, lean_object* v_b_1229_){
_start:
{
lean_object* v_a_1231_; uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1228_, v_sz_1227_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v_env_1225_);
lean_dec_ref(v_descr_1224_);
return v_b_1229_;
}
else
{
lean_object* v_snd_1236_; lean_object* v_fst_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1337_; 
v_snd_1236_ = lean_ctor_get(v_b_1229_, 1);
v_fst_1237_ = lean_ctor_get(v_b_1229_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_b_1229_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1239_ = v_b_1229_;
v_isShared_1240_ = v_isSharedCheck_1337_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1237_);
lean_dec(v_b_1229_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1337_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1336_; 
v_fst_1241_ = lean_ctor_get(v_snd_1236_, 0);
v_snd_1242_ = lean_ctor_get(v_snd_1236_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_snd_1236_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1244_ = v_snd_1236_;
v_isShared_1245_ = v_isSharedCheck_1336_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_snd_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1336_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_a_1246_; 
v_a_1246_ = lean_array_uget(v_as_1226_, v_i_1228_);
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1296_; 
v_a_1247_ = lean_ctor_get(v_a_1246_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1249_ = v_a_1246_;
v_isShared_1250_ = v_isSharedCheck_1296_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v_a_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1296_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_exportEntry_x3f_1251_; lean_object* v___x_1252_; lean_object* v_exported_1253_; lean_object* v_server_1254_; lean_object* v_private_1255_; lean_object* v___y_1257_; lean_object* v_server_1258_; lean_object* v_exported_1277_; 
v_exportEntry_x3f_1251_ = lean_ctor_get(v_descr_1224_, 6);
lean_inc_ref(v_exportEntry_x3f_1251_);
lean_inc_ref(v_env_1225_);
v___x_1252_ = lean_apply_2(v_exportEntry_x3f_1251_, v_env_1225_, v_a_1247_);
v_exported_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_exported_1253_);
v_server_1254_ = lean_ctor_get(v___x_1252_, 1);
lean_inc(v_server_1254_);
v_private_1255_ = lean_ctor_get(v___x_1252_, 2);
lean_inc(v_private_1255_);
lean_dec_ref(v___x_1252_);
if (lean_obj_tag(v_exported_1253_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_val_1287_ = lean_ctor_get(v_exported_1253_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_exported_1253_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v_exported_1253_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v_exported_1253_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_val_1287_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_array_push(v_fst_1237_, v___x_1292_);
v_exported_1277_ = v___x_1293_;
goto v___jp_1276_;
}
}
}
else
{
lean_dec(v_exported_1253_);
v_exported_1277_ = v_fst_1237_;
goto v___jp_1276_;
}
v___jp_1256_:
{
if (lean_obj_tag(v_private_1255_) == 1)
{
lean_object* v_val_1259_; lean_object* v___x_1261_; 
v_val_1259_ = lean_ctor_get(v_private_1255_, 0);
lean_inc(v_val_1259_);
lean_dec_ref(v_private_1255_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_val_1259_);
v___x_1261_ = v___x_1249_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_val_1259_);
v___x_1261_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_array_push(v_snd_1242_, v___x_1261_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1262_);
lean_ctor_set(v___x_1244_, 0, v_server_1258_);
v___x_1264_ = v___x_1244_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_server_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1264_);
lean_ctor_set(v___x_1239_, 0, v___y_1257_);
v___x_1266_ = v___x_1239_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___y_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v_a_1231_ = v___x_1266_;
goto v___jp_1230_;
}
}
}
}
else
{
lean_object* v___x_1271_; 
lean_dec(v_private_1255_);
lean_del_object(v___x_1249_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_server_1258_);
v___x_1271_ = v___x_1244_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_server_1258_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_snd_1242_);
v___x_1271_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1271_);
lean_ctor_set(v___x_1239_, 0, v___y_1257_);
v___x_1273_ = v___x_1239_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___y_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_a_1231_ = v___x_1273_;
goto v___jp_1230_;
}
}
}
}
v___jp_1276_:
{
if (lean_obj_tag(v_server_1254_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_val_1278_ = lean_ctor_get(v_server_1254_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_server_1254_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v_server_1254_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v_server_1254_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 0);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_val_1278_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_push(v_fst_1241_, v___x_1283_);
v___y_1257_ = v_exported_1277_;
v_server_1258_ = v___x_1284_;
goto v___jp_1256_;
}
}
}
else
{
lean_dec(v_server_1254_);
v___y_1257_ = v_exported_1277_;
v_server_1258_ = v_fst_1241_;
goto v___jp_1256_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1335_; 
v_a_1297_ = lean_ctor_get(v_a_1246_, 0);
v_a_1298_ = lean_ctor_get(v_a_1246_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1300_ = v_a_1246_;
v_isShared_1301_ = v_isSharedCheck_1335_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_inc(v_a_1297_);
lean_dec(v_a_1246_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1335_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_exportEntry_x3f_1302_; lean_object* v___x_1303_; lean_object* v_exported_1304_; lean_object* v_server_1305_; lean_object* v_private_1306_; lean_object* v___y_1308_; lean_object* v_server_1309_; lean_object* v_exported_1328_; 
v_exportEntry_x3f_1302_ = lean_ctor_get(v_descr_1224_, 6);
lean_inc_ref(v_exportEntry_x3f_1302_);
lean_inc_ref(v_env_1225_);
v___x_1303_ = lean_apply_2(v_exportEntry_x3f_1302_, v_env_1225_, v_a_1298_);
v_exported_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_exported_1304_);
v_server_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc(v_server_1305_);
v_private_1306_ = lean_ctor_get(v___x_1303_, 2);
lean_inc(v_private_1306_);
lean_dec_ref(v___x_1303_);
if (lean_obj_tag(v_exported_1304_) == 1)
{
lean_object* v_val_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_val_1332_ = lean_ctor_get(v_exported_1304_, 0);
lean_inc(v_val_1332_);
lean_dec_ref(v_exported_1304_);
lean_inc(v_a_1297_);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1297_);
lean_ctor_set(v___x_1333_, 1, v_val_1332_);
v___x_1334_ = lean_array_push(v_fst_1237_, v___x_1333_);
v_exported_1328_ = v___x_1334_;
goto v___jp_1327_;
}
else
{
lean_dec(v_exported_1304_);
v_exported_1328_ = v_fst_1237_;
goto v___jp_1327_;
}
v___jp_1307_:
{
if (lean_obj_tag(v_private_1306_) == 1)
{
lean_object* v_val_1310_; lean_object* v___x_1312_; 
v_val_1310_ = lean_ctor_get(v_private_1306_, 0);
lean_inc(v_val_1310_);
lean_dec_ref(v_private_1306_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v_val_1310_);
v___x_1312_ = v___x_1300_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_val_1310_);
v___x_1312_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_array_push(v_snd_1242_, v___x_1312_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1313_);
lean_ctor_set(v___x_1244_, 0, v_server_1309_);
v___x_1315_ = v___x_1244_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_server_1309_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1315_);
lean_ctor_set(v___x_1239_, 0, v___y_1308_);
v___x_1317_ = v___x_1239_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___y_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
v_a_1231_ = v___x_1317_;
goto v___jp_1230_;
}
}
}
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_private_1306_);
lean_del_object(v___x_1300_);
lean_dec(v_a_1297_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_server_1309_);
v___x_1322_ = v___x_1244_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_server_1309_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_snd_1242_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1322_);
lean_ctor_set(v___x_1239_, 0, v___y_1308_);
v___x_1324_ = v___x_1239_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___y_1308_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v_a_1231_ = v___x_1324_;
goto v___jp_1230_;
}
}
}
}
v___jp_1327_:
{
if (lean_obj_tag(v_server_1305_) == 1)
{
lean_object* v_val_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_val_1329_ = lean_ctor_get(v_server_1305_, 0);
lean_inc(v_val_1329_);
lean_dec_ref(v_server_1305_);
lean_inc(v_a_1297_);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1297_);
lean_ctor_set(v___x_1330_, 1, v_val_1329_);
v___x_1331_ = lean_array_push(v_fst_1241_, v___x_1330_);
v___y_1308_ = v_exported_1328_;
v_server_1309_ = v___x_1331_;
goto v___jp_1307_;
}
else
{
lean_dec(v_server_1305_);
v___y_1308_ = v_exported_1328_;
v_server_1309_ = v_fst_1241_;
goto v___jp_1307_;
}
}
}
}
}
}
}
v___jp_1230_:
{
size_t v___x_1232_; size_t v___x_1233_; 
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1228_, v___x_1232_);
v_i_1228_ = v___x_1233_;
v_b_1229_ = v_a_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1338_, lean_object* v_env_1339_, lean_object* v_as_1340_, lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_b_1343_){
_start:
{
size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1338_, v_env_1339_, v_as_1340_, v_sz_boxed_1344_, v_i_boxed_1345_, v_b_1343_);
lean_dec_ref(v_as_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1354_, lean_object* v_env_1355_, lean_object* v_s_1356_){
_start:
{
lean_object* v_newEntries_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1374_; 
v_newEntries_1357_ = lean_ctor_get(v_s_1356_, 2);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_s_1356_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_s_1356_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_s_1356_, 0);
lean_dec(v_unused_1376_);
v___x_1359_ = v_s_1356_;
v_isShared_1360_ = v_isSharedCheck_1374_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_newEntries_1357_);
lean_dec(v_s_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1374_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; lean_object* v_snd_1367_; lean_object* v_fst_1368_; lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v___x_1372_; 
v___x_1361_ = lean_array_mk(v_newEntries_1357_);
v___x_1362_ = l_Array_reverse___redArg(v___x_1361_);
v___x_1363_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1364_ = lean_array_size(v___x_1362_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1354_, v_env_1355_, v___x_1362_, v_sz_1364_, v___x_1365_, v___x_1363_);
lean_dec_ref(v___x_1362_);
v_snd_1367_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_snd_1367_);
v_fst_1368_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_fst_1368_);
lean_dec_ref(v___x_1366_);
v_fst_1369_ = lean_ctor_get(v_snd_1367_, 0);
lean_inc(v_fst_1369_);
v_snd_1370_ = lean_ctor_get(v_snd_1367_, 1);
lean_inc(v_snd_1370_);
lean_dec(v_snd_1367_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 2, v_snd_1370_);
lean_ctor_set(v___x_1359_, 1, v_fst_1369_);
lean_ctor_set(v___x_1359_, 0, v_fst_1368_);
v___x_1372_ = v___x_1359_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_fst_1368_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_fst_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_snd_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_00_u03c3_1379_, lean_object* v_descr_1380_, lean_object* v_env_1381_, lean_object* v_s_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1380_, v_env_1381_, v_s_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_00_u03c3_1386_, lean_object* v_descr_1387_, lean_object* v_env_1388_, lean_object* v_as_1389_, size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_b_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1387_, v_env_1388_, v_as_1389_, v_sz_1390_, v_i_1391_, v_b_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_00_u03c3_1396_, lean_object* v_descr_1397_, lean_object* v_env_1398_, lean_object* v_as_1399_, lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_b_1402_){
_start:
{
size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1394_, v_00_u03b2_1395_, v_00_u03c3_1396_, v_descr_1397_, v_env_1398_, v_as_1399_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1402_);
lean_dec_ref(v_as_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1411_, v___y_1412_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v_x_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1415_, lean_object* v_x_1416_){
_start:
{
lean_inc_ref(v_s_1415_);
return v_s_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1417_, v_x_1418_);
lean_dec_ref(v_x_1418_);
lean_dec_ref(v_s_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1425_, v_x_1426_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1430_);
lean_dec_ref(v_x_1430_);
return v_res_1431_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___f_1437_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1438_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1439_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1440_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1443_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v___f_1440_);
lean_ctor_set(v___x_1443_, 3, v___f_1439_);
lean_ctor_set(v___x_1443_, 4, v___f_1438_);
lean_ctor_set(v___x_1443_, 5, v___f_1437_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___f_1445_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1446_, 0, v_inst_1444_);
v___f_1447_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1448_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1451_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1452_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1450_);
lean_ctor_set(v___x_1452_, 2, v___f_1445_);
lean_ctor_set(v___x_1452_, 3, v___f_1446_);
lean_ctor_set(v___x_1452_, 4, v___f_1447_);
lean_ctor_set(v___x_1452_, 5, v___x_1451_);
lean_ctor_set(v___x_1452_, 6, v___f_1448_);
v___x_1453_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_00_u03c3_1457_, lean_object* v_inst_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1462_, lean_object* v_inst_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1471_ = lean_st_mk_ref(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1478_){
_start:
{
lean_object* v_newEntries_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_newEntries_1479_ = lean_ctor_get(v_s_1478_, 2);
v___x_1480_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1481_ = l_List_lengthTR___redArg(v_newEntries_1479_);
v___x_1482_ = l_Nat_reprFast(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
v___x_1484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1480_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1485_);
lean_dec_ref(v_s_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1489_);
lean_dec_ref(v_x_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1493_){
_start:
{
lean_object* v_name_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_name_1495_ = lean_ctor_get(v_descr_1493_, 0);
v___f_1496_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1497_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1493_, 4);
v___x_1498_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1498_, 0, lean_box(0));
lean_closure_set(v___x_1498_, 1, lean_box(0));
lean_closure_set(v___x_1498_, 2, lean_box(0));
lean_closure_set(v___x_1498_, 3, v_descr_1493_);
v___x_1499_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1499_, 0, lean_box(0));
lean_closure_set(v___x_1499_, 1, lean_box(0));
lean_closure_set(v___x_1499_, 2, lean_box(0));
lean_closure_set(v___x_1499_, 3, v_descr_1493_);
v___x_1500_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1500_, 0, lean_box(0));
lean_closure_set(v___x_1500_, 1, lean_box(0));
lean_closure_set(v___x_1500_, 2, lean_box(0));
lean_closure_set(v___x_1500_, 3, v_descr_1493_);
v___x_1501_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1501_, 0, lean_box(0));
lean_closure_set(v___x_1501_, 1, lean_box(0));
lean_closure_set(v___x_1501_, 2, lean_box(0));
lean_closure_set(v___x_1501_, 3, v_descr_1493_);
v___x_1502_ = lean_box(2);
v___x_1503_ = lean_box(0);
lean_inc(v_name_1495_);
v___x_1504_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1504_, 0, v_name_1495_);
lean_ctor_set(v___x_1504_, 1, v___x_1498_);
lean_ctor_set(v___x_1504_, 2, v___x_1499_);
lean_ctor_set(v___x_1504_, 3, v___x_1500_);
lean_ctor_set(v___x_1504_, 4, v___x_1501_);
lean_ctor_set(v___x_1504_, 5, v___f_1496_);
lean_ctor_set(v___x_1504_, 6, v___x_1502_);
lean_ctor_set(v___x_1504_, 7, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___f_1497_);
v___x_1506_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1519_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1519_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1519_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1511_ = l_Lean_scopedEnvExtensionsRef;
v___x_1512_ = lean_st_ref_take(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_descr_1493_);
lean_ctor_set(v___x_1513_, 1, v_a_1507_);
lean_inc_ref(v___x_1513_);
v___x_1514_ = lean_array_push(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_st_ref_set(v___x_1511_, v___x_1514_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1517_ = v___x_1509_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1513_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v_descr_1493_);
v_a_1520_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1506_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1506_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_00_u03c3_1533_, lean_object* v_descr_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_00_u03c3_1539_, lean_object* v_descr_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1537_, v_00_u03b2_1538_, v_00_u03c3_1539_, v_descr_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1543_){
_start:
{
lean_object* v_stateStack_1544_; 
v_stateStack_1544_ = lean_ctor_get(v_s_1543_, 0);
if (lean_obj_tag(v_stateStack_1544_) == 0)
{
return v_s_1543_;
}
else
{
lean_object* v_head_1545_; lean_object* v_scopedEntries_1546_; lean_object* v_newEntries_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1565_; 
lean_inc_ref(v_stateStack_1544_);
v_head_1545_ = lean_ctor_get(v_stateStack_1544_, 0);
lean_inc(v_head_1545_);
v_scopedEntries_1546_ = lean_ctor_get(v_s_1543_, 1);
v_newEntries_1547_ = lean_ctor_get(v_s_1543_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_s_1543_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v_s_1543_, 0);
lean_dec(v_unused_1566_);
v___x_1549_ = v_s_1543_;
v_isShared_1550_ = v_isSharedCheck_1565_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_newEntries_1547_);
lean_inc(v_scopedEntries_1546_);
lean_dec(v_s_1543_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1565_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_state_1551_; lean_object* v_activeScopes_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1564_; 
v_state_1551_ = lean_ctor_get(v_head_1545_, 0);
v_activeScopes_1552_ = lean_ctor_get(v_head_1545_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_head_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1554_ = v_head_1545_;
v_isShared_1555_ = v_isSharedCheck_1564_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_activeScopes_1552_);
lean_inc(v_state_1551_);
lean_dec(v_head_1545_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1564_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = 1;
if (v_isShared_1555_ == 0)
{
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_state_1551_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_activeScopes_1552_);
v___x_1558_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*2, v___x_1556_);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_stateStack_1544_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1559_);
v___x_1561_ = v___x_1549_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_scopedEntries_1546_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_newEntries_1547_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1568_, lean_object* v_env_1569_){
_start:
{
lean_object* v_ext_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_ext_1570_ = lean_ctor_get(v_ext_1568_, 1);
lean_inc_ref(v_ext_1570_);
lean_dec_ref(v_ext_1568_);
v___f_1571_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1572_ = lean_box(1);
v___x_1573_ = lean_box(0);
v___x_1574_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1570_, v_env_1569_, v___f_1571_, v___x_1572_, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_00_u03c3_1577_, lean_object* v_ext_1578_, lean_object* v_env_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1578_, v_env_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1581_){
_start:
{
lean_object* v_stateStack_1582_; 
v_stateStack_1582_ = lean_ctor_get(v_s_1581_, 0);
if (lean_obj_tag(v_stateStack_1582_) == 1)
{
lean_object* v_tail_1583_; 
v_tail_1583_ = lean_ctor_get(v_stateStack_1582_, 1);
if (lean_obj_tag(v_tail_1583_) == 1)
{
lean_object* v_scopedEntries_1584_; lean_object* v_newEntries_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_inc_ref(v_tail_1583_);
v_scopedEntries_1584_ = lean_ctor_get(v_s_1581_, 1);
v_newEntries_1585_ = lean_ctor_get(v_s_1581_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_s_1581_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_s_1581_, 0);
lean_dec(v_unused_1593_);
v___x_1587_ = v_s_1581_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_newEntries_1585_);
lean_inc(v_scopedEntries_1584_);
lean_dec(v_s_1581_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_tail_1583_);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_tail_1583_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_scopedEntries_1584_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_newEntries_1585_);
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
return v_s_1581_;
}
}
else
{
return v_s_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1595_, lean_object* v_env_1596_){
_start:
{
lean_object* v_ext_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_ext_1597_ = lean_ctor_get(v_ext_1595_, 1);
lean_inc_ref(v_ext_1597_);
lean_dec_ref(v_ext_1595_);
v___f_1598_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1599_ = lean_box(1);
v___x_1600_ = lean_box(0);
v___x_1601_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1597_, v_env_1596_, v___f_1598_, v___x_1599_, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_00_u03c3_1604_, lean_object* v_ext_1605_, lean_object* v_env_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1605_, v_env_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_zero_1610_; uint8_t v_isZero_1611_; 
v_zero_1610_ = lean_unsigned_to_nat(0u);
v_isZero_1611_ = lean_nat_dec_eq(v_a_1608_, v_zero_1610_);
if (v_isZero_1611_ == 1)
{
return v_a_1609_;
}
else
{
if (lean_obj_tag(v_a_1609_) == 0)
{
return v_a_1609_;
}
else
{
lean_object* v_head_1612_; lean_object* v_tail_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1632_; 
v_head_1612_ = lean_ctor_get(v_a_1609_, 0);
v_tail_1613_ = lean_ctor_get(v_a_1609_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_a_1609_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1615_ = v_a_1609_;
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_tail_1613_);
lean_inc(v_head_1612_);
lean_dec(v_a_1609_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_state_1617_; lean_object* v_activeScopes_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1631_; 
v_state_1617_ = lean_ctor_get(v_head_1612_, 0);
v_activeScopes_1618_ = lean_ctor_get(v_head_1612_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_head_1612_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1620_ = v_head_1612_;
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_activeScopes_1618_);
lean_inc(v_state_1617_);
lean_dec(v_head_1612_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_one_1622_; lean_object* v_n_1623_; lean_object* v___x_1625_; 
v_one_1622_ = lean_unsigned_to_nat(1u);
v_n_1623_ = lean_nat_sub(v_a_1608_, v_one_1622_);
if (v_isShared_1621_ == 0)
{
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_state_1617_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_activeScopes_1618_);
v___x_1625_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*2, v_isZero_1611_);
v___x_1626_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1623_, v_tail_1613_);
lean_dec(v_n_1623_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 1, v___x_1626_);
lean_ctor_set(v___x_1615_, 0, v___x_1625_);
v___x_1628_ = v___x_1615_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1633_, v_a_1634_);
lean_dec(v_a_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1637_, v_a_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1644_, lean_object* v_s_1645_){
_start:
{
lean_object* v_stateStack_1646_; lean_object* v_scopedEntries_1647_; lean_object* v_newEntries_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
v_stateStack_1646_ = lean_ctor_get(v_s_1645_, 0);
v_scopedEntries_1647_ = lean_ctor_get(v_s_1645_, 1);
v_newEntries_1648_ = lean_ctor_get(v_s_1645_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_s_1645_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v_s_1645_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_newEntries_1648_);
lean_inc(v_scopedEntries_1647_);
lean_inc(v_stateStack_1646_);
lean_dec(v_s_1645_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1644_, v_stateStack_1646_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_scopedEntries_1647_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_newEntries_1648_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1657_, lean_object* v_s_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1657_, v_s_1658_);
lean_dec(v_depth_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1660_, lean_object* v_env_1661_, lean_object* v_depth_1662_){
_start:
{
lean_object* v_ext_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_ext_1663_ = lean_ctor_get(v_ext_1660_, 1);
lean_inc_ref(v_ext_1663_);
lean_dec_ref(v_ext_1660_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1664_, 0, v_depth_1662_);
v___x_1665_ = lean_box(1);
v___x_1666_ = lean_box(0);
v___x_1667_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1663_, v_env_1661_, v___f_1664_, v___x_1665_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_00_u03c3_1670_, lean_object* v_ext_1671_, lean_object* v_env_1672_, lean_object* v_depth_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1671_, v_env_1672_, v_depth_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1675_, lean_object* v_env_1676_, lean_object* v_b_1677_){
_start:
{
lean_object* v_ext_1678_; lean_object* v_toEnvExtension_1679_; lean_object* v_asyncMode_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_ext_1678_ = lean_ctor_get(v_ext_1675_, 1);
lean_inc_ref(v_ext_1678_);
lean_dec_ref(v_ext_1675_);
v_toEnvExtension_1679_ = lean_ctor_get(v_ext_1678_, 0);
v_asyncMode_1680_ = lean_ctor_get(v_toEnvExtension_1679_, 2);
lean_inc(v_asyncMode_1680_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_b_1677_);
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1678_, v_env_1676_, v___x_1681_, v_asyncMode_1680_, v___x_1682_);
lean_dec(v_asyncMode_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1684_, lean_object* v_00_u03b2_1685_, lean_object* v_00_u03c3_1686_, lean_object* v_ext_1687_, lean_object* v_env_1688_, lean_object* v_b_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1687_, v_env_1688_, v_b_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1691_, lean_object* v_env_1692_, lean_object* v_namespaceName_1693_, lean_object* v_b_1694_){
_start:
{
lean_object* v_ext_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v_ext_1695_ = lean_ctor_get(v_ext_1691_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_ext_1691_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v_ext_1691_, 0);
lean_dec(v_unused_1707_);
v___x_1697_ = v_ext_1691_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_ext_1695_);
lean_dec(v_ext_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_toEnvExtension_1699_; lean_object* v_asyncMode_1700_; lean_object* v___x_1702_; 
v_toEnvExtension_1699_ = lean_ctor_get(v_ext_1695_, 0);
v_asyncMode_1700_ = lean_ctor_get(v_toEnvExtension_1699_, 2);
lean_inc(v_asyncMode_1700_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 1);
lean_ctor_set(v___x_1697_, 1, v_b_1694_);
lean_ctor_set(v___x_1697_, 0, v_namespaceName_1693_);
v___x_1702_ = v___x_1697_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_namespaceName_1693_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_b_1694_);
v___x_1702_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1695_, v_env_1692_, v___x_1702_, v_asyncMode_1700_, v___x_1703_);
lean_dec(v_asyncMode_1700_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_00_u03c3_1710_, lean_object* v_ext_1711_, lean_object* v_env_1712_, lean_object* v_namespaceName_1713_, lean_object* v_b_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1711_, v_env_1712_, v_namespaceName_1713_, v_b_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1716_, lean_object* v_states_1717_, lean_object* v_b_1718_){
_start:
{
if (lean_obj_tag(v_states_1717_) == 0)
{
lean_dec(v_b_1718_);
lean_dec_ref(v_ext_1716_);
return v_states_1717_;
}
else
{
lean_object* v_descr_1719_; lean_object* v_head_1720_; lean_object* v_tail_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1744_; 
v_descr_1719_ = lean_ctor_get(v_ext_1716_, 0);
v_head_1720_ = lean_ctor_get(v_states_1717_, 0);
v_tail_1721_ = lean_ctor_get(v_states_1717_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_states_1717_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1723_ = v_states_1717_;
v_isShared_1724_ = v_isSharedCheck_1744_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_tail_1721_);
lean_inc(v_head_1720_);
lean_dec(v_states_1717_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1744_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_addEntry_1725_; lean_object* v_state_1726_; lean_object* v_activeScopes_1727_; uint8_t v_delimitsLocal_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1743_; 
v_addEntry_1725_ = lean_ctor_get(v_descr_1719_, 4);
v_state_1726_ = lean_ctor_get(v_head_1720_, 0);
v_activeScopes_1727_ = lean_ctor_get(v_head_1720_, 1);
v_delimitsLocal_1728_ = lean_ctor_get_uint8(v_head_1720_, sizeof(void*)*2);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_head_1720_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1730_ = v_head_1720_;
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_activeScopes_1727_);
lean_inc(v_state_1726_);
lean_dec(v_head_1720_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v_top_1734_; 
lean_inc(v_addEntry_1725_);
lean_inc(v_b_1718_);
v___x_1732_ = lean_apply_2(v_addEntry_1725_, v_state_1726_, v_b_1718_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1732_);
v_top_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_activeScopes_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*2, v_delimitsLocal_1728_);
v_top_1734_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
if (v_delimitsLocal_1728_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = l_Lean_stateStackModify___redArg(v_ext_1716_, v_tail_1721_, v_b_1718_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1735_);
lean_ctor_set(v___x_1723_, 0, v_top_1734_);
v___x_1737_ = v___x_1723_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_top_1734_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_b_1718_);
lean_dec_ref(v_ext_1716_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v_top_1734_);
v___x_1740_ = v___x_1723_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_top_1734_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_tail_1721_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_00_u03c3_1747_, lean_object* v_ext_1748_, lean_object* v_states_1749_, lean_object* v_b_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_stateStackModify___redArg(v_ext_1748_, v_states_1749_, v_b_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1752_, lean_object* v_b_1753_, lean_object* v_s_1754_){
_start:
{
lean_object* v_stateStack_1755_; lean_object* v_scopedEntries_1756_; lean_object* v_newEntries_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_stateStack_1755_ = lean_ctor_get(v_s_1754_, 0);
v_scopedEntries_1756_ = lean_ctor_get(v_s_1754_, 1);
v_newEntries_1757_ = lean_ctor_get(v_s_1754_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_s_1754_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v_s_1754_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_newEntries_1757_);
lean_inc(v_scopedEntries_1756_);
lean_inc(v_stateStack_1755_);
lean_dec(v_s_1754_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = l_Lean_stateStackModify___redArg(v_ext_1752_, v_stateStack_1755_, v_b_1753_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_scopedEntries_1756_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_newEntries_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1766_, lean_object* v_env_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v_ext_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_ext_1769_ = lean_ctor_get(v_ext_1766_, 1);
lean_inc_ref(v_ext_1769_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1770_, 0, v_ext_1766_);
lean_closure_set(v___f_1770_, 1, v_b_1768_);
v___x_1771_ = lean_box(1);
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1769_, v_env_1767_, v___f_1770_, v___x_1771_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_00_u03c3_1776_, lean_object* v_ext_1777_, lean_object* v_env_1778_, lean_object* v_b_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1777_, v_env_1778_, v_b_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1781_, lean_object* v_ext_1782_, lean_object* v_b_1783_, uint8_t v_kind_1784_, lean_object* v_namespaceName_1785_){
_start:
{
switch(v_kind_1784_)
{
case 0:
{
lean_object* v___x_1786_; 
lean_dec(v_namespaceName_1785_);
v___x_1786_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1782_, v_env_1781_, v_b_1783_);
return v___x_1786_;
}
case 1:
{
lean_object* v___x_1787_; 
lean_dec(v_namespaceName_1785_);
v___x_1787_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1782_, v_env_1781_, v_b_1783_);
return v___x_1787_;
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1782_, v_env_1781_, v_namespaceName_1785_, v_b_1783_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1789_, lean_object* v_ext_1790_, lean_object* v_b_1791_, lean_object* v_kind_1792_, lean_object* v_namespaceName_1793_){
_start:
{
uint8_t v_kind_boxed_1794_; lean_object* v_res_1795_; 
v_kind_boxed_1794_ = lean_unbox(v_kind_1792_);
v_res_1795_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1789_, v_ext_1790_, v_b_1791_, v_kind_boxed_1794_, v_namespaceName_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_00_u03c3_1798_, lean_object* v_env_1799_, lean_object* v_ext_1800_, lean_object* v_b_1801_, uint8_t v_kind_1802_, lean_object* v_namespaceName_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1799_, v_ext_1800_, v_b_1801_, v_kind_1802_, v_namespaceName_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_, lean_object* v_00_u03c3_1807_, lean_object* v_env_1808_, lean_object* v_ext_1809_, lean_object* v_b_1810_, lean_object* v_kind_1811_, lean_object* v_namespaceName_1812_){
_start:
{
uint8_t v_kind_boxed_1813_; lean_object* v_res_1814_; 
v_kind_boxed_1813_ = lean_unbox(v_kind_1811_);
v_res_1814_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1805_, v_00_u03b2_1806_, v_00_u03c3_1807_, v_env_1808_, v_ext_1809_, v_b_1810_, v_kind_boxed_1813_, v_namespaceName_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1815_, lean_object* v_b_1816_, uint8_t v_kind_1817_, lean_object* v_ns_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1819_, v_ext_1815_, v_b_1816_, v_kind_1817_, v_ns_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1821_, lean_object* v_b_1822_, lean_object* v_kind_1823_, lean_object* v_ns_1824_, lean_object* v_x_1825_){
_start:
{
uint8_t v_kind_boxed_1826_; lean_object* v_res_1827_; 
v_kind_boxed_1826_ = lean_unbox(v_kind_1823_);
v_res_1827_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1821_, v_b_1822_, v_kind_boxed_1826_, v_ns_1824_, v_x_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1828_, lean_object* v_ext_1829_, lean_object* v_b_1830_, uint8_t v_kind_1831_, lean_object* v_ns_1832_){
_start:
{
lean_object* v_modifyEnv_1833_; lean_object* v___x_1834_; lean_object* v___f_1835_; lean_object* v___x_1836_; 
v_modifyEnv_1833_ = lean_ctor_get(v_inst_1828_, 1);
lean_inc(v_modifyEnv_1833_);
lean_dec_ref(v_inst_1828_);
v___x_1834_ = lean_box(v_kind_1831_);
v___f_1835_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1835_, 0, v_ext_1829_);
lean_closure_set(v___f_1835_, 1, v_b_1830_);
lean_closure_set(v___f_1835_, 2, v___x_1834_);
lean_closure_set(v___f_1835_, 3, v_ns_1832_);
v___x_1836_ = lean_apply_1(v_modifyEnv_1833_, v___f_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1837_, lean_object* v_ext_1838_, lean_object* v_b_1839_, lean_object* v_kind_1840_, lean_object* v_ns_1841_){
_start:
{
uint8_t v_kind_boxed_1842_; lean_object* v_res_1843_; 
v_kind_boxed_1842_ = lean_unbox(v_kind_1840_);
v_res_1843_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1837_, v_ext_1838_, v_b_1839_, v_kind_boxed_1842_, v_ns_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_ext_1847_, lean_object* v_b_1848_, uint8_t v_kind_1849_){
_start:
{
lean_object* v_toBind_1850_; lean_object* v_getCurrNamespace_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; 
v_toBind_1850_ = lean_ctor_get(v_inst_1844_, 1);
lean_inc(v_toBind_1850_);
lean_dec_ref(v_inst_1844_);
v_getCurrNamespace_1851_ = lean_ctor_get(v_inst_1845_, 0);
lean_inc(v_getCurrNamespace_1851_);
lean_dec_ref(v_inst_1845_);
v___x_1852_ = lean_box(v_kind_1849_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1853_, 0, v_inst_1846_);
lean_closure_set(v___f_1853_, 1, v_ext_1847_);
lean_closure_set(v___f_1853_, 2, v_b_1848_);
lean_closure_set(v___f_1853_, 3, v___x_1852_);
v___x_1854_ = lean_apply_4(v_toBind_1850_, lean_box(0), lean_box(0), v_getCurrNamespace_1851_, v___f_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_ext_1858_, lean_object* v_b_1859_, lean_object* v_kind_1860_){
_start:
{
uint8_t v_kind_boxed_1861_; lean_object* v_res_1862_; 
v_kind_boxed_1861_ = lean_unbox(v_kind_1860_);
v_res_1862_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1855_, v_inst_1856_, v_inst_1857_, v_ext_1858_, v_b_1859_, v_kind_boxed_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1863_, lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_00_u03c3_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_ext_1870_, lean_object* v_b_1871_, uint8_t v_kind_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1867_, v_inst_1868_, v_inst_1869_, v_ext_1870_, v_b_1871_, v_kind_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1874_, lean_object* v_00_u03b1_1875_, lean_object* v_00_u03b2_1876_, lean_object* v_00_u03c3_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_ext_1881_, lean_object* v_b_1882_, lean_object* v_kind_1883_){
_start:
{
uint8_t v_kind_boxed_1884_; lean_object* v_res_1885_; 
v_kind_boxed_1884_ = lean_unbox(v_kind_1883_);
v_res_1885_ = l_Lean_ScopedEnvExtension_add(v_m_1874_, v_00_u03b1_1875_, v_00_u03b2_1876_, v_00_u03c3_1877_, v_inst_1878_, v_inst_1879_, v_inst_1880_, v_ext_1881_, v_b_1882_, v_kind_boxed_1884_);
return v_res_1885_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1889_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1890_ = lean_unsigned_to_nat(16u);
v___x_1891_ = lean_unsigned_to_nat(209u);
v___x_1892_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1893_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1894_ = l_mkPanicMessageWithDecl(v___x_1893_, v___x_1892_, v___x_1891_, v___x_1890_, v___x_1889_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1895_, lean_object* v_ext_1896_, lean_object* v_env_1897_, lean_object* v_asyncMode_1898_){
_start:
{
lean_object* v_ext_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_stateStack_1903_; 
v_ext_1899_ = lean_ctor_get(v_ext_1896_, 1);
v___x_1900_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1901_ = lean_box(0);
v___x_1902_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1900_, v_ext_1899_, v_env_1897_, v_asyncMode_1898_, v___x_1901_);
v_stateStack_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_stateStack_1903_);
lean_dec(v___x_1902_);
if (lean_obj_tag(v_stateStack_1903_) == 1)
{
lean_object* v_head_1904_; lean_object* v_state_1905_; 
v_head_1904_ = lean_ctor_get(v_stateStack_1903_, 0);
lean_inc(v_head_1904_);
lean_dec_ref(v_stateStack_1903_);
v_state_1905_ = lean_ctor_get(v_head_1904_, 0);
lean_inc(v_state_1905_);
lean_dec(v_head_1904_);
return v_state_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v_stateStack_1903_);
v___x_1906_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1907_ = l_panic___redArg(v_inst_1895_, v___x_1906_);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1908_, lean_object* v_ext_1909_, lean_object* v_env_1910_, lean_object* v_asyncMode_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1908_, v_ext_1909_, v_env_1910_, v_asyncMode_1911_);
lean_dec(v_asyncMode_1911_);
lean_dec_ref(v_ext_1909_);
lean_dec(v_inst_1908_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1913_, lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_inst_1916_, lean_object* v_ext_1917_, lean_object* v_env_1918_, lean_object* v_asyncMode_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1916_, v_ext_1917_, v_env_1918_, v_asyncMode_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1921_, lean_object* v_00_u03b1_1922_, lean_object* v_00_u03b2_1923_, lean_object* v_inst_1924_, lean_object* v_ext_1925_, lean_object* v_env_1926_, lean_object* v_asyncMode_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1921_, v_00_u03b1_1922_, v_00_u03b2_1923_, v_inst_1924_, v_ext_1925_, v_env_1926_, v_asyncMode_1927_);
lean_dec(v_asyncMode_1927_);
lean_dec_ref(v_ext_1925_);
lean_dec(v_inst_1924_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1929_, lean_object* v_as_1930_, size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_b_1933_){
_start:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_usize_dec_lt(v_i_1932_, v_sz_1931_);
if (v___x_1934_ == 0)
{
lean_dec_ref(v_ext_1929_);
return v_b_1933_;
}
else
{
lean_object* v_descr_1935_; lean_object* v_snd_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1950_; 
v_descr_1935_ = lean_ctor_get(v_ext_1929_, 0);
v_snd_1936_ = lean_ctor_get(v_b_1933_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_b_1933_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_b_1933_, 0);
lean_dec(v_unused_1951_);
v___x_1938_ = v_b_1933_;
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snd_1936_);
lean_dec(v_b_1933_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_addEntry_1940_; lean_object* v___x_1941_; lean_object* v_a_1942_; lean_object* v_state_1943_; lean_object* v___x_1945_; 
v_addEntry_1940_ = lean_ctor_get(v_descr_1935_, 4);
v___x_1941_ = lean_box(0);
v_a_1942_ = lean_array_uget_borrowed(v_as_1930_, v_i_1932_);
lean_inc(v_addEntry_1940_);
lean_inc(v_a_1942_);
v_state_1943_ = lean_apply_2(v_addEntry_1940_, v_snd_1936_, v_a_1942_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v_state_1943_);
lean_ctor_set(v___x_1938_, 0, v___x_1941_);
v___x_1945_ = v___x_1938_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_state_1943_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
size_t v___x_1946_; size_t v___x_1947_; 
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_add(v_i_1932_, v___x_1946_);
v_i_1932_ = v___x_1947_;
v_b_1933_ = v___x_1945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1952_, lean_object* v_as_1953_, lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_b_1956_){
_start:
{
size_t v_sz_boxed_1957_; size_t v_i_boxed_1958_; lean_object* v_res_1959_; 
v_sz_boxed_1957_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1958_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1952_, v_as_1953_, v_sz_boxed_1957_, v_i_boxed_1958_, v_b_1956_);
lean_dec_ref(v_as_1953_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1960_, lean_object* v_as_1961_, size_t v_sz_1962_, size_t v_i_1963_, lean_object* v_b_1964_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_lt(v_i_1963_, v_sz_1962_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_ext_1960_);
return v_b_1964_;
}
else
{
lean_object* v_descr_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1981_; 
v_descr_1966_ = lean_ctor_get(v_ext_1960_, 0);
v_snd_1967_ = lean_ctor_get(v_b_1964_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_b_1964_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_b_1964_, 0);
lean_dec(v_unused_1982_);
v___x_1969_ = v_b_1964_;
v_isShared_1970_ = v_isSharedCheck_1981_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_dec(v_b_1964_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1981_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_addEntry_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v_state_1974_; lean_object* v___x_1976_; 
v_addEntry_1971_ = lean_ctor_get(v_descr_1966_, 4);
v___x_1972_ = lean_box(0);
v_a_1973_ = lean_array_uget_borrowed(v_as_1961_, v_i_1963_);
lean_inc(v_addEntry_1971_);
lean_inc(v_a_1973_);
v_state_1974_ = lean_apply_2(v_addEntry_1971_, v_snd_1967_, v_a_1973_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v_state_1974_);
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1976_ = v___x_1969_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_state_1974_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
size_t v___x_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1963_, v___x_1977_);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1960_, v_as_1961_, v_sz_1962_, v___x_1978_, v___x_1976_);
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1983_, lean_object* v_as_1984_, lean_object* v_sz_1985_, lean_object* v_i_1986_, lean_object* v_b_1987_){
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1983_, v_as_1984_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1987_);
lean_dec_ref(v_as_1984_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1991_, lean_object* v_ext_1992_, lean_object* v_n_1993_, lean_object* v_b_1994_){
_start:
{
if (lean_obj_tag(v_n_1993_) == 0)
{
lean_object* v_cs_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; size_t v_sz_1998_; size_t v___x_1999_; lean_object* v___x_2000_; lean_object* v_fst_2001_; 
v_cs_1995_ = lean_ctor_get(v_n_1993_, 0);
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_b_1994_);
v_sz_1998_ = lean_array_size(v_cs_1995_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1991_, v_ext_1992_, v_cs_1995_, v_sz_1998_, v___x_1999_, v___x_1997_);
v_fst_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_fst_2001_);
if (lean_obj_tag(v_fst_2001_) == 0)
{
lean_object* v_snd_2002_; lean_object* v___x_2003_; 
v_snd_2002_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_snd_2002_);
lean_dec_ref(v___x_2000_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_snd_2002_);
return v___x_2003_;
}
else
{
lean_object* v_val_2004_; 
lean_dec_ref(v___x_2000_);
v_val_2004_ = lean_ctor_get(v_fst_2001_, 0);
lean_inc(v_val_2004_);
lean_dec_ref(v_fst_2001_);
return v_val_2004_;
}
}
else
{
lean_object* v_vs_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; lean_object* v_fst_2011_; 
v_vs_2005_ = lean_ctor_get(v_n_1993_, 0);
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v_b_1994_);
v_sz_2008_ = lean_array_size(v_vs_2005_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1992_, v_vs_2005_, v_sz_2008_, v___x_2009_, v___x_2007_);
v_fst_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_fst_2011_);
if (lean_obj_tag(v_fst_2011_) == 0)
{
lean_object* v_snd_2012_; lean_object* v___x_2013_; 
v_snd_2012_ = lean_ctor_get(v___x_2010_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2010_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_snd_2012_);
return v___x_2013_;
}
else
{
lean_object* v_val_2014_; 
lean_dec_ref(v___x_2010_);
v_val_2014_ = lean_ctor_get(v_fst_2011_, 0);
lean_inc(v_val_2014_);
lean_dec_ref(v_fst_2011_);
return v_val_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2015_, lean_object* v_ext_2016_, lean_object* v_as_2017_, size_t v_sz_2018_, size_t v_i_2019_, lean_object* v_b_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_lt(v_i_2019_, v_sz_2018_);
if (v___x_2021_ == 0)
{
lean_dec_ref(v_ext_2016_);
return v_b_2020_;
}
else
{
lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2040_; 
v_snd_2022_ = lean_ctor_get(v_b_2020_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_b_2020_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v_b_2020_, 0);
lean_dec(v_unused_2041_);
v___x_2024_ = v_b_2020_;
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_dec(v_b_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_2017_, v_i_2019_);
lean_inc(v_snd_2022_);
lean_inc_ref(v_ext_2016_);
v___x_2027_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2015_, v_ext_2016_, v_a_2026_, v_snd_2022_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec_ref(v_ext_2016_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2028_);
v___x_2030_ = v___x_2024_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_snd_2022_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec(v_snd_2022_);
v_a_2032_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2027_);
v___x_2033_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2032_);
lean_ctor_set(v___x_2024_, 0, v___x_2033_);
v___x_2035_ = v___x_2024_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_a_2032_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
size_t v___x_2036_; size_t v___x_2037_; 
v___x_2036_ = ((size_t)1ULL);
v___x_2037_ = lean_usize_add(v_i_2019_, v___x_2036_);
v_i_2019_ = v___x_2037_;
v_b_2020_ = v___x_2035_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2042_, lean_object* v_ext_2043_, lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_){
_start:
{
size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2042_, v_ext_2043_, v_as_2044_, v_sz_boxed_2048_, v_i_boxed_2049_, v_b_2047_);
lean_dec_ref(v_as_2044_);
lean_dec(v_init_2042_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2051_, lean_object* v_ext_2052_, lean_object* v_n_2053_, lean_object* v_b_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2051_, v_ext_2052_, v_n_2053_, v_b_2054_);
lean_dec_ref(v_n_2053_);
lean_dec(v_init_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_){
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
size_t v___x_2073_; size_t v___x_2074_; 
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_add(v_i_2059_, v___x_2073_);
v_i_2059_ = v___x_2074_;
v_b_2060_ = v___x_2072_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2079_, lean_object* v_as_2080_, lean_object* v_sz_2081_, lean_object* v_i_2082_, lean_object* v_b_2083_){
_start:
{
size_t v_sz_boxed_2084_; size_t v_i_boxed_2085_; lean_object* v_res_2086_; 
v_sz_boxed_2084_ = lean_unbox_usize(v_sz_2081_);
lean_dec(v_sz_2081_);
v_i_boxed_2085_ = lean_unbox_usize(v_i_2082_);
lean_dec(v_i_2082_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2079_, v_as_2080_, v_sz_boxed_2084_, v_i_boxed_2085_, v_b_2083_);
lean_dec_ref(v_as_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2087_, lean_object* v_as_2088_, size_t v_sz_2089_, size_t v_i_2090_, lean_object* v_b_2091_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2090_, v_sz_2089_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v_ext_2087_);
return v_b_2091_;
}
else
{
lean_object* v_descr_2093_; lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_descr_2093_ = lean_ctor_get(v_ext_2087_, 0);
v_snd_2094_ = lean_ctor_get(v_b_2091_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_b_2091_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_b_2091_, 0);
lean_dec(v_unused_2109_);
v___x_2096_ = v_b_2091_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_dec(v_b_2091_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_addEntry_2098_; lean_object* v___x_2099_; lean_object* v_a_2100_; lean_object* v_state_2101_; lean_object* v___x_2103_; 
v_addEntry_2098_ = lean_ctor_get(v_descr_2093_, 4);
v___x_2099_ = lean_box(0);
v_a_2100_ = lean_array_uget_borrowed(v_as_2088_, v_i_2090_);
lean_inc(v_addEntry_2098_);
lean_inc(v_a_2100_);
v_state_2101_ = lean_apply_2(v_addEntry_2098_, v_snd_2094_, v_a_2100_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_state_2101_);
lean_ctor_set(v___x_2096_, 0, v___x_2099_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_state_2101_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2090_, v___x_2104_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2087_, v_as_2088_, v_sz_2089_, v___x_2105_, v___x_2103_);
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2110_, lean_object* v_as_2111_, lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_b_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2110_, v_as_2111_, v_sz_boxed_2115_, v_i_boxed_2116_, v_b_2114_);
lean_dec_ref(v_as_2111_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2118_, lean_object* v_t_2119_, lean_object* v_init_2120_){
_start:
{
lean_object* v_root_2121_; lean_object* v_tail_2122_; lean_object* v___x_2123_; 
v_root_2121_ = lean_ctor_get(v_t_2119_, 0);
v_tail_2122_ = lean_ctor_get(v_t_2119_, 1);
lean_inc_ref(v_ext_2118_);
lean_inc(v_init_2120_);
v___x_2123_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2120_, v_ext_2118_, v_root_2121_, v_init_2120_);
lean_dec(v_init_2120_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
lean_dec_ref(v_ext_2118_);
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
return v_a_2124_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; size_t v_sz_2128_; size_t v___x_2129_; lean_object* v___x_2130_; lean_object* v_fst_2131_; 
v_a_2125_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2123_);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v_a_2125_);
v_sz_2128_ = lean_array_size(v_tail_2122_);
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2118_, v_tail_2122_, v_sz_2128_, v___x_2129_, v___x_2127_);
v_fst_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_fst_2131_);
if (lean_obj_tag(v_fst_2131_) == 0)
{
lean_object* v_snd_2132_; 
v_snd_2132_ = lean_ctor_get(v___x_2130_, 1);
lean_inc(v_snd_2132_);
lean_dec_ref(v___x_2130_);
return v_snd_2132_;
}
else
{
lean_object* v_val_2133_; 
lean_dec_ref(v___x_2130_);
v_val_2133_ = lean_ctor_get(v_fst_2131_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_fst_2131_);
return v_val_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2134_, lean_object* v_t_2135_, lean_object* v_init_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2134_, v_t_2135_, v_init_2136_);
lean_dec_ref(v_t_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2138_, lean_object* v_ext_2139_, lean_object* v_s_2140_){
_start:
{
lean_object* v_stateStack_2141_; 
v_stateStack_2141_ = lean_ctor_get(v_s_2140_, 0);
lean_inc(v_stateStack_2141_);
if (lean_obj_tag(v_stateStack_2141_) == 1)
{
lean_object* v_scopedEntries_2142_; lean_object* v_newEntries_2143_; lean_object* v_head_2144_; lean_object* v_tail_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2174_; 
v_scopedEntries_2142_ = lean_ctor_get(v_s_2140_, 1);
v_newEntries_2143_ = lean_ctor_get(v_s_2140_, 2);
v_head_2144_ = lean_ctor_get(v_stateStack_2141_, 0);
v_tail_2145_ = lean_ctor_get(v_stateStack_2141_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_stateStack_2141_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2147_ = v_stateStack_2141_;
v_isShared_2148_ = v_isSharedCheck_2174_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_tail_2145_);
lean_inc(v_head_2144_);
lean_dec(v_stateStack_2141_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2174_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___y_2150_; lean_object* v_state_2155_; lean_object* v_activeScopes_2156_; uint8_t v_delimitsLocal_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2173_; 
v_state_2155_ = lean_ctor_get(v_head_2144_, 0);
v_activeScopes_2156_ = lean_ctor_get(v_head_2144_, 1);
v_delimitsLocal_2157_ = lean_ctor_get_uint8(v_head_2144_, sizeof(void*)*2);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_head_2144_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2159_ = v_head_2144_;
v_isShared_2160_ = v_isSharedCheck_2173_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_activeScopes_2156_);
lean_inc(v_state_2155_);
lean_dec(v_head_2144_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2173_;
goto v_resetjp_2158_;
}
v___jp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___y_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___y_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_tail_2145_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_scopedEntries_2142_);
lean_ctor_set(v___x_2153_, 2, v_newEntries_2143_);
return v___x_2153_;
}
}
v_resetjp_2158_:
{
uint8_t v___x_2161_; 
v___x_2161_ = l_Lean_NameSet_contains(v_activeScopes_2156_, v_namespaceName_2138_);
if (v___x_2161_ == 0)
{
lean_object* v_activeScopes_2162_; lean_object* v___x_2163_; 
lean_inc(v_newEntries_2143_);
lean_inc_ref(v_scopedEntries_2142_);
lean_dec_ref(v_s_2140_);
lean_inc(v_namespaceName_2138_);
v_activeScopes_2162_ = l_Lean_NameSet_insert(v_activeScopes_2156_, v_namespaceName_2138_);
v___x_2163_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2142_, v_namespaceName_2138_);
lean_dec(v_namespaceName_2138_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref(v_ext_2139_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_activeScopes_2162_);
v___x_2165_ = v___x_2159_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_state_2155_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_activeScopes_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*2, v_delimitsLocal_2157_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
v___y_2150_ = v___x_2165_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_val_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_val_2167_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2167_);
lean_dec_ref(v___x_2163_);
v___x_2168_ = 1;
v___x_2169_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2139_, v_val_2167_, v_state_2155_);
lean_dec(v_val_2167_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_activeScopes_2162_);
lean_ctor_set(v___x_2159_, 0, v___x_2169_);
v___x_2171_ = v___x_2159_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_activeScopes_2162_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*2, v___x_2168_);
v___y_2150_ = v___x_2171_;
goto v___jp_2149_;
}
}
}
else
{
lean_del_object(v___x_2159_);
lean_dec(v_activeScopes_2156_);
lean_dec(v_state_2155_);
lean_del_object(v___x_2147_);
lean_dec(v_tail_2145_);
lean_dec_ref(v_ext_2139_);
lean_dec(v_namespaceName_2138_);
return v_s_2140_;
}
}
}
}
else
{
lean_dec(v_stateStack_2141_);
lean_dec_ref(v_ext_2139_);
lean_dec(v_namespaceName_2138_);
return v_s_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2175_, lean_object* v_env_2176_, lean_object* v_namespaceName_2177_){
_start:
{
lean_object* v_ext_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_ext_2178_ = lean_ctor_get(v_ext_2175_, 1);
lean_inc_ref(v_ext_2178_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2179_, 0, v_namespaceName_2177_);
lean_closure_set(v___f_2179_, 1, v_ext_2175_);
v___x_2180_ = lean_box(1);
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2178_, v_env_2176_, v___f_2179_, v___x_2180_, v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_00_u03c3_2185_, lean_object* v_ext_2186_, lean_object* v_env_2187_, lean_object* v_namespaceName_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2186_, v_env_2187_, v_namespaceName_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2190_, lean_object* v_00_u03c3_2191_, lean_object* v_00_u03b1_2192_, lean_object* v_ext_2193_, lean_object* v_t_2194_, lean_object* v_init_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2193_, v_t_2194_, v_init_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_00_u03c3_2198_, lean_object* v_00_u03b1_2199_, lean_object* v_ext_2200_, lean_object* v_t_2201_, lean_object* v_init_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2197_, v_00_u03c3_2198_, v_00_u03b1_2199_, v_ext_2200_, v_t_2201_, v_init_2202_);
lean_dec_ref(v_t_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2204_, lean_object* v_00_u03c3_2205_, lean_object* v_init_2206_, lean_object* v_00_u03b1_2207_, lean_object* v_ext_2208_, lean_object* v_n_2209_, lean_object* v_b_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2206_, v_ext_2208_, v_n_2209_, v_b_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2212_, lean_object* v_00_u03c3_2213_, lean_object* v_init_2214_, lean_object* v_00_u03b1_2215_, lean_object* v_ext_2216_, lean_object* v_n_2217_, lean_object* v_b_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2212_, v_00_u03c3_2213_, v_init_2214_, v_00_u03b1_2215_, v_ext_2216_, v_n_2217_, v_b_2218_);
lean_dec_ref(v_n_2217_);
lean_dec(v_init_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2220_, lean_object* v_00_u03c3_2221_, lean_object* v_00_u03b1_2222_, lean_object* v_ext_2223_, lean_object* v_as_2224_, size_t v_sz_2225_, size_t v_i_2226_, lean_object* v_b_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2223_, v_as_2224_, v_sz_2225_, v_i_2226_, v_b_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_00_u03c3_2230_, lean_object* v_00_u03b1_2231_, lean_object* v_ext_2232_, lean_object* v_as_2233_, lean_object* v_sz_2234_, lean_object* v_i_2235_, lean_object* v_b_2236_){
_start:
{
size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2234_);
lean_dec(v_sz_2234_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2229_, v_00_u03c3_2230_, v_00_u03b1_2231_, v_ext_2232_, v_as_2233_, v_sz_boxed_2237_, v_i_boxed_2238_, v_b_2236_);
lean_dec_ref(v_as_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2240_, lean_object* v_00_u03c3_2241_, lean_object* v_init_2242_, lean_object* v_00_u03b1_2243_, lean_object* v_ext_2244_, lean_object* v_as_2245_, size_t v_sz_2246_, size_t v_i_2247_, lean_object* v_b_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2242_, v_ext_2244_, v_as_2245_, v_sz_2246_, v_i_2247_, v_b_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2250_, lean_object* v_00_u03c3_2251_, lean_object* v_init_2252_, lean_object* v_00_u03b1_2253_, lean_object* v_ext_2254_, lean_object* v_as_2255_, lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_b_2258_){
_start:
{
size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2250_, v_00_u03c3_2251_, v_init_2252_, v_00_u03b1_2253_, v_ext_2254_, v_as_2255_, v_sz_boxed_2259_, v_i_boxed_2260_, v_b_2258_);
lean_dec_ref(v_as_2255_);
lean_dec(v_init_2252_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2262_, lean_object* v_00_u03c3_2263_, lean_object* v_00_u03b1_2264_, lean_object* v_ext_2265_, lean_object* v_as_2266_, size_t v_sz_2267_, size_t v_i_2268_, lean_object* v_b_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2265_, v_as_2266_, v_sz_2267_, v_i_2268_, v_b_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2271_, lean_object* v_00_u03c3_2272_, lean_object* v_00_u03b1_2273_, lean_object* v_ext_2274_, lean_object* v_as_2275_, lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_b_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2271_, v_00_u03c3_2272_, v_00_u03b1_2273_, v_ext_2274_, v_as_2275_, v_sz_boxed_2279_, v_i_boxed_2280_, v_b_2278_);
lean_dec_ref(v_as_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2282_, lean_object* v_00_u03c3_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_ext_2285_, lean_object* v_as_2286_, size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_b_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2285_, v_as_2286_, v_sz_2287_, v_i_2288_, v_b_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2291_, lean_object* v_00_u03c3_2292_, lean_object* v_00_u03b1_2293_, lean_object* v_ext_2294_, lean_object* v_as_2295_, lean_object* v_sz_2296_, lean_object* v_i_2297_, lean_object* v_b_2298_){
_start:
{
size_t v_sz_boxed_2299_; size_t v_i_boxed_2300_; lean_object* v_res_2301_; 
v_sz_boxed_2299_ = lean_unbox_usize(v_sz_2296_);
lean_dec(v_sz_2296_);
v_i_boxed_2300_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2291_, v_00_u03c3_2292_, v_00_u03b1_2293_, v_ext_2294_, v_as_2295_, v_sz_boxed_2299_, v_i_boxed_2300_, v_b_2298_);
lean_dec_ref(v_as_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2302_, lean_object* v_00_u03c3_2303_, lean_object* v_00_u03b1_2304_, lean_object* v_ext_2305_, lean_object* v_as_2306_, size_t v_sz_2307_, size_t v_i_2308_, lean_object* v_b_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2305_, v_as_2306_, v_sz_2307_, v_i_2308_, v_b_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2311_, lean_object* v_00_u03c3_2312_, lean_object* v_00_u03b1_2313_, lean_object* v_ext_2314_, lean_object* v_as_2315_, lean_object* v_sz_2316_, lean_object* v_i_2317_, lean_object* v_b_2318_){
_start:
{
size_t v_sz_boxed_2319_; size_t v_i_boxed_2320_; lean_object* v_res_2321_; 
v_sz_boxed_2319_ = lean_unbox_usize(v_sz_2316_);
lean_dec(v_sz_2316_);
v_i_boxed_2320_ = lean_unbox_usize(v_i_2317_);
lean_dec(v_i_2317_);
v_res_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2311_, v_00_u03c3_2312_, v_00_u03b1_2313_, v_ext_2314_, v_as_2315_, v_sz_boxed_2319_, v_i_boxed_2320_, v_b_2318_);
lean_dec_ref(v_as_2315_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2322_, lean_object* v_s_2323_){
_start:
{
lean_object* v_stateStack_2324_; 
v_stateStack_2324_ = lean_ctor_get(v_s_2323_, 0);
lean_inc(v_stateStack_2324_);
if (lean_obj_tag(v_stateStack_2324_) == 1)
{
lean_object* v_head_2325_; lean_object* v_scopedEntries_2326_; lean_object* v_newEntries_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2354_; 
v_head_2325_ = lean_ctor_get(v_stateStack_2324_, 0);
lean_inc(v_head_2325_);
v_scopedEntries_2326_ = lean_ctor_get(v_s_2323_, 1);
v_newEntries_2327_ = lean_ctor_get(v_s_2323_, 2);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_s_2323_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v_s_2323_, 0);
lean_dec(v_unused_2355_);
v___x_2329_ = v_s_2323_;
v_isShared_2330_ = v_isSharedCheck_2354_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_newEntries_2327_);
lean_inc(v_scopedEntries_2326_);
lean_dec(v_s_2323_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2354_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_tail_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2352_; 
v_tail_2331_ = lean_ctor_get(v_stateStack_2324_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_stateStack_2324_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_stateStack_2324_, 0);
lean_dec(v_unused_2353_);
v___x_2333_ = v_stateStack_2324_;
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_tail_2331_);
lean_dec(v_stateStack_2324_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_state_2335_; lean_object* v_activeScopes_2336_; uint8_t v_delimitsLocal_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2351_; 
v_state_2335_ = lean_ctor_get(v_head_2325_, 0);
v_activeScopes_2336_ = lean_ctor_get(v_head_2325_, 1);
v_delimitsLocal_2337_ = lean_ctor_get_uint8(v_head_2325_, sizeof(void*)*2);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_head_2325_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2339_ = v_head_2325_;
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_activeScopes_2336_);
lean_inc(v_state_2335_);
lean_dec(v_head_2325_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_apply_1(v_f_2322_, v_state_2335_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2341_);
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_activeScopes_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*2, v_delimitsLocal_2337_);
v___x_2343_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2343_);
v___x_2345_ = v___x_2333_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_tail_2331_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2345_);
v___x_2347_ = v___x_2329_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_scopedEntries_2326_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_newEntries_2327_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2324_);
lean_dec(v_f_2322_);
return v_s_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2356_, lean_object* v_env_2357_, lean_object* v_f_2358_){
_start:
{
lean_object* v_ext_2359_; lean_object* v_toEnvExtension_2360_; lean_object* v_asyncMode_2361_; lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_ext_2359_ = lean_ctor_get(v_ext_2356_, 1);
lean_inc_ref(v_ext_2359_);
lean_dec_ref(v_ext_2356_);
v_toEnvExtension_2360_ = lean_ctor_get(v_ext_2359_, 0);
v_asyncMode_2361_ = lean_ctor_get(v_toEnvExtension_2360_, 2);
lean_inc(v_asyncMode_2361_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2362_, 0, v_f_2358_);
v___x_2363_ = lean_box(0);
v___x_2364_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2359_, v_env_2357_, v___f_2362_, v_asyncMode_2361_, v___x_2363_);
lean_dec(v_asyncMode_2361_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2365_, lean_object* v_00_u03b2_2366_, lean_object* v_00_u03c3_2367_, lean_object* v_ext_2368_, lean_object* v_env_2369_, lean_object* v_f_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2368_, v_env_2369_, v_f_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2372_, lean_object* v_____s_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_apply_2(v_toPure_2372_, lean_box(0), v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2376_, lean_object* v_toPure_2377_, lean_object* v_r_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2376_);
v___x_2380_ = lean_apply_2(v_toPure_2377_, lean_box(0), v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2381_, lean_object* v_toBind_2382_, lean_object* v___f_2383_, lean_object* v_a_2384_, lean_object* v_x_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_modifyEnv_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_modifyEnv_2387_ = lean_ctor_get(v_inst_2381_, 1);
lean_inc(v_modifyEnv_2387_);
lean_dec_ref(v_inst_2381_);
v___x_2388_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2388_, 0, lean_box(0));
lean_closure_set(v___x_2388_, 1, lean_box(0));
lean_closure_set(v___x_2388_, 2, lean_box(0));
lean_closure_set(v___x_2388_, 3, v_a_2384_);
v___x_2389_ = lean_apply_1(v_modifyEnv_2387_, v___x_2388_);
v___x_2390_ = lean_apply_4(v_toBind_2382_, lean_box(0), lean_box(0), v___x_2389_, v___f_2383_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2391_, lean_object* v_inst_2392_, lean_object* v_toBind_2393_, lean_object* v_inst_2394_, lean_object* v___f_2395_, lean_object* v_____do__lift_2396_){
_start:
{
lean_object* v___x_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; size_t v_sz_2400_; size_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2397_ = lean_box(0);
v___f_2398_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2398_, 0, v___x_2397_);
lean_closure_set(v___f_2398_, 1, v_toPure_2391_);
lean_inc(v_toBind_2393_);
v___f_2399_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2399_, 0, v_inst_2392_);
lean_closure_set(v___f_2399_, 1, v_toBind_2393_);
lean_closure_set(v___f_2399_, 2, v___f_2398_);
v_sz_2400_ = lean_array_size(v_____do__lift_2396_);
v___x_2401_ = ((size_t)0ULL);
v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2394_, v_____do__lift_2396_, v___f_2399_, v_sz_2400_, v___x_2401_, v___x_2397_);
v___x_2403_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v___x_2402_, v___f_2395_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = l_Lean_scopedEnvExtensionsRef;
v___x_2405_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2405_, 0, lean_box(0));
lean_closure_set(v___x_2405_, 1, lean_box(0));
lean_closure_set(v___x_2405_, 2, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_){
_start:
{
lean_object* v_toApplicative_2409_; lean_object* v_toBind_2410_; lean_object* v_toPure_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; 
v_toApplicative_2409_ = lean_ctor_get(v_inst_2406_, 0);
v_toBind_2410_ = lean_ctor_get(v_inst_2406_, 1);
lean_inc_n(v_toBind_2410_, 2);
v_toPure_2411_ = lean_ctor_get(v_toApplicative_2409_, 1);
lean_inc_n(v_toPure_2411_, 2);
v___x_2412_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2413_ = lean_apply_2(v_inst_2408_, lean_box(0), v___x_2412_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2414_, 0, v_toPure_2411_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2415_, 0, v_toPure_2411_);
lean_closure_set(v___f_2415_, 1, v_inst_2407_);
lean_closure_set(v___f_2415_, 2, v_toBind_2410_);
lean_closure_set(v___f_2415_, 3, v_inst_2406_);
lean_closure_set(v___f_2415_, 4, v___f_2414_);
v___x_2416_ = lean_apply_4(v_toBind_2410_, lean_box(0), lean_box(0), v___x_2413_, v___f_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_pushScope___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2422_, lean_object* v_toBind_2423_, lean_object* v___f_2424_, lean_object* v_a_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_modifyEnv_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_modifyEnv_2428_ = lean_ctor_get(v_inst_2422_, 1);
lean_inc(v_modifyEnv_2428_);
lean_dec_ref(v_inst_2422_);
v___x_2429_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2429_, 0, lean_box(0));
lean_closure_set(v___x_2429_, 1, lean_box(0));
lean_closure_set(v___x_2429_, 2, lean_box(0));
lean_closure_set(v___x_2429_, 3, v_a_2425_);
v___x_2430_ = lean_apply_1(v_modifyEnv_2428_, v___x_2429_);
v___x_2431_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2430_, v___f_2424_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2432_, lean_object* v_inst_2433_, lean_object* v_toBind_2434_, lean_object* v_inst_2435_, lean_object* v___f_2436_, lean_object* v_____do__lift_2437_){
_start:
{
lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2438_ = lean_box(0);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2439_, 0, v___x_2438_);
lean_closure_set(v___f_2439_, 1, v_toPure_2432_);
lean_inc(v_toBind_2434_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
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
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_){
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
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2454_, 0, v_toPure_2450_);
lean_closure_set(v___f_2454_, 1, v_inst_2446_);
lean_closure_set(v___f_2454_, 2, v_toBind_2449_);
lean_closure_set(v___f_2454_, 3, v_inst_2445_);
lean_closure_set(v___f_2454_, 4, v___f_2453_);
v___x_2455_ = lean_apply_4(v_toBind_2449_, lean_box(0), lean_box(0), v___x_2452_, v___f_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_popScope___redArg(v_inst_2457_, v_inst_2458_, v_inst_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2461_, lean_object* v_depth_2462_, lean_object* v_x_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2461_, v_x_2463_, v_depth_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2465_, lean_object* v_depth_2466_, lean_object* v_toBind_2467_, lean_object* v___f_2468_, lean_object* v_a_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_modifyEnv_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_modifyEnv_2472_ = lean_ctor_get(v_inst_2465_, 1);
lean_inc(v_modifyEnv_2472_);
lean_dec_ref(v_inst_2465_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2473_, 0, v_a_2469_);
lean_closure_set(v___f_2473_, 1, v_depth_2466_);
v___x_2474_ = lean_apply_1(v_modifyEnv_2472_, v___f_2473_);
v___x_2475_ = lean_apply_4(v_toBind_2467_, lean_box(0), lean_box(0), v___x_2474_, v___f_2468_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2476_, lean_object* v_inst_2477_, lean_object* v_depth_2478_, lean_object* v_toBind_2479_, lean_object* v_inst_2480_, lean_object* v___f_2481_, lean_object* v_____do__lift_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2483_ = lean_box(0);
v___f_2484_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2484_, 0, v___x_2483_);
lean_closure_set(v___f_2484_, 1, v_toPure_2476_);
lean_inc(v_toBind_2479_);
v___f_2485_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2485_, 0, v_inst_2477_);
lean_closure_set(v___f_2485_, 1, v_depth_2478_);
lean_closure_set(v___f_2485_, 2, v_toBind_2479_);
lean_closure_set(v___f_2485_, 3, v___f_2484_);
v_sz_2486_ = lean_array_size(v_____do__lift_2482_);
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2480_, v_____do__lift_2482_, v___f_2485_, v_sz_2486_, v___x_2487_, v___x_2483_);
v___x_2489_ = lean_apply_4(v_toBind_2479_, lean_box(0), lean_box(0), v___x_2488_, v___f_2481_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_depth_2493_){
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
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2500_, 0, v_toPure_2496_);
lean_closure_set(v___f_2500_, 1, v_inst_2491_);
lean_closure_set(v___f_2500_, 2, v_depth_2493_);
lean_closure_set(v___f_2500_, 3, v_toBind_2495_);
lean_closure_set(v___f_2500_, 4, v_inst_2490_);
lean_closure_set(v___f_2500_, 5, v___f_2499_);
v___x_2501_ = lean_apply_4(v_toBind_2495_, lean_box(0), lean_box(0), v___x_2498_, v___f_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_depth_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_setDelimitsLocal___redArg(v_inst_2503_, v_inst_2504_, v_inst_2505_, v_depth_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2508_, lean_object* v_namespaceName_2509_, lean_object* v_x_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2508_, v_x_2510_, v_namespaceName_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2512_, lean_object* v_namespaceName_2513_, lean_object* v_toBind_2514_, lean_object* v___f_2515_, lean_object* v_a_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_modifyEnv_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_modifyEnv_2519_ = lean_ctor_get(v_inst_2512_, 1);
lean_inc(v_modifyEnv_2519_);
lean_dec_ref(v_inst_2512_);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2520_, 0, v_a_2516_);
lean_closure_set(v___f_2520_, 1, v_namespaceName_2513_);
v___x_2521_ = lean_apply_1(v_modifyEnv_2519_, v___f_2520_);
v___x_2522_ = lean_apply_4(v_toBind_2514_, lean_box(0), lean_box(0), v___x_2521_, v___f_2515_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2523_, lean_object* v_inst_2524_, lean_object* v_namespaceName_2525_, lean_object* v_toBind_2526_, lean_object* v_inst_2527_, lean_object* v___f_2528_, lean_object* v_____do__lift_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___f_2532_; size_t v_sz_2533_; size_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2530_ = lean_box(0);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2531_, 0, v___x_2530_);
lean_closure_set(v___f_2531_, 1, v_toPure_2523_);
lean_inc(v_toBind_2526_);
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2532_, 0, v_inst_2524_);
lean_closure_set(v___f_2532_, 1, v_namespaceName_2525_);
lean_closure_set(v___f_2532_, 2, v_toBind_2526_);
lean_closure_set(v___f_2532_, 3, v___f_2531_);
v_sz_2533_ = lean_array_size(v_____do__lift_2529_);
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2527_, v_____do__lift_2529_, v___f_2532_, v_sz_2533_, v___x_2534_, v___x_2530_);
v___x_2536_ = lean_apply_4(v_toBind_2526_, lean_box(0), lean_box(0), v___x_2535_, v___f_2528_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_namespaceName_2540_){
_start:
{
lean_object* v_toApplicative_2541_; lean_object* v_toBind_2542_; lean_object* v_toPure_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_toApplicative_2541_ = lean_ctor_get(v_inst_2537_, 0);
v_toBind_2542_ = lean_ctor_get(v_inst_2537_, 1);
lean_inc_n(v_toBind_2542_, 2);
v_toPure_2543_ = lean_ctor_get(v_toApplicative_2541_, 1);
lean_inc_n(v_toPure_2543_, 2);
v___x_2544_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2545_ = lean_apply_2(v_inst_2539_, lean_box(0), v___x_2544_);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2546_, 0, v_toPure_2543_);
v___f_2547_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2547_, 0, v_toPure_2543_);
lean_closure_set(v___f_2547_, 1, v_inst_2538_);
lean_closure_set(v___f_2547_, 2, v_namespaceName_2540_);
lean_closure_set(v___f_2547_, 3, v_toBind_2542_);
lean_closure_set(v___f_2547_, 4, v_inst_2537_);
lean_closure_set(v___f_2547_, 5, v___f_2546_);
v___x_2548_ = lean_apply_4(v_toBind_2542_, lean_box(0), lean_box(0), v___x_2545_, v___f_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_namespaceName_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_activateScoped___redArg(v_inst_2550_, v_inst_2551_, v_inst_2552_, v_namespaceName_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2556_){
_start:
{
lean_inc(v___y_2556_);
return v___y_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2557_);
lean_dec(v___y_2557_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2559_, lean_object* v_a_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_a_2560_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2564_, lean_object* v_a_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2564_, v_a_2565_, v___y_2566_);
lean_dec_ref(v___y_2566_);
lean_dec(v_x_2564_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_initial_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2577_){
_start:
{
lean_object* v_name_2579_; lean_object* v_addEntry_2580_; lean_object* v_initial_2581_; lean_object* v_finalizeImport_2582_; lean_object* v_exportEntry_x3f_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_name_2579_ = lean_ctor_get(v_descr_2577_, 0);
lean_inc(v_name_2579_);
v_addEntry_2580_ = lean_ctor_get(v_descr_2577_, 1);
lean_inc(v_addEntry_2580_);
v_initial_2581_ = lean_ctor_get(v_descr_2577_, 2);
lean_inc(v_initial_2581_);
v_finalizeImport_2582_ = lean_ctor_get(v_descr_2577_, 3);
lean_inc(v_finalizeImport_2582_);
v_exportEntry_x3f_2583_ = lean_ctor_get(v_descr_2577_, 4);
lean_inc_ref(v_exportEntry_x3f_2583_);
lean_dec_ref(v_descr_2577_);
v___f_2584_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2585_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2586_, 0, v_initial_2581_);
v___x_2587_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2587_, 0, v_name_2579_);
lean_ctor_set(v___x_2587_, 1, v___f_2586_);
lean_ctor_set(v___x_2587_, 2, v___f_2585_);
lean_ctor_set(v___x_2587_, 3, v___f_2584_);
lean_ctor_set(v___x_2587_, 4, v_addEntry_2580_);
lean_ctor_set(v___x_2587_, 5, v_finalizeImport_2582_);
lean_ctor_set(v___x_2587_, 6, v_exportEntry_x3f_2583_);
v___x_2588_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2592_, lean_object* v_00_u03c3_2593_, lean_object* v_descr_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_00_u03c3_2598_, lean_object* v_descr_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2597_, v_00_u03c3_2598_, v_descr_2599_);
return v_res_2601_;
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
