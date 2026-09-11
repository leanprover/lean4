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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
size_t v_x_1054__boxed_332_; lean_object* v_res_333_; 
v_x_1054__boxed_332_ = lean_unbox_usize(v_x_330_);
lean_dec(v_x_330_);
v_res_333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_329_, v_x_1054__boxed_332_, v_x_331_);
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
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_nbuckets_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_419_ = lean_array_get_size(v_data_418_);
v___x_420_ = lean_unsigned_to_nat(2u);
v_nbuckets_421_ = lean_nat_mul(v___x_419_, v___x_420_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_box(0);
v___x_424_ = lean_mk_array(v_nbuckets_421_, v___x_423_);
v___x_425_ = lean_array_propagate_mark(v_data_418_, v___x_424_);
v___x_426_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_422_, v_data_418_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
lean_object* v_key_430_; lean_object* v_tail_431_; uint8_t v___x_432_; 
v_key_430_ = lean_ctor_get(v_x_428_, 0);
v_tail_431_ = lean_ctor_get(v_x_428_, 2);
v___x_432_ = lean_name_eq(v_key_430_, v_a_427_);
if (v___x_432_ == 0)
{
v_x_428_ = v_tail_431_;
goto _start;
}
else
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec(v_a_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_438_, lean_object* v_a_439_, lean_object* v_b_440_){
_start:
{
lean_object* v_size_441_; lean_object* v_buckets_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_488_; 
v_size_441_ = lean_ctor_get(v_m_438_, 0);
v_buckets_442_ = lean_ctor_get(v_m_438_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_m_438_);
if (v_isSharedCheck_488_ == 0)
{
v___x_444_ = v_m_438_;
v_isShared_445_ = v_isSharedCheck_488_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_buckets_442_);
lean_inc(v_size_441_);
lean_dec(v_m_438_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_488_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; uint64_t v___y_448_; 
v___x_446_ = lean_array_get_size(v_buckets_442_);
if (lean_obj_tag(v_a_439_) == 0)
{
uint64_t v___x_486_; 
v___x_486_ = 1723ULL;
v___y_448_ = v___x_486_;
goto v___jp_447_;
}
else
{
uint64_t v_hash_487_; 
v_hash_487_ = lean_ctor_get_uint64(v_a_439_, sizeof(void*)*2);
v___y_448_ = v_hash_487_;
goto v___jp_447_;
}
v___jp_447_:
{
uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v_fold_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v_bkt_460_; uint8_t v___x_461_; 
v___x_449_ = 32ULL;
v___x_450_ = lean_uint64_shift_right(v___y_448_, v___x_449_);
v_fold_451_ = lean_uint64_xor(v___y_448_, v___x_450_);
v___x_452_ = 16ULL;
v___x_453_ = lean_uint64_shift_right(v_fold_451_, v___x_452_);
v___x_454_ = lean_uint64_xor(v_fold_451_, v___x_453_);
v___x_455_ = lean_uint64_to_usize(v___x_454_);
v___x_456_ = lean_usize_of_nat(v___x_446_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_sub(v___x_456_, v___x_457_);
v___x_459_ = lean_usize_land(v___x_455_, v___x_458_);
v_bkt_460_ = lean_array_uget_borrowed(v_buckets_442_, v___x_459_);
v___x_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_439_, v_bkt_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v_size_x27_463_; lean_object* v___x_464_; lean_object* v_buckets_x27_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v_size_x27_463_ = lean_nat_add(v_size_441_, v___x_462_);
lean_dec(v_size_441_);
lean_inc(v_bkt_460_);
v___x_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_464_, 0, v_a_439_);
lean_ctor_set(v___x_464_, 1, v_b_440_);
lean_ctor_set(v___x_464_, 2, v_bkt_460_);
v_buckets_x27_465_ = lean_array_uset(v_buckets_442_, v___x_459_, v___x_464_);
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = lean_nat_mul(v_size_x27_463_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = lean_nat_div(v___x_467_, v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_array_get_size(v_buckets_x27_465_);
v___x_471_ = lean_nat_dec_le(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
if (v___x_471_ == 0)
{
lean_object* v_val_472_; lean_object* v___x_474_; 
v_val_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_465_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_val_472_);
lean_ctor_set(v___x_444_, 0, v_size_x27_463_);
v___x_474_ = v___x_444_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_size_x27_463_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_val_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_477_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_buckets_x27_465_);
lean_ctor_set(v___x_444_, 0, v_size_x27_463_);
v___x_477_ = v___x_444_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_size_x27_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_buckets_x27_465_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v___x_479_; lean_object* v_buckets_x27_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
lean_inc(v_bkt_460_);
v___x_479_ = lean_box(0);
v_buckets_x27_480_ = lean_array_uset(v_buckets_442_, v___x_459_, v___x_479_);
v___x_481_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_439_, v_b_440_, v_bkt_460_);
v___x_482_ = lean_array_uset(v_buckets_x27_480_, v___x_459_, v___x_481_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_482_);
v___x_484_ = v___x_444_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_size_441_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_ks_493_; lean_object* v_vs_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_518_; 
v_ks_493_ = lean_ctor_get(v_x_489_, 0);
v_vs_494_ = lean_ctor_get(v_x_489_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_489_);
if (v_isSharedCheck_518_ == 0)
{
v___x_496_ = v_x_489_;
v_isShared_497_ = v_isSharedCheck_518_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_vs_494_);
lean_inc(v_ks_493_);
lean_dec(v_x_489_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_518_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_array_get_size(v_ks_493_);
v___x_499_ = lean_nat_dec_lt(v_x_490_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec(v_x_490_);
v___x_500_ = lean_array_push(v_ks_493_, v_x_491_);
v___x_501_ = lean_array_push(v_vs_494_, v_x_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_501_);
lean_ctor_set(v___x_496_, 0, v___x_500_);
v___x_503_ = v___x_496_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v_k_x27_505_; uint8_t v___x_506_; 
v_k_x27_505_ = lean_array_fget_borrowed(v_ks_493_, v_x_490_);
v___x_506_ = lean_name_eq(v_x_491_, v_k_x27_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; 
if (v_isShared_497_ == 0)
{
v___x_508_ = v___x_496_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_ks_493_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_vs_494_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v_x_490_, v___x_509_);
lean_dec(v_x_490_);
v_x_489_ = v___x_508_;
v_x_490_ = v___x_510_;
goto _start;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = lean_array_fset(v_ks_493_, v_x_490_, v_x_491_);
v___x_514_ = lean_array_fset(v_vs_494_, v_x_490_, v_x_492_);
lean_dec(v_x_490_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_514_);
lean_ctor_set(v___x_496_, 0, v___x_513_);
v___x_516_ = v___x_496_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_519_, lean_object* v_k_520_, lean_object* v_v_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_519_, v___x_522_, v_k_520_, v_v_521_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_525_, size_t v_x_526_, size_t v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_object* v_es_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v_j_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_es_530_ = lean_ctor_get(v_x_525_, 0);
v___x_531_ = ((size_t)31ULL);
v___x_532_ = lean_usize_land(v_x_526_, v___x_531_);
v_j_533_ = lean_usize_to_nat(v___x_532_);
v___x_534_ = lean_array_get_size(v_es_530_);
v___x_535_ = lean_nat_dec_lt(v_j_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v_j_533_);
lean_dec(v_x_529_);
lean_dec(v_x_528_);
return v_x_525_;
}
else
{
lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_574_; 
lean_inc_ref(v_es_530_);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_x_525_, 0);
lean_dec(v_unused_575_);
v___x_537_ = v_x_525_;
v_isShared_538_ = v_isSharedCheck_574_;
goto v_resetjp_536_;
}
else
{
lean_dec(v_x_525_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_574_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_v_539_; lean_object* v___x_540_; lean_object* v_xs_x27_541_; lean_object* v___y_543_; 
v_v_539_ = lean_array_fget(v_es_530_, v_j_533_);
v___x_540_ = lean_box(0);
v_xs_x27_541_ = lean_array_fset(v_es_530_, v_j_533_, v___x_540_);
switch(lean_obj_tag(v_v_539_))
{
case 0:
{
lean_object* v_key_548_; lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_key_548_ = lean_ctor_get(v_v_539_, 0);
v_val_549_ = lean_ctor_get(v_v_539_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_v_539_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v_v_539_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_inc(v_key_548_);
lean_dec(v_v_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___x_553_; 
v___x_553_ = lean_name_eq(v_x_528_, v_key_548_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_del_object(v___x_551_);
v___x_554_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_548_, v_val_549_, v_x_528_, v_x_529_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___y_543_ = v___x_555_;
goto v___jp_542_;
}
else
{
lean_object* v___x_557_; 
lean_dec(v_val_549_);
lean_dec(v_key_548_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_x_529_);
lean_ctor_set(v___x_551_, 0, v_x_528_);
v___x_557_ = v___x_551_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_x_528_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_x_529_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_543_ = v___x_557_;
goto v___jp_542_;
}
}
}
}
case 1:
{
lean_object* v_node_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_572_; 
v_node_560_ = lean_ctor_get(v_v_539_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_v_539_);
if (v_isSharedCheck_572_ == 0)
{
v___x_562_ = v_v_539_;
v_isShared_563_ = v_isSharedCheck_572_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_node_560_);
lean_dec(v_v_539_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_572_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_564_ = ((size_t)5ULL);
v___x_565_ = lean_usize_shift_right(v_x_526_, v___x_564_);
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_x_527_, v___x_566_);
v___x_568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_560_, v___x_565_, v___x_567_, v_x_528_, v_x_529_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_568_);
v___x_570_ = v___x_562_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_543_ = v___x_570_;
goto v___jp_542_;
}
}
}
default: 
{
lean_object* v___x_573_; 
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_x_528_);
lean_ctor_set(v___x_573_, 1, v_x_529_);
v___y_543_ = v___x_573_;
goto v___jp_542_;
}
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_array_fset(v_xs_x27_541_, v_j_533_, v___y_543_);
lean_dec(v_j_533_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_544_);
v___x_546_ = v___x_537_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
else
{
lean_object* v_ks_576_; lean_object* v_vs_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_595_; 
v_ks_576_ = lean_ctor_get(v_x_525_, 0);
v_vs_577_ = lean_ctor_get(v_x_525_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_595_ == 0)
{
v___x_579_ = v_x_525_;
v_isShared_580_ = v_isSharedCheck_595_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_vs_577_);
lean_inc(v_ks_576_);
lean_dec(v_x_525_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_595_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_ks_576_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_vs_577_);
v___x_582_ = v_reuseFailAlloc_594_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v_newNode_583_; size_t v___x_584_; uint8_t v___x_585_; 
v_newNode_583_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_582_, v_x_528_, v_x_529_);
v___x_584_ = ((size_t)7ULL);
v___x_585_ = lean_usize_dec_le(v___x_584_, v_x_527_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_583_);
v___x_587_ = lean_unsigned_to_nat(4u);
v___x_588_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
lean_dec(v___x_586_);
if (v___x_588_ == 0)
{
lean_object* v_ks_589_; lean_object* v_vs_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_ks_589_ = lean_ctor_get(v_newNode_583_, 0);
lean_inc_ref(v_ks_589_);
v_vs_590_ = lean_ctor_get(v_newNode_583_, 1);
lean_inc_ref(v_vs_590_);
lean_dec_ref(v_newNode_583_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_527_, v_ks_589_, v_vs_590_, v___x_591_, v___x_592_);
lean_dec_ref(v_vs_590_);
lean_dec_ref(v_ks_589_);
return v___x_593_;
}
else
{
return v_newNode_583_;
}
}
else
{
return v_newNode_583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_i_599_, lean_object* v_entries_600_){
_start:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_array_get_size(v_keys_597_);
v___x_602_ = lean_nat_dec_lt(v_i_599_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_i_599_);
return v_entries_600_;
}
else
{
lean_object* v_k_603_; lean_object* v_v_604_; uint64_t v___y_606_; 
v_k_603_ = lean_array_fget_borrowed(v_keys_597_, v_i_599_);
v_v_604_ = lean_array_fget_borrowed(v_vals_598_, v_i_599_);
if (lean_obj_tag(v_k_603_) == 0)
{
uint64_t v___x_617_; 
v___x_617_ = 1723ULL;
v___y_606_ = v___x_617_;
goto v___jp_605_;
}
else
{
uint64_t v_hash_618_; 
v_hash_618_ = lean_ctor_get_uint64(v_k_603_, sizeof(void*)*2);
v___y_606_ = v_hash_618_;
goto v___jp_605_;
}
v___jp_605_:
{
size_t v_h_607_; size_t v___x_608_; lean_object* v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v_h_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_h_607_ = lean_uint64_to_usize(v___y_606_);
v___x_608_ = ((size_t)5ULL);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_sub(v_depth_596_, v___x_610_);
v___x_612_ = lean_usize_mul(v___x_608_, v___x_611_);
v_h_613_ = lean_usize_shift_right(v_h_607_, v___x_612_);
v___x_614_ = lean_nat_add(v_i_599_, v___x_609_);
lean_dec(v_i_599_);
lean_inc(v_v_604_);
lean_inc(v_k_603_);
v___x_615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_600_, v_h_613_, v_depth_596_, v_k_603_, v_v_604_);
v_i_599_ = v___x_614_;
v_entries_600_ = v___x_615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_619_, lean_object* v_keys_620_, lean_object* v_vals_621_, lean_object* v_i_622_, lean_object* v_entries_623_){
_start:
{
size_t v_depth_boxed_624_; lean_object* v_res_625_; 
v_depth_boxed_624_ = lean_unbox_usize(v_depth_619_);
lean_dec(v_depth_619_);
v_res_625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_624_, v_keys_620_, v_vals_621_, v_i_622_, v_entries_623_);
lean_dec_ref(v_vals_621_);
lean_dec_ref(v_keys_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
size_t v_x_1430__boxed_631_; size_t v_x_1431__boxed_632_; lean_object* v_res_633_; 
v_x_1430__boxed_631_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_x_1431__boxed_632_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_626_, v_x_1430__boxed_631_, v_x_1431__boxed_632_, v_x_629_, v_x_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
uint64_t v___y_638_; 
if (lean_obj_tag(v_x_635_) == 0)
{
uint64_t v___x_642_; 
v___x_642_ = 1723ULL;
v___y_638_ = v___x_642_;
goto v___jp_637_;
}
else
{
uint64_t v_hash_643_; 
v_hash_643_ = lean_ctor_get_uint64(v_x_635_, sizeof(void*)*2);
v___y_638_ = v_hash_643_;
goto v___jp_637_;
}
v___jp_637_:
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_uint64_to_usize(v___y_638_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_634_, v___x_639_, v___x_640_, v_x_635_, v_x_636_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
uint8_t v_stage_u2081_647_; 
v_stage_u2081_647_ = lean_ctor_get_uint8(v_x_644_, sizeof(void*)*2);
if (v_stage_u2081_647_ == 0)
{
lean_object* v_map_u2081_648_; lean_object* v_map_u2082_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_map_u2081_648_ = lean_ctor_get(v_x_644_, 0);
v_map_u2082_649_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_x_644_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_map_u2082_649_);
lean_inc(v_map_u2081_648_);
lean_dec(v_x_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_649_, v_x_645_, v_x_646_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_map_u2081_648_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_656_, sizeof(void*)*2, v_stage_u2081_647_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_map_u2081_658_; lean_object* v_map_u2082_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_map_u2081_658_ = lean_ctor_get(v_x_644_, 0);
v_map_u2082_659_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v_x_644_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_map_u2082_659_);
lean_inc(v_map_u2081_658_);
lean_dec(v_x_644_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_658_, v_x_645_, v_x_646_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_map_u2082_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*2, v_stage_u2081_647_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_unsigned_to_nat(32u);
v___x_669_ = lean_mk_empty_array_with_capacity(v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_671_ = ((size_t)5ULL);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_unsigned_to_nat(32u);
v___x_674_ = lean_mk_empty_array_with_capacity(v___x_673_);
v___x_675_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_676_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
lean_ctor_set(v___x_676_, 2, v___x_672_);
lean_ctor_set(v___x_676_, 3, v___x_672_);
lean_ctor_set_usize(v___x_676_, 4, v___x_671_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_677_, lean_object* v_ns_678_, lean_object* v_b_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_677_, v_ns_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_682_ = l_Lean_PersistentArray_push___redArg(v___x_681_, v_b_679_);
v___x_683_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_677_, v_ns_678_, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_val_684_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v___x_680_, 1);
v___x_685_ = l_Lean_PersistentArray_push___redArg(v_val_684_, v_b_679_);
v___x_686_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_677_, v_ns_678_, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_687_, lean_object* v_scopedEntries_688_, lean_object* v_ns_689_, lean_object* v_b_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_688_, v_ns_689_, v_b_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_696_, v_x_697_, v_x_698_);
lean_dec(v_x_698_);
lean_dec_ref(v_x_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_701_, v_x_702_, v_x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_709_, v_x_710_, v_x_711_);
lean_dec(v_x_711_);
lean_dec_ref(v_x_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_714_, v_a_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_717_, lean_object* v_m_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_717_, v_m_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_m_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_722_, v_x_723_, v_x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_726_, lean_object* v_m_727_, lean_object* v_a_728_, lean_object* v_b_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_727_, v_a_728_, v_b_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, size_t v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_732_, v_x_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
size_t v_x_1731__boxed_740_; lean_object* v_res_741_; 
v_x_1731__boxed_740_ = lean_unbox_usize(v_x_738_);
lean_dec(v_x_738_);
v_res_741_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_736_, v_x_737_, v_x_1731__boxed_740_, v_x_739_);
lean_dec(v_x_739_);
lean_dec_ref(v_x_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_742_, lean_object* v_a_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_746_, lean_object* v_a_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_746_, v_a_747_, v_x_748_);
lean_dec(v_x_748_);
lean_dec(v_a_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, size_t v_x_752_, size_t v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_751_, v_x_752_, v_x_753_, v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
size_t v_x_1747__boxed_763_; size_t v_x_1748__boxed_764_; lean_object* v_res_765_; 
v_x_1747__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_x_1748__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_res_765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_757_, v_x_758_, v_x_1747__boxed_763_, v_x_1748__boxed_764_, v_x_761_, v_x_762_);
return v_res_765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_766_, lean_object* v_a_767_, lean_object* v_x_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_770_, lean_object* v_a_771_, lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_770_, v_a_771_, v_x_772_);
lean_dec(v_x_772_);
lean_dec(v_a_771_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_775_, lean_object* v_data_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_778_, lean_object* v_a_779_, lean_object* v_b_780_, lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_779_, v_b_780_, v_x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_heq_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_784_, v_vals_785_, v_i_787_, v_k_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_790_, lean_object* v_keys_791_, lean_object* v_vals_792_, lean_object* v_heq_793_, lean_object* v_i_794_, lean_object* v_k_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_790_, v_keys_791_, v_vals_792_, v_heq_793_, v_i_794_, v_k_795_);
lean_dec(v_k_795_);
lean_dec_ref(v_vals_792_);
lean_dec_ref(v_keys_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_797_, lean_object* v_n_798_, lean_object* v_k_799_, lean_object* v_v_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_798_, v_k_799_, v_v_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_802_, size_t v_depth_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_heq_806_, lean_object* v_i_807_, lean_object* v_entries_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_803_, v_keys_804_, v_vals_805_, v_i_807_, v_entries_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_810_, lean_object* v_depth_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_heq_814_, lean_object* v_i_815_, lean_object* v_entries_816_){
_start:
{
size_t v_depth_boxed_817_; lean_object* v_res_818_; 
v_depth_boxed_817_ = lean_unbox_usize(v_depth_811_);
lean_dec(v_depth_811_);
v_res_818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_810_, v_depth_boxed_817_, v_keys_812_, v_vals_813_, v_heq_814_, v_i_815_, v_entries_816_);
lean_dec_ref(v_vals_813_);
lean_dec_ref(v_keys_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_819_, lean_object* v_i_820_, lean_object* v_source_821_, lean_object* v_target_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_820_, v_source_821_, v_target_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_825_, v_x_826_, v_x_827_, v_x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_834_, lean_object* v_as_835_, size_t v_sz_836_, size_t v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_a_842_; uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_837_, v_sz_836_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec_ref(v_descr_834_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_838_);
return v___x_847_;
}
else
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_888_; 
v_fst_848_ = lean_ctor_get(v_b_838_, 0);
v_snd_849_ = lean_ctor_get(v_b_838_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_b_838_);
if (v_isSharedCheck_888_ == 0)
{
v___x_851_ = v_b_838_;
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_b_838_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_888_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_a_853_; 
v_a_853_ = lean_array_uget_borrowed(v_as_835_, v_i_837_);
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_ofOLeanEntry_855_; lean_object* v_addEntry_856_; lean_object* v___x_857_; 
v_a_854_ = lean_ctor_get(v_a_853_, 0);
v_ofOLeanEntry_855_ = lean_ctor_get(v_descr_834_, 2);
v_addEntry_856_ = lean_ctor_get(v_descr_834_, 4);
lean_inc_ref(v_ofOLeanEntry_855_);
lean_inc_ref(v___y_839_);
lean_inc(v_a_854_);
lean_inc(v_fst_848_);
v___x_857_ = lean_apply_4(v_ofOLeanEntry_855_, v_fst_848_, v_a_854_, v___y_839_, lean_box(0));
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
lean_inc(v_addEntry_856_);
v___x_859_ = lean_apply_2(v_addEntry_856_, v_fst_848_, v_a_858_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_859_);
v___x_861_ = v___x_851_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_snd_849_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_842_ = v___x_861_;
goto v___jp_841_;
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
lean_dec_ref(v_descr_834_);
v_a_863_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_857_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v_a_872_; lean_object* v_ofOLeanEntry_873_; lean_object* v___x_874_; 
v_a_871_ = lean_ctor_get(v_a_853_, 0);
v_a_872_ = lean_ctor_get(v_a_853_, 1);
v_ofOLeanEntry_873_ = lean_ctor_get(v_descr_834_, 2);
lean_inc_ref(v_ofOLeanEntry_873_);
lean_inc_ref(v___y_839_);
lean_inc(v_a_872_);
lean_inc(v_fst_848_);
v___x_874_ = lean_apply_4(v_ofOLeanEntry_873_, v_fst_848_, v_a_872_, v___y_839_, lean_box(0));
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
lean_inc(v_a_871_);
v___x_876_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_849_, v_a_871_, v_a_875_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_876_);
v___x_878_ = v___x_851_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
v_a_842_ = v___x_878_;
goto v___jp_841_;
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
lean_dec_ref(v_descr_834_);
v_a_880_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_874_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_874_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
v___jp_841_:
{
size_t v___x_843_; size_t v___x_844_; 
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_i_837_, v___x_843_);
v_i_837_ = v___x_844_;
v_b_838_ = v_a_842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_889_, lean_object* v_as_890_, lean_object* v_sz_891_, lean_object* v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v_sz_boxed_896_ = lean_unbox_usize(v_sz_891_);
lean_dec(v_sz_891_);
v_i_boxed_897_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_889_, v_as_890_, v_sz_boxed_896_, v_i_boxed_897_, v_b_893_, v___y_894_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_as_890_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_899_, lean_object* v_as_900_, size_t v_sz_901_, size_t v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec_ref(v_descr_899_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_903_);
return v___x_907_;
}
else
{
lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_933_; 
v_fst_908_ = lean_ctor_get(v_b_903_, 0);
v_snd_909_ = lean_ctor_get(v_b_903_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_b_903_);
if (v_isSharedCheck_933_ == 0)
{
v___x_911_ = v_b_903_;
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v_b_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_a_913_; lean_object* v___x_915_; 
v_a_913_ = lean_array_uget_borrowed(v_as_900_, v_i_902_);
if (v_isShared_912_ == 0)
{
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_fst_908_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_snd_909_);
v___x_915_ = v_reuseFailAlloc_932_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_sz_916_ = lean_array_size(v_a_913_);
v___x_917_ = ((size_t)0ULL);
lean_inc_ref(v_descr_899_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_899_, v_a_913_, v_sz_916_, v___x_917_, v___x_915_, v___y_904_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_931_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v_fst_920_ = lean_ctor_get(v_a_919_, 0);
v_snd_921_ = lean_ctor_get(v_a_919_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_931_ == 0)
{
v___x_923_ = v_a_919_;
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_inc(v_fst_920_);
lean_dec(v_a_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_snd_921_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
size_t v___x_927_; size_t v___x_928_; 
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_902_, v___x_927_);
v_i_902_ = v___x_928_;
v_b_903_ = v___x_926_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_899_);
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_934_, lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_942_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_934_, v_as_935_, v_sz_boxed_941_, v_i_boxed_942_, v_b_938_, v___y_939_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_944_, lean_object* v_as_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_mkInitial_948_; lean_object* v_finalizeImport_949_; lean_object* v___x_950_; 
v_mkInitial_948_ = lean_ctor_get(v_descr_944_, 1);
v_finalizeImport_949_ = lean_ctor_get(v_descr_944_, 5);
lean_inc(v_finalizeImport_949_);
lean_inc_ref(v_mkInitial_948_);
v___x_950_ = lean_apply_1(v_mkInitial_948_, lean_box(0));
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; size_t v_sz_955_; size_t v___x_956_; lean_object* v___x_957_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = 1;
v___x_953_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_a_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v_sz_955_ = lean_array_size(v_as_945_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_944_, v_as_945_, v_sz_955_, v___x_956_, v___x_954_, v_a_946_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_979_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_979_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_979_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_979_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_978_; 
v_fst_962_ = lean_ctor_get(v_a_958_, 0);
v_snd_963_ = lean_ctor_get(v_a_958_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_978_ == 0)
{
v___x_965_ = v_a_958_;
v_isShared_966_ = v_isSharedCheck_978_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_snd_963_);
lean_inc(v_fst_962_);
lean_dec(v_a_958_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_978_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_967_ = lean_apply_1(v_finalizeImport_949_, v_fst_962_);
v___x_968_ = l_Lean_NameSet_empty;
v___x_969_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*2, v___x_952_);
v___x_970_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 1, v___x_970_);
lean_ctor_set(v___x_965_, 0, v___x_969_);
v___x_972_ = v___x_965_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_977_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_snd_963_);
lean_ctor_set(v___x_973_, 2, v___x_970_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_973_);
v___x_975_ = v___x_960_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_finalizeImport_949_);
v_a_980_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_957_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_957_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_finalizeImport_949_);
lean_dec_ref(v_descr_944_);
v_a_988_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_950_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_950_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_996_, lean_object* v_as_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_996_, v_as_997_, v_a_998_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_as_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1001_, lean_object* v_00_u03b2_1002_, lean_object* v_00_u03c3_1003_, lean_object* v_descr_1004_, lean_object* v_as_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1004_, v_as_1005_, v_a_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_00_u03c3_1011_, lean_object* v_descr_1012_, lean_object* v_as_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1009_, v_00_u03b2_1010_, v_00_u03c3_1011_, v_descr_1012_, v_as_1013_, v_a_1014_);
lean_dec_ref(v_a_1014_);
lean_dec_ref(v_as_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03c3_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_descr_1020_, lean_object* v_as_1021_, size_t v_sz_1022_, size_t v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1020_, v_as_1021_, v_sz_1022_, v_i_1023_, v_b_1024_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03c3_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_descr_1031_, lean_object* v_as_1032_, lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1028_, v_00_u03c3_1029_, v_00_u03b2_1030_, v_descr_1031_, v_as_1032_, v_sz_boxed_1038_, v_i_boxed_1039_, v_b_1035_, v___y_1036_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_as_1032_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03c3_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_descr_1044_, lean_object* v_as_1045_, size_t v_sz_1046_, size_t v_i_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1044_, v_as_1045_, v_sz_1046_, v_i_1047_, v_b_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03c3_1053_, lean_object* v_00_u03b2_1054_, lean_object* v_descr_1055_, lean_object* v_as_1056_, lean_object* v_sz_1057_, lean_object* v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
size_t v_sz_boxed_1062_; size_t v_i_boxed_1063_; lean_object* v_res_1064_; 
v_sz_boxed_1062_ = lean_unbox_usize(v_sz_1057_);
lean_dec(v_sz_1057_);
v_i_boxed_1063_ = lean_unbox_usize(v_i_1058_);
lean_dec(v_i_1058_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1052_, v_00_u03c3_1053_, v_00_u03b2_1054_, v_descr_1055_, v_as_1056_, v_sz_boxed_1062_, v_i_boxed_1063_, v_b_1059_, v___y_1060_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1065_, lean_object* v_descr_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
if (lean_obj_tag(v_a_1068_) == 0)
{
lean_object* v___x_1070_; 
lean_dec(v_a_1067_);
lean_dec_ref(v_descr_1066_);
v___x_1070_ = l_List_reverse___redArg(v_a_1069_);
return v___x_1070_;
}
else
{
lean_object* v_head_1071_; lean_object* v_tail_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1097_; 
v_head_1071_ = lean_ctor_get(v_a_1068_, 0);
v_tail_1072_ = lean_ctor_get(v_a_1068_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1068_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1074_ = v_a_1068_;
v_isShared_1075_ = v_isSharedCheck_1097_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_tail_1072_);
lean_inc(v_head_1071_);
lean_dec(v_a_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1097_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___y_1077_; lean_object* v_state_1082_; lean_object* v_activeScopes_1083_; uint8_t v_delimitsLocal_1084_; uint8_t v___x_1085_; 
v_state_1082_ = lean_ctor_get(v_head_1071_, 0);
v_activeScopes_1083_ = lean_ctor_get(v_head_1071_, 1);
v_delimitsLocal_1084_ = lean_ctor_get_uint8(v_head_1071_, sizeof(void*)*2);
v___x_1085_ = l_Lean_NameSet_contains(v_activeScopes_1083_, v_a_1065_);
if (v___x_1085_ == 0)
{
v___y_1077_ = v_head_1071_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_activeScopes_1083_);
lean_inc(v_state_1082_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_head_1071_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_head_1071_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_head_1071_, 0);
lean_dec(v_unused_1096_);
v___x_1087_ = v_head_1071_;
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_head_1071_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_addEntry_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v_addEntry_1089_ = lean_ctor_get(v_descr_1066_, 4);
lean_inc(v_addEntry_1089_);
lean_inc(v_a_1067_);
v___x_1090_ = lean_apply_2(v_addEntry_1089_, v_state_1082_, v_a_1067_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_activeScopes_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1093_, sizeof(void*)*2, v_delimitsLocal_1084_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1077_ = v___x_1092_;
goto v___jp_1076_;
}
}
}
v___jp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_a_1069_);
lean_ctor_set(v___x_1074_, 0, v___y_1077_);
v___x_1079_ = v___x_1074_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___y_1077_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_a_1069_);
v___x_1079_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
v_a_1068_ = v_tail_1072_;
v_a_1069_ = v___x_1079_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1098_, lean_object* v_descr_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1098_, v_descr_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
if (lean_obj_tag(v_a_1106_) == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_a_1105_);
lean_dec_ref(v_descr_1104_);
v___x_1108_ = l_List_reverse___redArg(v_a_1107_);
return v___x_1108_;
}
else
{
lean_object* v_head_1109_; lean_object* v_tail_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1130_; 
v_head_1109_ = lean_ctor_get(v_a_1106_, 0);
v_tail_1110_ = lean_ctor_get(v_a_1106_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1106_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1112_ = v_a_1106_;
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_tail_1110_);
lean_inc(v_head_1109_);
lean_dec(v_a_1106_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_addEntry_1114_; lean_object* v_state_1115_; lean_object* v_activeScopes_1116_; uint8_t v_delimitsLocal_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1129_; 
v_addEntry_1114_ = lean_ctor_get(v_descr_1104_, 4);
v_state_1115_ = lean_ctor_get(v_head_1109_, 0);
v_activeScopes_1116_ = lean_ctor_get(v_head_1109_, 1);
v_delimitsLocal_1117_ = lean_ctor_get_uint8(v_head_1109_, sizeof(void*)*2);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_head_1109_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1119_ = v_head_1109_;
v_isShared_1120_ = v_isSharedCheck_1129_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_activeScopes_1116_);
lean_inc(v_state_1115_);
lean_dec(v_head_1109_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1129_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_inc(v_addEntry_1114_);
lean_inc(v_a_1105_);
v___x_1121_ = lean_apply_2(v_addEntry_1114_, v_state_1115_, v_a_1105_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_activeScopes_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*2, v_delimitsLocal_1117_);
v___x_1123_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_a_1107_);
lean_ctor_set(v___x_1112_, 0, v___x_1123_);
v___x_1125_ = v___x_1112_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_a_1107_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v_a_1106_ = v_tail_1110_;
v_a_1107_ = v___x_1125_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1131_, lean_object* v_s_1132_, lean_object* v_e_1133_){
_start:
{
if (lean_obj_tag(v_e_1133_) == 0)
{
lean_object* v_stateStack_1134_; lean_object* v_scopedEntries_1135_; lean_object* v_newEntries_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1156_; 
v_stateStack_1134_ = lean_ctor_get(v_s_1132_, 0);
v_scopedEntries_1135_ = lean_ctor_get(v_s_1132_, 1);
v_newEntries_1136_ = lean_ctor_get(v_s_1132_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_s_1132_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1138_ = v_s_1132_;
v_isShared_1139_ = v_isSharedCheck_1156_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_newEntries_1136_);
lean_inc(v_scopedEntries_1135_);
lean_inc(v_stateStack_1134_);
lean_dec(v_s_1132_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1156_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1155_; 
v_a_1140_ = lean_ctor_get(v_e_1133_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_e_1133_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1142_ = v_e_1133_;
v_isShared_1143_ = v_isSharedCheck_1155_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v_e_1133_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1155_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_toOLeanEntry_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v_toOLeanEntry_1144_ = lean_ctor_get(v_descr_1131_, 3);
lean_inc(v_toOLeanEntry_1144_);
v___x_1145_ = lean_box(0);
lean_inc(v_a_1140_);
v___x_1146_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1131_, v_a_1140_, v_stateStack_1134_, v___x_1145_);
v___x_1147_ = lean_apply_1(v_toOLeanEntry_1144_, v_a_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1147_);
v___x_1149_ = v___x_1142_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v_newEntries_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 2, v___x_1150_);
lean_ctor_set(v___x_1138_, 0, v___x_1146_);
v___x_1152_ = v___x_1138_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_scopedEntries_1135_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1157_; lean_object* v_scopedEntries_1158_; lean_object* v_newEntries_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1181_; 
v_stateStack_1157_ = lean_ctor_get(v_s_1132_, 0);
v_scopedEntries_1158_ = lean_ctor_get(v_s_1132_, 1);
v_newEntries_1159_ = lean_ctor_get(v_s_1132_, 2);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_s_1132_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1161_ = v_s_1132_;
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_newEntries_1159_);
lean_inc(v_scopedEntries_1158_);
lean_inc(v_stateStack_1157_);
lean_dec(v_s_1132_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1180_; 
v_a_1163_ = lean_ctor_get(v_e_1133_, 0);
v_a_1164_ = lean_ctor_get(v_e_1133_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_e_1133_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1166_ = v_e_1133_;
v_isShared_1167_ = v_isSharedCheck_1180_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_inc(v_a_1163_);
lean_dec(v_e_1133_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1180_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_toOLeanEntry_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v_toOLeanEntry_1168_ = lean_ctor_get(v_descr_1131_, 3);
lean_inc(v_toOLeanEntry_1168_);
v___x_1169_ = lean_box(0);
lean_inc_n(v_a_1164_, 2);
v___x_1170_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1163_, v_descr_1131_, v_a_1164_, v_stateStack_1157_, v___x_1169_);
lean_inc(v_a_1163_);
v___x_1171_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1158_, v_a_1163_, v_a_1164_);
v___x_1172_ = lean_apply_1(v_toOLeanEntry_1168_, v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1172_);
v___x_1174_ = v___x_1166_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_newEntries_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1175_);
lean_ctor_set(v___x_1161_, 1, v___x_1171_);
lean_ctor_set(v___x_1161_, 0, v___x_1170_);
v___x_1177_ = v___x_1161_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_00_u03c3_1184_, lean_object* v_descr_1185_, lean_object* v_s_1186_, lean_object* v_e_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1185_, v_s_1186_, v_e_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1189_, lean_object* v_00_u03b2_1190_, lean_object* v_00_u03b1_1191_, lean_object* v_descr_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1197_, lean_object* v_a_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_00_u03b1_1200_, lean_object* v_descr_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1198_, v_descr_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1206_, lean_object* v_a_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_00_u03b1_1209_, lean_object* v_descr_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1206_, v_a_1207_, v_00_u03b2_1208_, v_00_u03b1_1209_, v_descr_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1215_, lean_object* v_env_1216_, lean_object* v_as_1217_, size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_b_1220_){
_start:
{
lean_object* v_a_1222_; uint8_t v___x_1226_; 
v___x_1226_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1226_ == 0)
{
lean_dec_ref(v_env_1216_);
lean_dec_ref(v_descr_1215_);
return v_b_1220_;
}
else
{
lean_object* v_snd_1227_; lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1328_; 
v_snd_1227_ = lean_ctor_get(v_b_1220_, 1);
v_fst_1228_ = lean_ctor_get(v_b_1220_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_b_1220_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1230_ = v_b_1220_;
v_isShared_1231_ = v_isSharedCheck_1328_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1227_);
lean_inc(v_fst_1228_);
lean_dec(v_b_1220_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1328_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1327_; 
v_fst_1232_ = lean_ctor_get(v_snd_1227_, 0);
v_snd_1233_ = lean_ctor_get(v_snd_1227_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1227_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1235_ = v_snd_1227_;
v_isShared_1236_ = v_isSharedCheck_1327_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_inc(v_fst_1232_);
lean_dec(v_snd_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1327_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_array_uget(v_as_1217_, v_i_1219_);
if (lean_obj_tag(v_a_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1287_; 
v_a_1238_ = lean_ctor_get(v_a_1237_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1237_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1240_ = v_a_1237_;
v_isShared_1241_ = v_isSharedCheck_1287_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v_a_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1287_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_exportEntry_x3f_1242_; lean_object* v___x_1243_; lean_object* v_exported_1244_; lean_object* v_server_1245_; lean_object* v_private_1246_; lean_object* v___y_1248_; lean_object* v_server_1249_; lean_object* v_exported_1268_; 
v_exportEntry_x3f_1242_ = lean_ctor_get(v_descr_1215_, 6);
lean_inc_ref(v_exportEntry_x3f_1242_);
lean_inc_ref(v_env_1216_);
v___x_1243_ = lean_apply_2(v_exportEntry_x3f_1242_, v_env_1216_, v_a_1238_);
v_exported_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_exported_1244_);
v_server_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_server_1245_);
v_private_1246_ = lean_ctor_get(v___x_1243_, 2);
lean_inc(v_private_1246_);
lean_dec_ref(v___x_1243_);
if (lean_obj_tag(v_exported_1244_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_val_1278_ = lean_ctor_get(v_exported_1244_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_exported_1244_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v_exported_1244_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v_exported_1244_);
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
v___x_1284_ = lean_array_push(v_fst_1228_, v___x_1283_);
v_exported_1268_ = v___x_1284_;
goto v___jp_1267_;
}
}
}
else
{
lean_dec(v_exported_1244_);
v_exported_1268_ = v_fst_1228_;
goto v___jp_1267_;
}
v___jp_1247_:
{
if (lean_obj_tag(v_private_1246_) == 1)
{
lean_object* v_val_1250_; lean_object* v___x_1252_; 
v_val_1250_ = lean_ctor_get(v_private_1246_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v_private_1246_, 1);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v_val_1250_);
v___x_1252_ = v___x_1240_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_val_1250_);
v___x_1252_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_array_push(v_snd_1233_, v___x_1252_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1253_);
lean_ctor_set(v___x_1235_, 0, v_server_1249_);
v___x_1255_ = v___x_1235_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_server_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1255_);
lean_ctor_set(v___x_1230_, 0, v___y_1248_);
v___x_1257_ = v___x_1230_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___y_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
v_a_1222_ = v___x_1257_;
goto v___jp_1221_;
}
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v_private_1246_);
lean_del_object(v___x_1240_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_server_1249_);
v___x_1262_ = v___x_1235_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_server_1249_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_snd_1233_);
v___x_1262_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1262_);
lean_ctor_set(v___x_1230_, 0, v___y_1248_);
v___x_1264_ = v___x_1230_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___y_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_a_1222_ = v___x_1264_;
goto v___jp_1221_;
}
}
}
}
v___jp_1267_:
{
if (lean_obj_tag(v_server_1245_) == 1)
{
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
v_val_1269_ = lean_ctor_get(v_server_1245_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_server_1245_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1271_ = v_server_1245_;
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v_server_1245_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 0);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_val_1269_);
v___x_1274_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_array_push(v_fst_1232_, v___x_1274_);
v___y_1248_ = v_exported_1268_;
v_server_1249_ = v___x_1275_;
goto v___jp_1247_;
}
}
}
else
{
lean_dec(v_server_1245_);
v___y_1248_ = v_exported_1268_;
v_server_1249_ = v_fst_1232_;
goto v___jp_1247_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1326_; 
v_a_1288_ = lean_ctor_get(v_a_1237_, 0);
v_a_1289_ = lean_ctor_get(v_a_1237_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1237_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1291_ = v_a_1237_;
v_isShared_1292_ = v_isSharedCheck_1326_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v_a_1237_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1326_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_exportEntry_x3f_1293_; lean_object* v___x_1294_; lean_object* v_exported_1295_; lean_object* v_server_1296_; lean_object* v_private_1297_; lean_object* v___y_1299_; lean_object* v_server_1300_; lean_object* v_exported_1319_; 
v_exportEntry_x3f_1293_ = lean_ctor_get(v_descr_1215_, 6);
lean_inc_ref(v_exportEntry_x3f_1293_);
lean_inc_ref(v_env_1216_);
v___x_1294_ = lean_apply_2(v_exportEntry_x3f_1293_, v_env_1216_, v_a_1289_);
v_exported_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_exported_1295_);
v_server_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_server_1296_);
v_private_1297_ = lean_ctor_get(v___x_1294_, 2);
lean_inc(v_private_1297_);
lean_dec_ref(v___x_1294_);
if (lean_obj_tag(v_exported_1295_) == 1)
{
lean_object* v_val_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_val_1323_ = lean_ctor_get(v_exported_1295_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v_exported_1295_, 1);
lean_inc(v_a_1288_);
v___x_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_a_1288_);
lean_ctor_set(v___x_1324_, 1, v_val_1323_);
v___x_1325_ = lean_array_push(v_fst_1228_, v___x_1324_);
v_exported_1319_ = v___x_1325_;
goto v___jp_1318_;
}
else
{
lean_dec(v_exported_1295_);
v_exported_1319_ = v_fst_1228_;
goto v___jp_1318_;
}
v___jp_1298_:
{
if (lean_obj_tag(v_private_1297_) == 1)
{
lean_object* v_val_1301_; lean_object* v___x_1303_; 
v_val_1301_ = lean_ctor_get(v_private_1297_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v_private_1297_, 1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v_val_1301_);
v___x_1303_ = v___x_1291_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1288_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_val_1301_);
v___x_1303_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_array_push(v_snd_1233_, v___x_1303_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1304_);
lean_ctor_set(v___x_1235_, 0, v_server_1300_);
v___x_1306_ = v___x_1235_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_server_1300_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1306_);
lean_ctor_set(v___x_1230_, 0, v___y_1299_);
v___x_1308_ = v___x_1230_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___y_1299_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_a_1222_ = v___x_1308_;
goto v___jp_1221_;
}
}
}
}
else
{
lean_object* v___x_1313_; 
lean_dec(v_private_1297_);
lean_del_object(v___x_1291_);
lean_dec(v_a_1288_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_server_1300_);
v___x_1313_ = v___x_1235_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_server_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_snd_1233_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1313_);
lean_ctor_set(v___x_1230_, 0, v___y_1299_);
v___x_1315_ = v___x_1230_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___y_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
v_a_1222_ = v___x_1315_;
goto v___jp_1221_;
}
}
}
}
v___jp_1318_:
{
if (lean_obj_tag(v_server_1296_) == 1)
{
lean_object* v_val_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_val_1320_ = lean_ctor_get(v_server_1296_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v_server_1296_, 1);
lean_inc(v_a_1288_);
v___x_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1288_);
lean_ctor_set(v___x_1321_, 1, v_val_1320_);
v___x_1322_ = lean_array_push(v_fst_1232_, v___x_1321_);
v___y_1299_ = v_exported_1319_;
v_server_1300_ = v___x_1322_;
goto v___jp_1298_;
}
else
{
lean_dec(v_server_1296_);
v___y_1299_ = v_exported_1319_;
v_server_1300_ = v_fst_1232_;
goto v___jp_1298_;
}
}
}
}
}
}
}
v___jp_1221_:
{
size_t v___x_1223_; size_t v___x_1224_; 
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1219_, v___x_1223_);
v_i_1219_ = v___x_1224_;
v_b_1220_ = v_a_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1329_, lean_object* v_env_1330_, lean_object* v_as_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_b_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1329_, v_env_1330_, v_as_1331_, v_sz_boxed_1335_, v_i_boxed_1336_, v_b_1334_);
lean_dec_ref(v_as_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1345_, lean_object* v_env_1346_, lean_object* v_s_1347_){
_start:
{
lean_object* v_newEntries_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1365_; 
v_newEntries_1348_ = lean_ctor_get(v_s_1347_, 2);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_s_1347_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1366_ = lean_ctor_get(v_s_1347_, 1);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_s_1347_, 0);
lean_dec(v_unused_1367_);
v___x_1350_ = v_s_1347_;
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_newEntries_1348_);
lean_dec(v_s_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; lean_object* v_snd_1358_; lean_object* v_fst_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1363_; 
v___x_1352_ = lean_array_mk(v_newEntries_1348_);
v___x_1353_ = l_Array_reverse___redArg(v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1355_ = lean_array_size(v___x_1353_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1345_, v_env_1346_, v___x_1353_, v_sz_1355_, v___x_1356_, v___x_1354_);
lean_dec_ref(v___x_1353_);
v_snd_1358_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_snd_1358_);
v_fst_1359_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_fst_1359_);
lean_dec_ref(v___x_1357_);
v_fst_1360_ = lean_ctor_get(v_snd_1358_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v_snd_1358_, 1);
lean_inc(v_snd_1361_);
lean_dec(v_snd_1358_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 2, v_snd_1361_);
lean_ctor_set(v___x_1350_, 1, v_fst_1360_);
lean_ctor_set(v___x_1350_, 0, v_fst_1359_);
v___x_1363_ = v___x_1350_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_fst_1359_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_fst_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_snd_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_00_u03c3_1370_, lean_object* v_descr_1371_, lean_object* v_env_1372_, lean_object* v_s_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1371_, v_env_1372_, v_s_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1375_, lean_object* v_00_u03b2_1376_, lean_object* v_00_u03c3_1377_, lean_object* v_descr_1378_, lean_object* v_env_1379_, lean_object* v_as_1380_, size_t v_sz_1381_, size_t v_i_1382_, lean_object* v_b_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1378_, v_env_1379_, v_as_1380_, v_sz_1381_, v_i_1382_, v_b_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_00_u03c3_1387_, lean_object* v_descr_1388_, lean_object* v_env_1389_, lean_object* v_as_1390_, lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_b_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1385_, v_00_u03b2_1386_, v_00_u03c3_1387_, v_descr_1388_, v_env_1389_, v_as_1390_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1393_);
lean_dec_ref(v_as_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1402_, v___y_1403_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_x_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1406_, lean_object* v_x_1407_){
_start:
{
lean_inc_ref(v_s_1406_);
return v_s_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1408_, v_x_1409_);
lean_dec_ref(v_x_1409_);
lean_dec_ref(v_s_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1416_, v_x_1417_);
lean_dec_ref(v_x_1417_);
lean_dec_ref(v_x_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_box(0);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1421_);
lean_dec_ref(v_x_1421_);
return v_res_1422_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___f_1428_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1429_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1430_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1431_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1434_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___f_1431_);
lean_ctor_set(v___x_1434_, 3, v___f_1430_);
lean_ctor_set(v___x_1434_, 4, v___f_1429_);
lean_ctor_set(v___x_1434_, 5, v___f_1428_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1435_){
_start:
{
lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___f_1436_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1437_, 0, v_inst_1435_);
v___f_1438_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1439_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1442_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1443_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v___f_1436_);
lean_ctor_set(v___x_1443_, 3, v___f_1437_);
lean_ctor_set(v___x_1443_, 4, v___f_1438_);
lean_ctor_set(v___x_1443_, 5, v___x_1442_);
lean_ctor_set(v___x_1443_, 6, v___f_1439_);
v___x_1444_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1446_, lean_object* v_00_u03b2_1447_, lean_object* v_00_u03c3_1448_, lean_object* v_inst_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1453_, lean_object* v_inst_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1462_ = lean_st_mk_ref(v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1469_){
_start:
{
lean_object* v_newEntries_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_newEntries_1470_ = lean_ctor_get(v_s_1469_, 2);
v___x_1471_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1472_ = l_List_lengthTR___redArg(v_newEntries_1470_);
v___x_1473_ = l_Nat_reprFast(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1476_);
lean_dec_ref(v_s_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1480_);
lean_dec_ref(v_x_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1484_){
_start:
{
lean_object* v_name_1486_; lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_name_1486_ = lean_ctor_get(v_descr_1484_, 0);
v___f_1487_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1488_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1484_, 4);
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1489_, 0, lean_box(0));
lean_closure_set(v___x_1489_, 1, lean_box(0));
lean_closure_set(v___x_1489_, 2, lean_box(0));
lean_closure_set(v___x_1489_, 3, v_descr_1484_);
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, lean_box(0));
lean_closure_set(v___x_1490_, 2, lean_box(0));
lean_closure_set(v___x_1490_, 3, v_descr_1484_);
v___x_1491_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1491_, 0, lean_box(0));
lean_closure_set(v___x_1491_, 1, lean_box(0));
lean_closure_set(v___x_1491_, 2, lean_box(0));
lean_closure_set(v___x_1491_, 3, v_descr_1484_);
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, lean_box(0));
lean_closure_set(v___x_1492_, 3, v_descr_1484_);
v___x_1493_ = lean_box(2);
v___x_1494_ = lean_box(0);
lean_inc(v_name_1486_);
v___x_1495_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1495_, 0, v_name_1486_);
lean_ctor_set(v___x_1495_, 1, v___x_1489_);
lean_ctor_set(v___x_1495_, 2, v___x_1490_);
lean_ctor_set(v___x_1495_, 3, v___x_1491_);
lean_ctor_set(v___x_1495_, 4, v___x_1492_);
lean_ctor_set(v___x_1495_, 5, v___f_1487_);
lean_ctor_set(v___x_1495_, 6, v___x_1493_);
lean_ctor_set(v___x_1495_, 7, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___f_1488_);
v___x_1497_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1510_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1510_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1510_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1502_ = l_Lean_scopedEnvExtensionsRef;
v___x_1503_ = lean_st_ref_take(v___x_1502_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_descr_1484_);
lean_ctor_set(v___x_1504_, 1, v_a_1498_);
lean_inc_ref(v___x_1504_);
v___x_1505_ = lean_array_push(v___x_1503_, v___x_1504_);
v___x_1506_ = lean_st_ref_put(v___x_1502_, v___x_1505_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1504_);
v___x_1508_ = v___x_1500_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1504_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_descr_1484_);
v_a_1511_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1497_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1497_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1522_, lean_object* v_00_u03b2_1523_, lean_object* v_00_u03c3_1524_, lean_object* v_descr_1525_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_00_u03c3_1530_, lean_object* v_descr_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1528_, v_00_u03b2_1529_, v_00_u03c3_1530_, v_descr_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1534_){
_start:
{
lean_object* v_stateStack_1535_; 
v_stateStack_1535_ = lean_ctor_get(v_s_1534_, 0);
if (lean_obj_tag(v_stateStack_1535_) == 0)
{
return v_s_1534_;
}
else
{
lean_object* v_head_1536_; lean_object* v_scopedEntries_1537_; lean_object* v_newEntries_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1556_; 
lean_inc_ref(v_stateStack_1535_);
v_head_1536_ = lean_ctor_get(v_stateStack_1535_, 0);
lean_inc(v_head_1536_);
v_scopedEntries_1537_ = lean_ctor_get(v_s_1534_, 1);
v_newEntries_1538_ = lean_ctor_get(v_s_1534_, 2);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_s_1534_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_s_1534_, 0);
lean_dec(v_unused_1557_);
v___x_1540_ = v_s_1534_;
v_isShared_1541_ = v_isSharedCheck_1556_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_newEntries_1538_);
lean_inc(v_scopedEntries_1537_);
lean_dec(v_s_1534_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1556_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_state_1542_; lean_object* v_activeScopes_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1555_; 
v_state_1542_ = lean_ctor_get(v_head_1536_, 0);
v_activeScopes_1543_ = lean_ctor_get(v_head_1536_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_head_1536_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1545_ = v_head_1536_;
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_activeScopes_1543_);
lean_inc(v_state_1542_);
lean_dec(v_head_1536_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = 1;
if (v_isShared_1546_ == 0)
{
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_state_1542_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_activeScopes_1543_);
v___x_1549_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*2, v___x_1547_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_stateStack_1535_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1550_);
v___x_1552_ = v___x_1540_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_scopedEntries_1537_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_newEntries_1538_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1559_, lean_object* v_env_1560_){
_start:
{
lean_object* v_ext_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_ext_1561_ = lean_ctor_get(v_ext_1559_, 1);
lean_inc_ref(v_ext_1561_);
lean_dec_ref(v_ext_1559_);
v___f_1562_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1563_ = lean_box(1);
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1561_, v_env_1560_, v___f_1562_, v___x_1563_, v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_00_u03c3_1568_, lean_object* v_ext_1569_, lean_object* v_env_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1569_, v_env_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1572_){
_start:
{
lean_object* v_stateStack_1573_; 
v_stateStack_1573_ = lean_ctor_get(v_s_1572_, 0);
if (lean_obj_tag(v_stateStack_1573_) == 1)
{
lean_object* v_tail_1574_; 
v_tail_1574_ = lean_ctor_get(v_stateStack_1573_, 1);
if (lean_obj_tag(v_tail_1574_) == 1)
{
lean_object* v_scopedEntries_1575_; lean_object* v_newEntries_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_inc_ref(v_tail_1574_);
v_scopedEntries_1575_ = lean_ctor_get(v_s_1572_, 1);
v_newEntries_1576_ = lean_ctor_get(v_s_1572_, 2);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_s_1572_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_s_1572_, 0);
lean_dec(v_unused_1584_);
v___x_1578_ = v_s_1572_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_newEntries_1576_);
lean_inc(v_scopedEntries_1575_);
lean_dec(v_s_1572_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_tail_1574_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_tail_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_scopedEntries_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_newEntries_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
return v_s_1572_;
}
}
else
{
return v_s_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1586_, lean_object* v_env_1587_){
_start:
{
lean_object* v_ext_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_ext_1588_ = lean_ctor_get(v_ext_1586_, 1);
lean_inc_ref(v_ext_1588_);
lean_dec_ref(v_ext_1586_);
v___f_1589_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1590_ = lean_box(1);
v___x_1591_ = lean_box(0);
v___x_1592_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1588_, v_env_1587_, v___f_1589_, v___x_1590_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_00_u03c3_1595_, lean_object* v_ext_1596_, lean_object* v_env_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1596_, v_env_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_zero_1601_; uint8_t v_isZero_1602_; 
v_zero_1601_ = lean_unsigned_to_nat(0u);
v_isZero_1602_ = lean_nat_dec_eq(v_a_1599_, v_zero_1601_);
if (v_isZero_1602_ == 1)
{
return v_a_1600_;
}
else
{
if (lean_obj_tag(v_a_1600_) == 0)
{
return v_a_1600_;
}
else
{
lean_object* v_head_1603_; lean_object* v_tail_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1623_; 
v_head_1603_ = lean_ctor_get(v_a_1600_, 0);
v_tail_1604_ = lean_ctor_get(v_a_1600_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_a_1600_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1606_ = v_a_1600_;
v_isShared_1607_ = v_isSharedCheck_1623_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_tail_1604_);
lean_inc(v_head_1603_);
lean_dec(v_a_1600_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1623_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_state_1608_; lean_object* v_activeScopes_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1622_; 
v_state_1608_ = lean_ctor_get(v_head_1603_, 0);
v_activeScopes_1609_ = lean_ctor_get(v_head_1603_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_head_1603_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1611_ = v_head_1603_;
v_isShared_1612_ = v_isSharedCheck_1622_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_activeScopes_1609_);
lean_inc(v_state_1608_);
lean_dec(v_head_1603_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1622_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_one_1613_; lean_object* v_n_1614_; lean_object* v___x_1616_; 
v_one_1613_ = lean_unsigned_to_nat(1u);
v_n_1614_ = lean_nat_sub(v_a_1599_, v_one_1613_);
if (v_isShared_1612_ == 0)
{
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_state_1608_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_activeScopes_1609_);
v___x_1616_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*2, v_isZero_1602_);
v___x_1617_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1614_, v_tail_1604_);
lean_dec(v_n_1614_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v___x_1617_);
lean_ctor_set(v___x_1606_, 0, v___x_1616_);
v___x_1619_ = v___x_1606_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1624_, v_a_1625_);
lean_dec(v_a_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1628_, v_a_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1635_, lean_object* v_s_1636_){
_start:
{
lean_object* v_stateStack_1637_; lean_object* v_scopedEntries_1638_; lean_object* v_newEntries_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
v_stateStack_1637_ = lean_ctor_get(v_s_1636_, 0);
v_scopedEntries_1638_ = lean_ctor_get(v_s_1636_, 1);
v_newEntries_1639_ = lean_ctor_get(v_s_1636_, 2);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_s_1636_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v_s_1636_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_newEntries_1639_);
lean_inc(v_scopedEntries_1638_);
lean_inc(v_stateStack_1637_);
lean_dec(v_s_1636_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1635_, v_stateStack_1637_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_scopedEntries_1638_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_newEntries_1639_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1648_, lean_object* v_s_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1648_, v_s_1649_);
lean_dec(v_depth_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1651_, lean_object* v_env_1652_, lean_object* v_depth_1653_){
_start:
{
lean_object* v_ext_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_ext_1654_ = lean_ctor_get(v_ext_1651_, 1);
lean_inc_ref(v_ext_1654_);
lean_dec_ref(v_ext_1651_);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1655_, 0, v_depth_1653_);
v___x_1656_ = lean_box(1);
v___x_1657_ = lean_box(0);
v___x_1658_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1654_, v_env_1652_, v___f_1655_, v___x_1656_, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_00_u03c3_1661_, lean_object* v_ext_1662_, lean_object* v_env_1663_, lean_object* v_depth_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1662_, v_env_1663_, v_depth_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1666_, lean_object* v_env_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v_ext_1669_; lean_object* v_toEnvExtension_1670_; lean_object* v_asyncMode_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_ext_1669_ = lean_ctor_get(v_ext_1666_, 1);
lean_inc_ref(v_ext_1669_);
lean_dec_ref(v_ext_1666_);
v_toEnvExtension_1670_ = lean_ctor_get(v_ext_1669_, 0);
v_asyncMode_1671_ = lean_ctor_get(v_toEnvExtension_1670_, 2);
lean_inc(v_asyncMode_1671_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_b_1668_);
v___x_1673_ = lean_box(0);
v___x_1674_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1669_, v_env_1667_, v___x_1672_, v_asyncMode_1671_, v___x_1673_);
lean_dec(v_asyncMode_1671_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1675_, lean_object* v_00_u03b2_1676_, lean_object* v_00_u03c3_1677_, lean_object* v_ext_1678_, lean_object* v_env_1679_, lean_object* v_b_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1678_, v_env_1679_, v_b_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1682_, lean_object* v_env_1683_, lean_object* v_namespaceName_1684_, lean_object* v_b_1685_){
_start:
{
lean_object* v_ext_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1697_; 
v_ext_1686_ = lean_ctor_get(v_ext_1682_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_ext_1682_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_ext_1682_, 0);
lean_dec(v_unused_1698_);
v___x_1688_ = v_ext_1682_;
v_isShared_1689_ = v_isSharedCheck_1697_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_ext_1686_);
lean_dec(v_ext_1682_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1697_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_toEnvExtension_1690_; lean_object* v_asyncMode_1691_; lean_object* v___x_1693_; 
v_toEnvExtension_1690_ = lean_ctor_get(v_ext_1686_, 0);
v_asyncMode_1691_ = lean_ctor_get(v_toEnvExtension_1690_, 2);
lean_inc(v_asyncMode_1691_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
lean_ctor_set(v___x_1688_, 1, v_b_1685_);
lean_ctor_set(v___x_1688_, 0, v_namespaceName_1684_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_namespaceName_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_b_1685_);
v___x_1693_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1686_, v_env_1683_, v___x_1693_, v_asyncMode_1691_, v___x_1694_);
lean_dec(v_asyncMode_1691_);
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_00_u03c3_1701_, lean_object* v_ext_1702_, lean_object* v_env_1703_, lean_object* v_namespaceName_1704_, lean_object* v_b_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1702_, v_env_1703_, v_namespaceName_1704_, v_b_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1707_, lean_object* v_states_1708_, lean_object* v_b_1709_){
_start:
{
if (lean_obj_tag(v_states_1708_) == 0)
{
lean_dec(v_b_1709_);
lean_dec_ref(v_ext_1707_);
return v_states_1708_;
}
else
{
lean_object* v_descr_1710_; lean_object* v_head_1711_; lean_object* v_tail_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1735_; 
v_descr_1710_ = lean_ctor_get(v_ext_1707_, 0);
v_head_1711_ = lean_ctor_get(v_states_1708_, 0);
v_tail_1712_ = lean_ctor_get(v_states_1708_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_states_1708_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1714_ = v_states_1708_;
v_isShared_1715_ = v_isSharedCheck_1735_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_tail_1712_);
lean_inc(v_head_1711_);
lean_dec(v_states_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1735_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_addEntry_1716_; lean_object* v_state_1717_; lean_object* v_activeScopes_1718_; uint8_t v_delimitsLocal_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1734_; 
v_addEntry_1716_ = lean_ctor_get(v_descr_1710_, 4);
v_state_1717_ = lean_ctor_get(v_head_1711_, 0);
v_activeScopes_1718_ = lean_ctor_get(v_head_1711_, 1);
v_delimitsLocal_1719_ = lean_ctor_get_uint8(v_head_1711_, sizeof(void*)*2);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_head_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1721_ = v_head_1711_;
v_isShared_1722_ = v_isSharedCheck_1734_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_activeScopes_1718_);
lean_inc(v_state_1717_);
lean_dec(v_head_1711_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1734_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v_top_1725_; 
lean_inc(v_addEntry_1716_);
lean_inc(v_b_1709_);
v___x_1723_ = lean_apply_2(v_addEntry_1716_, v_state_1717_, v_b_1709_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1723_);
v_top_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_activeScopes_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*2, v_delimitsLocal_1719_);
v_top_1725_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
if (v_delimitsLocal_1719_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_stateStackModify___redArg(v_ext_1707_, v_tail_1712_, v_b_1709_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1726_);
lean_ctor_set(v___x_1714_, 0, v_top_1725_);
v___x_1728_ = v___x_1714_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_top_1725_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_b_1709_);
lean_dec_ref(v_ext_1707_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v_top_1725_);
v___x_1731_ = v___x_1714_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_top_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_tail_1712_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_00_u03c3_1738_, lean_object* v_ext_1739_, lean_object* v_states_1740_, lean_object* v_b_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_stateStackModify___redArg(v_ext_1739_, v_states_1740_, v_b_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1743_, lean_object* v_b_1744_, lean_object* v_s_1745_){
_start:
{
lean_object* v_stateStack_1746_; lean_object* v_scopedEntries_1747_; lean_object* v_newEntries_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1756_; 
v_stateStack_1746_ = lean_ctor_get(v_s_1745_, 0);
v_scopedEntries_1747_ = lean_ctor_get(v_s_1745_, 1);
v_newEntries_1748_ = lean_ctor_get(v_s_1745_, 2);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_s_1745_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1750_ = v_s_1745_;
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_newEntries_1748_);
lean_inc(v_scopedEntries_1747_);
lean_inc(v_stateStack_1746_);
lean_dec(v_s_1745_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1752_ = l_Lean_stateStackModify___redArg(v_ext_1743_, v_stateStack_1746_, v_b_1744_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1752_);
v___x_1754_ = v___x_1750_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_scopedEntries_1747_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_newEntries_1748_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1757_, lean_object* v_env_1758_, lean_object* v_b_1759_){
_start:
{
lean_object* v_ext_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_ext_1760_ = lean_ctor_get(v_ext_1757_, 1);
lean_inc_ref(v_ext_1760_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1761_, 0, v_ext_1757_);
lean_closure_set(v___f_1761_, 1, v_b_1759_);
v___x_1762_ = lean_box(1);
v___x_1763_ = lean_box(0);
v___x_1764_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1760_, v_env_1758_, v___f_1761_, v___x_1762_, v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_00_u03c3_1767_, lean_object* v_ext_1768_, lean_object* v_env_1769_, lean_object* v_b_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1768_, v_env_1769_, v_b_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1772_, lean_object* v_ext_1773_, lean_object* v_b_1774_, uint8_t v_kind_1775_, lean_object* v_namespaceName_1776_){
_start:
{
switch(v_kind_1775_)
{
case 0:
{
lean_object* v___x_1777_; 
lean_dec(v_namespaceName_1776_);
v___x_1777_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1773_, v_env_1772_, v_b_1774_);
return v___x_1777_;
}
case 1:
{
lean_object* v___x_1778_; 
lean_dec(v_namespaceName_1776_);
v___x_1778_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1773_, v_env_1772_, v_b_1774_);
return v___x_1778_;
}
default: 
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1773_, v_env_1772_, v_namespaceName_1776_, v_b_1774_);
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1780_, lean_object* v_ext_1781_, lean_object* v_b_1782_, lean_object* v_kind_1783_, lean_object* v_namespaceName_1784_){
_start:
{
uint8_t v_kind_boxed_1785_; lean_object* v_res_1786_; 
v_kind_boxed_1785_ = lean_unbox(v_kind_1783_);
v_res_1786_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1780_, v_ext_1781_, v_b_1782_, v_kind_boxed_1785_, v_namespaceName_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_00_u03c3_1789_, lean_object* v_env_1790_, lean_object* v_ext_1791_, lean_object* v_b_1792_, uint8_t v_kind_1793_, lean_object* v_namespaceName_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1790_, v_ext_1791_, v_b_1792_, v_kind_1793_, v_namespaceName_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_00_u03c3_1798_, lean_object* v_env_1799_, lean_object* v_ext_1800_, lean_object* v_b_1801_, lean_object* v_kind_1802_, lean_object* v_namespaceName_1803_){
_start:
{
uint8_t v_kind_boxed_1804_; lean_object* v_res_1805_; 
v_kind_boxed_1804_ = lean_unbox(v_kind_1802_);
v_res_1805_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1796_, v_00_u03b2_1797_, v_00_u03c3_1798_, v_env_1799_, v_ext_1800_, v_b_1801_, v_kind_boxed_1804_, v_namespaceName_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1806_, lean_object* v_b_1807_, uint8_t v_kind_1808_, lean_object* v_ns_1809_, lean_object* v_x_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1810_, v_ext_1806_, v_b_1807_, v_kind_1808_, v_ns_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1812_, lean_object* v_b_1813_, lean_object* v_kind_1814_, lean_object* v_ns_1815_, lean_object* v_x_1816_){
_start:
{
uint8_t v_kind_boxed_1817_; lean_object* v_res_1818_; 
v_kind_boxed_1817_ = lean_unbox(v_kind_1814_);
v_res_1818_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1812_, v_b_1813_, v_kind_boxed_1817_, v_ns_1815_, v_x_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1819_, lean_object* v_ext_1820_, lean_object* v_b_1821_, uint8_t v_kind_1822_, lean_object* v_ns_1823_){
_start:
{
lean_object* v_modifyEnv_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; 
v_modifyEnv_1824_ = lean_ctor_get(v_inst_1819_, 1);
lean_inc(v_modifyEnv_1824_);
lean_dec_ref(v_inst_1819_);
v___x_1825_ = lean_box(v_kind_1822_);
v___f_1826_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1826_, 0, v_ext_1820_);
lean_closure_set(v___f_1826_, 1, v_b_1821_);
lean_closure_set(v___f_1826_, 2, v___x_1825_);
lean_closure_set(v___f_1826_, 3, v_ns_1823_);
v___x_1827_ = lean_apply_1(v_modifyEnv_1824_, v___f_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1828_, lean_object* v_ext_1829_, lean_object* v_b_1830_, lean_object* v_kind_1831_, lean_object* v_ns_1832_){
_start:
{
uint8_t v_kind_boxed_1833_; lean_object* v_res_1834_; 
v_kind_boxed_1833_ = lean_unbox(v_kind_1831_);
v_res_1834_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1828_, v_ext_1829_, v_b_1830_, v_kind_boxed_1833_, v_ns_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_ext_1838_, lean_object* v_b_1839_, uint8_t v_kind_1840_){
_start:
{
lean_object* v_toBind_1841_; lean_object* v_getCurrNamespace_1842_; lean_object* v___x_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; 
v_toBind_1841_ = lean_ctor_get(v_inst_1835_, 1);
lean_inc(v_toBind_1841_);
lean_dec_ref(v_inst_1835_);
v_getCurrNamespace_1842_ = lean_ctor_get(v_inst_1836_, 0);
lean_inc(v_getCurrNamespace_1842_);
lean_dec_ref(v_inst_1836_);
v___x_1843_ = lean_box(v_kind_1840_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1844_, 0, v_inst_1837_);
lean_closure_set(v___f_1844_, 1, v_ext_1838_);
lean_closure_set(v___f_1844_, 2, v_b_1839_);
lean_closure_set(v___f_1844_, 3, v___x_1843_);
v___x_1845_ = lean_apply_4(v_toBind_1841_, lean_box(0), lean_box(0), v_getCurrNamespace_1842_, v___f_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_ext_1849_, lean_object* v_b_1850_, lean_object* v_kind_1851_){
_start:
{
uint8_t v_kind_boxed_1852_; lean_object* v_res_1853_; 
v_kind_boxed_1852_ = lean_unbox(v_kind_1851_);
v_res_1853_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1846_, v_inst_1847_, v_inst_1848_, v_ext_1849_, v_b_1850_, v_kind_boxed_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1854_, lean_object* v_00_u03b1_1855_, lean_object* v_00_u03b2_1856_, lean_object* v_00_u03c3_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_ext_1861_, lean_object* v_b_1862_, uint8_t v_kind_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1858_, v_inst_1859_, v_inst_1860_, v_ext_1861_, v_b_1862_, v_kind_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1865_, lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_00_u03c3_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_ext_1872_, lean_object* v_b_1873_, lean_object* v_kind_1874_){
_start:
{
uint8_t v_kind_boxed_1875_; lean_object* v_res_1876_; 
v_kind_boxed_1875_ = lean_unbox(v_kind_1874_);
v_res_1876_ = l_Lean_ScopedEnvExtension_add(v_m_1865_, v_00_u03b1_1866_, v_00_u03b2_1867_, v_00_u03c3_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_ext_1872_, v_b_1873_, v_kind_boxed_1875_);
return v_res_1876_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1880_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1881_ = lean_unsigned_to_nat(16u);
v___x_1882_ = lean_unsigned_to_nat(209u);
v___x_1883_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1884_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1885_ = l_mkPanicMessageWithDecl(v___x_1884_, v___x_1883_, v___x_1882_, v___x_1881_, v___x_1880_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1886_, lean_object* v_ext_1887_, lean_object* v_env_1888_, lean_object* v_asyncMode_1889_){
_start:
{
lean_object* v_ext_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_stateStack_1894_; 
v_ext_1890_ = lean_ctor_get(v_ext_1887_, 1);
v___x_1891_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1891_, v_ext_1890_, v_env_1888_, v_asyncMode_1889_, v___x_1892_);
v_stateStack_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_stateStack_1894_);
lean_dec(v___x_1893_);
if (lean_obj_tag(v_stateStack_1894_) == 1)
{
lean_object* v_head_1895_; lean_object* v_state_1896_; 
v_head_1895_ = lean_ctor_get(v_stateStack_1894_, 0);
lean_inc(v_head_1895_);
lean_dec_ref_known(v_stateStack_1894_, 2);
v_state_1896_ = lean_ctor_get(v_head_1895_, 0);
lean_inc(v_state_1896_);
lean_dec(v_head_1895_);
return v_state_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_stateStack_1894_);
v___x_1897_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1898_ = l_panic___redArg(v_inst_1886_, v___x_1897_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1899_, lean_object* v_ext_1900_, lean_object* v_env_1901_, lean_object* v_asyncMode_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1899_, v_ext_1900_, v_env_1901_, v_asyncMode_1902_);
lean_dec(v_asyncMode_1902_);
lean_dec_ref(v_ext_1900_);
lean_dec(v_inst_1899_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1904_, lean_object* v_00_u03b1_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_inst_1907_, lean_object* v_ext_1908_, lean_object* v_env_1909_, lean_object* v_asyncMode_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1907_, v_ext_1908_, v_env_1909_, v_asyncMode_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_inst_1915_, lean_object* v_ext_1916_, lean_object* v_env_1917_, lean_object* v_asyncMode_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1912_, v_00_u03b1_1913_, v_00_u03b2_1914_, v_inst_1915_, v_ext_1916_, v_env_1917_, v_asyncMode_1918_);
lean_dec(v_asyncMode_1918_);
lean_dec_ref(v_ext_1916_);
lean_dec(v_inst_1915_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1920_, lean_object* v_as_1921_, size_t v_sz_1922_, size_t v_i_1923_, lean_object* v_b_1924_){
_start:
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_usize_dec_lt(v_i_1923_, v_sz_1922_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_ext_1920_);
return v_b_1924_;
}
else
{
lean_object* v_descr_1926_; lean_object* v_snd_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1941_; 
v_descr_1926_ = lean_ctor_get(v_ext_1920_, 0);
v_snd_1927_ = lean_ctor_get(v_b_1924_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_b_1924_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_b_1924_, 0);
lean_dec(v_unused_1942_);
v___x_1929_ = v_b_1924_;
v_isShared_1930_ = v_isSharedCheck_1941_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snd_1927_);
lean_dec(v_b_1924_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1941_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_addEntry_1931_; lean_object* v___x_1932_; lean_object* v_a_1933_; lean_object* v_state_1934_; lean_object* v___x_1936_; 
v_addEntry_1931_ = lean_ctor_get(v_descr_1926_, 4);
v___x_1932_ = lean_box(0);
v_a_1933_ = lean_array_uget_borrowed(v_as_1921_, v_i_1923_);
lean_inc(v_addEntry_1931_);
lean_inc(v_a_1933_);
v_state_1934_ = lean_apply_2(v_addEntry_1931_, v_snd_1927_, v_a_1933_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v_state_1934_);
lean_ctor_set(v___x_1929_, 0, v___x_1932_);
v___x_1936_ = v___x_1929_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_state_1934_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
size_t v___x_1937_; size_t v___x_1938_; 
v___x_1937_ = ((size_t)1ULL);
v___x_1938_ = lean_usize_add(v_i_1923_, v___x_1937_);
v_i_1923_ = v___x_1938_;
v_b_1924_ = v___x_1936_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1943_, lean_object* v_as_1944_, lean_object* v_sz_1945_, lean_object* v_i_1946_, lean_object* v_b_1947_){
_start:
{
size_t v_sz_boxed_1948_; size_t v_i_boxed_1949_; lean_object* v_res_1950_; 
v_sz_boxed_1948_ = lean_unbox_usize(v_sz_1945_);
lean_dec(v_sz_1945_);
v_i_boxed_1949_ = lean_unbox_usize(v_i_1946_);
lean_dec(v_i_1946_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1943_, v_as_1944_, v_sz_boxed_1948_, v_i_boxed_1949_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1951_, lean_object* v_as_1952_, size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_b_1955_){
_start:
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1956_ == 0)
{
lean_dec_ref(v_ext_1951_);
return v_b_1955_;
}
else
{
lean_object* v_descr_1957_; lean_object* v_snd_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1972_; 
v_descr_1957_ = lean_ctor_get(v_ext_1951_, 0);
v_snd_1958_ = lean_ctor_get(v_b_1955_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_b_1955_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_b_1955_, 0);
lean_dec(v_unused_1973_);
v___x_1960_ = v_b_1955_;
v_isShared_1961_ = v_isSharedCheck_1972_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snd_1958_);
lean_dec(v_b_1955_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1972_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_addEntry_1962_; lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v_state_1965_; lean_object* v___x_1967_; 
v_addEntry_1962_ = lean_ctor_get(v_descr_1957_, 4);
v___x_1963_ = lean_box(0);
v_a_1964_ = lean_array_uget_borrowed(v_as_1952_, v_i_1954_);
lean_inc(v_addEntry_1962_);
lean_inc(v_a_1964_);
v_state_1965_ = lean_apply_2(v_addEntry_1962_, v_snd_1958_, v_a_1964_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_state_1965_);
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1967_ = v___x_1960_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_state_1965_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1954_, v___x_1968_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1951_, v_as_1952_, v_sz_1953_, v___x_1969_, v___x_1967_);
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1974_, lean_object* v_as_1975_, lean_object* v_sz_1976_, lean_object* v_i_1977_, lean_object* v_b_1978_){
_start:
{
size_t v_sz_boxed_1979_; size_t v_i_boxed_1980_; lean_object* v_res_1981_; 
v_sz_boxed_1979_ = lean_unbox_usize(v_sz_1976_);
lean_dec(v_sz_1976_);
v_i_boxed_1980_ = lean_unbox_usize(v_i_1977_);
lean_dec(v_i_1977_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1974_, v_as_1975_, v_sz_boxed_1979_, v_i_boxed_1980_, v_b_1978_);
lean_dec_ref(v_as_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1982_, lean_object* v_ext_1983_, lean_object* v_n_1984_, lean_object* v_b_1985_){
_start:
{
if (lean_obj_tag(v_n_1984_) == 0)
{
lean_object* v_cs_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; size_t v_sz_1989_; size_t v___x_1990_; lean_object* v___x_1991_; lean_object* v_fst_1992_; 
v_cs_1986_ = lean_ctor_get(v_n_1984_, 0);
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v_b_1985_);
v_sz_1989_ = lean_array_size(v_cs_1986_);
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1982_, v_ext_1983_, v_cs_1986_, v_sz_1989_, v___x_1990_, v___x_1988_);
v_fst_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_fst_1992_);
if (lean_obj_tag(v_fst_1992_) == 0)
{
lean_object* v_snd_1993_; lean_object* v___x_1994_; 
v_snd_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_snd_1993_);
lean_dec_ref(v___x_1991_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_snd_1993_);
return v___x_1994_;
}
else
{
lean_object* v_val_1995_; 
lean_dec_ref(v___x_1991_);
v_val_1995_ = lean_ctor_get(v_fst_1992_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v_fst_1992_, 1);
return v_val_1995_;
}
}
else
{
lean_object* v_vs_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; size_t v_sz_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v_fst_2002_; 
v_vs_1996_ = lean_ctor_get(v_n_1984_, 0);
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v_b_1985_);
v_sz_1999_ = lean_array_size(v_vs_1996_);
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1983_, v_vs_1996_, v_sz_1999_, v___x_2000_, v___x_1998_);
v_fst_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_fst_2002_);
if (lean_obj_tag(v_fst_2002_) == 0)
{
lean_object* v_snd_2003_; lean_object* v___x_2004_; 
v_snd_2003_ = lean_ctor_get(v___x_2001_, 1);
lean_inc(v_snd_2003_);
lean_dec_ref(v___x_2001_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_snd_2003_);
return v___x_2004_;
}
else
{
lean_object* v_val_2005_; 
lean_dec_ref(v___x_2001_);
v_val_2005_ = lean_ctor_get(v_fst_2002_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v_fst_2002_, 1);
return v_val_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2006_, lean_object* v_ext_2007_, lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2012_ == 0)
{
lean_dec_ref(v_ext_2007_);
return v_b_2011_;
}
else
{
lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2031_; 
v_snd_2013_ = lean_ctor_get(v_b_2011_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_b_2011_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v_b_2011_, 0);
lean_dec(v_unused_2032_);
v___x_2015_ = v_b_2011_;
v_isShared_2016_ = v_isSharedCheck_2031_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_dec(v_b_2011_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2031_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_array_uget_borrowed(v_as_2008_, v_i_2010_);
lean_inc(v_snd_2013_);
lean_inc_ref(v_ext_2007_);
v___x_2018_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2006_, v_ext_2007_, v_a_2017_, v_snd_2013_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec_ref(v_ext_2007_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2013_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v_snd_2013_);
v_a_2023_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2024_ = lean_box(0);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_a_2023_);
lean_ctor_set(v___x_2015_, 0, v___x_2024_);
v___x_2026_ = v___x_2015_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_a_2023_);
v___x_2026_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
size_t v___x_2027_; size_t v___x_2028_; 
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2010_, v___x_2027_);
v_i_2010_ = v___x_2028_;
v_b_2011_ = v___x_2026_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2033_, lean_object* v_ext_2034_, lean_object* v_as_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_sz_boxed_2039_; size_t v_i_boxed_2040_; lean_object* v_res_2041_; 
v_sz_boxed_2039_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2040_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2033_, v_ext_2034_, v_as_2035_, v_sz_boxed_2039_, v_i_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
lean_dec(v_init_2033_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2042_, lean_object* v_ext_2043_, lean_object* v_n_2044_, lean_object* v_b_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2042_, v_ext_2043_, v_n_2044_, v_b_2045_);
lean_dec_ref(v_n_2044_);
lean_dec(v_init_2042_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2047_, lean_object* v_as_2048_, size_t v_sz_2049_, size_t v_i_2050_, lean_object* v_b_2051_){
_start:
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_lt(v_i_2050_, v_sz_2049_);
if (v___x_2052_ == 0)
{
lean_dec_ref(v_ext_2047_);
return v_b_2051_;
}
else
{
lean_object* v_descr_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2068_; 
v_descr_2053_ = lean_ctor_get(v_ext_2047_, 0);
v_snd_2054_ = lean_ctor_get(v_b_2051_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_b_2051_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_b_2051_, 0);
lean_dec(v_unused_2069_);
v___x_2056_ = v_b_2051_;
v_isShared_2057_ = v_isSharedCheck_2068_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_dec(v_b_2051_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2068_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_addEntry_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v_state_2061_; lean_object* v___x_2063_; 
v_addEntry_2058_ = lean_ctor_get(v_descr_2053_, 4);
v___x_2059_ = lean_box(0);
v_a_2060_ = lean_array_uget_borrowed(v_as_2048_, v_i_2050_);
lean_inc(v_addEntry_2058_);
lean_inc(v_a_2060_);
v_state_2061_ = lean_apply_2(v_addEntry_2058_, v_snd_2054_, v_a_2060_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v_state_2061_);
lean_ctor_set(v___x_2056_, 0, v___x_2059_);
v___x_2063_ = v___x_2056_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_state_2061_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
size_t v___x_2064_; size_t v___x_2065_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_i_2050_, v___x_2064_);
v_i_2050_ = v___x_2065_;
v_b_2051_ = v___x_2063_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2070_, lean_object* v_as_2071_, lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_b_2074_){
_start:
{
size_t v_sz_boxed_2075_; size_t v_i_boxed_2076_; lean_object* v_res_2077_; 
v_sz_boxed_2075_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2076_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2070_, v_as_2071_, v_sz_boxed_2075_, v_i_boxed_2076_, v_b_2074_);
lean_dec_ref(v_as_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2078_, lean_object* v_as_2079_, size_t v_sz_2080_, size_t v_i_2081_, lean_object* v_b_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_lt(v_i_2081_, v_sz_2080_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v_ext_2078_);
return v_b_2082_;
}
else
{
lean_object* v_descr_2084_; lean_object* v_snd_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2099_; 
v_descr_2084_ = lean_ctor_get(v_ext_2078_, 0);
v_snd_2085_ = lean_ctor_get(v_b_2082_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_b_2082_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_b_2082_, 0);
lean_dec(v_unused_2100_);
v___x_2087_ = v_b_2082_;
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_snd_2085_);
lean_dec(v_b_2082_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_addEntry_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v_state_2092_; lean_object* v___x_2094_; 
v_addEntry_2089_ = lean_ctor_get(v_descr_2084_, 4);
v___x_2090_ = lean_box(0);
v_a_2091_ = lean_array_uget_borrowed(v_as_2079_, v_i_2081_);
lean_inc(v_addEntry_2089_);
lean_inc(v_a_2091_);
v_state_2092_ = lean_apply_2(v_addEntry_2089_, v_snd_2085_, v_a_2091_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v_state_2092_);
lean_ctor_set(v___x_2087_, 0, v___x_2090_);
v___x_2094_ = v___x_2087_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_state_2092_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2081_, v___x_2095_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2078_, v_as_2079_, v_sz_2080_, v___x_2096_, v___x_2094_);
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2101_, lean_object* v_as_2102_, lean_object* v_sz_2103_, lean_object* v_i_2104_, lean_object* v_b_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2103_);
lean_dec(v_sz_2103_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2101_, v_as_2102_, v_sz_boxed_2106_, v_i_boxed_2107_, v_b_2105_);
lean_dec_ref(v_as_2102_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2109_, lean_object* v_t_2110_, lean_object* v_init_2111_){
_start:
{
lean_object* v_root_2112_; lean_object* v_tail_2113_; lean_object* v___x_2114_; 
v_root_2112_ = lean_ctor_get(v_t_2110_, 0);
v_tail_2113_ = lean_ctor_get(v_t_2110_, 1);
lean_inc_ref(v_ext_2109_);
lean_inc(v_init_2111_);
v___x_2114_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2111_, v_ext_2109_, v_root_2112_, v_init_2111_);
lean_dec(v_init_2111_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
lean_dec_ref(v_ext_2109_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
return v_a_2115_;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v_fst_2122_; 
v_a_2116_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_a_2116_);
v_sz_2119_ = lean_array_size(v_tail_2113_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2109_, v_tail_2113_, v_sz_2119_, v___x_2120_, v___x_2118_);
v_fst_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_fst_2122_);
if (lean_obj_tag(v_fst_2122_) == 0)
{
lean_object* v_snd_2123_; 
v_snd_2123_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_snd_2123_);
lean_dec_ref(v___x_2121_);
return v_snd_2123_;
}
else
{
lean_object* v_val_2124_; 
lean_dec_ref(v___x_2121_);
v_val_2124_ = lean_ctor_get(v_fst_2122_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_fst_2122_, 1);
return v_val_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2125_, lean_object* v_t_2126_, lean_object* v_init_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2125_, v_t_2126_, v_init_2127_);
lean_dec_ref(v_t_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2129_, lean_object* v_ext_2130_, lean_object* v_s_2131_){
_start:
{
lean_object* v_stateStack_2132_; 
v_stateStack_2132_ = lean_ctor_get(v_s_2131_, 0);
lean_inc(v_stateStack_2132_);
if (lean_obj_tag(v_stateStack_2132_) == 1)
{
lean_object* v_scopedEntries_2133_; lean_object* v_newEntries_2134_; lean_object* v_head_2135_; lean_object* v_tail_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2165_; 
v_scopedEntries_2133_ = lean_ctor_get(v_s_2131_, 1);
v_newEntries_2134_ = lean_ctor_get(v_s_2131_, 2);
v_head_2135_ = lean_ctor_get(v_stateStack_2132_, 0);
v_tail_2136_ = lean_ctor_get(v_stateStack_2132_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_stateStack_2132_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2138_ = v_stateStack_2132_;
v_isShared_2139_ = v_isSharedCheck_2165_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_tail_2136_);
lean_inc(v_head_2135_);
lean_dec(v_stateStack_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2165_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___y_2141_; lean_object* v_state_2146_; lean_object* v_activeScopes_2147_; uint8_t v_delimitsLocal_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2164_; 
v_state_2146_ = lean_ctor_get(v_head_2135_, 0);
v_activeScopes_2147_ = lean_ctor_get(v_head_2135_, 1);
v_delimitsLocal_2148_ = lean_ctor_get_uint8(v_head_2135_, sizeof(void*)*2);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_head_2135_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2150_ = v_head_2135_;
v_isShared_2151_ = v_isSharedCheck_2164_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_activeScopes_2147_);
lean_inc(v_state_2146_);
lean_dec(v_head_2135_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2164_;
goto v_resetjp_2149_;
}
v___jp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___y_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___y_2141_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_tail_2136_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v_scopedEntries_2133_);
lean_ctor_set(v___x_2144_, 2, v_newEntries_2134_);
return v___x_2144_;
}
}
v_resetjp_2149_:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_NameSet_contains(v_activeScopes_2147_, v_namespaceName_2129_);
if (v___x_2152_ == 0)
{
lean_object* v_activeScopes_2153_; lean_object* v___x_2154_; 
lean_inc(v_newEntries_2134_);
lean_inc_ref(v_scopedEntries_2133_);
lean_dec_ref(v_s_2131_);
lean_inc(v_namespaceName_2129_);
v_activeScopes_2153_ = l_Lean_NameSet_insert(v_activeScopes_2147_, v_namespaceName_2129_);
v___x_2154_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2133_, v_namespaceName_2129_);
lean_dec(v_namespaceName_2129_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref(v_ext_2130_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_activeScopes_2153_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_state_2146_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_activeScopes_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*2, v_delimitsLocal_2148_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
v___y_2141_ = v___x_2156_;
goto v___jp_2140_;
}
}
else
{
lean_object* v_val_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v_val_2158_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2159_ = 1;
v___x_2160_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2130_, v_val_2158_, v_state_2146_);
lean_dec(v_val_2158_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_activeScopes_2153_);
lean_ctor_set(v___x_2150_, 0, v___x_2160_);
v___x_2162_ = v___x_2150_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_activeScopes_2153_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*2, v___x_2159_);
v___y_2141_ = v___x_2162_;
goto v___jp_2140_;
}
}
}
else
{
lean_del_object(v___x_2150_);
lean_dec(v_activeScopes_2147_);
lean_dec(v_state_2146_);
lean_del_object(v___x_2138_);
lean_dec(v_tail_2136_);
lean_dec_ref(v_ext_2130_);
lean_dec(v_namespaceName_2129_);
return v_s_2131_;
}
}
}
}
else
{
lean_dec(v_stateStack_2132_);
lean_dec_ref(v_ext_2130_);
lean_dec(v_namespaceName_2129_);
return v_s_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2166_, lean_object* v_env_2167_, lean_object* v_namespaceName_2168_){
_start:
{
lean_object* v_ext_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_ext_2169_ = lean_ctor_get(v_ext_2166_, 1);
lean_inc_ref(v_ext_2169_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2170_, 0, v_namespaceName_2168_);
lean_closure_set(v___f_2170_, 1, v_ext_2166_);
v___x_2171_ = lean_box(1);
v___x_2172_ = lean_box(0);
v___x_2173_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2169_, v_env_2167_, v___f_2170_, v___x_2171_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_00_u03c3_2176_, lean_object* v_ext_2177_, lean_object* v_env_2178_, lean_object* v_namespaceName_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2177_, v_env_2178_, v_namespaceName_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2181_, lean_object* v_00_u03c3_2182_, lean_object* v_00_u03b1_2183_, lean_object* v_ext_2184_, lean_object* v_t_2185_, lean_object* v_init_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2184_, v_t_2185_, v_init_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2188_, lean_object* v_00_u03c3_2189_, lean_object* v_00_u03b1_2190_, lean_object* v_ext_2191_, lean_object* v_t_2192_, lean_object* v_init_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2188_, v_00_u03c3_2189_, v_00_u03b1_2190_, v_ext_2191_, v_t_2192_, v_init_2193_);
lean_dec_ref(v_t_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2195_, lean_object* v_00_u03c3_2196_, lean_object* v_init_2197_, lean_object* v_00_u03b1_2198_, lean_object* v_ext_2199_, lean_object* v_n_2200_, lean_object* v_b_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2197_, v_ext_2199_, v_n_2200_, v_b_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2203_, lean_object* v_00_u03c3_2204_, lean_object* v_init_2205_, lean_object* v_00_u03b1_2206_, lean_object* v_ext_2207_, lean_object* v_n_2208_, lean_object* v_b_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2203_, v_00_u03c3_2204_, v_init_2205_, v_00_u03b1_2206_, v_ext_2207_, v_n_2208_, v_b_2209_);
lean_dec_ref(v_n_2208_);
lean_dec(v_init_2205_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2211_, lean_object* v_00_u03c3_2212_, lean_object* v_00_u03b1_2213_, lean_object* v_ext_2214_, lean_object* v_as_2215_, size_t v_sz_2216_, size_t v_i_2217_, lean_object* v_b_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2214_, v_as_2215_, v_sz_2216_, v_i_2217_, v_b_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2220_, lean_object* v_00_u03c3_2221_, lean_object* v_00_u03b1_2222_, lean_object* v_ext_2223_, lean_object* v_as_2224_, lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_b_2227_){
_start:
{
size_t v_sz_boxed_2228_; size_t v_i_boxed_2229_; lean_object* v_res_2230_; 
v_sz_boxed_2228_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2229_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2220_, v_00_u03c3_2221_, v_00_u03b1_2222_, v_ext_2223_, v_as_2224_, v_sz_boxed_2228_, v_i_boxed_2229_, v_b_2227_);
lean_dec_ref(v_as_2224_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2231_, lean_object* v_00_u03c3_2232_, lean_object* v_init_2233_, lean_object* v_00_u03b1_2234_, lean_object* v_ext_2235_, lean_object* v_as_2236_, size_t v_sz_2237_, size_t v_i_2238_, lean_object* v_b_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2233_, v_ext_2235_, v_as_2236_, v_sz_2237_, v_i_2238_, v_b_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_00_u03c3_2242_, lean_object* v_init_2243_, lean_object* v_00_u03b1_2244_, lean_object* v_ext_2245_, lean_object* v_as_2246_, lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_b_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2241_, v_00_u03c3_2242_, v_init_2243_, v_00_u03b1_2244_, v_ext_2245_, v_as_2246_, v_sz_boxed_2250_, v_i_boxed_2251_, v_b_2249_);
lean_dec_ref(v_as_2246_);
lean_dec(v_init_2243_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2253_, lean_object* v_00_u03c3_2254_, lean_object* v_00_u03b1_2255_, lean_object* v_ext_2256_, lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2256_, v_as_2257_, v_sz_2258_, v_i_2259_, v_b_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2262_, lean_object* v_00_u03c3_2263_, lean_object* v_00_u03b1_2264_, lean_object* v_ext_2265_, lean_object* v_as_2266_, lean_object* v_sz_2267_, lean_object* v_i_2268_, lean_object* v_b_2269_){
_start:
{
size_t v_sz_boxed_2270_; size_t v_i_boxed_2271_; lean_object* v_res_2272_; 
v_sz_boxed_2270_ = lean_unbox_usize(v_sz_2267_);
lean_dec(v_sz_2267_);
v_i_boxed_2271_ = lean_unbox_usize(v_i_2268_);
lean_dec(v_i_2268_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2262_, v_00_u03c3_2263_, v_00_u03b1_2264_, v_ext_2265_, v_as_2266_, v_sz_boxed_2270_, v_i_boxed_2271_, v_b_2269_);
lean_dec_ref(v_as_2266_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2273_, lean_object* v_00_u03c3_2274_, lean_object* v_00_u03b1_2275_, lean_object* v_ext_2276_, lean_object* v_as_2277_, size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_b_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2276_, v_as_2277_, v_sz_2278_, v_i_2279_, v_b_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2282_, lean_object* v_00_u03c3_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_ext_2285_, lean_object* v_as_2286_, lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_b_2289_){
_start:
{
size_t v_sz_boxed_2290_; size_t v_i_boxed_2291_; lean_object* v_res_2292_; 
v_sz_boxed_2290_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2291_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2282_, v_00_u03c3_2283_, v_00_u03b1_2284_, v_ext_2285_, v_as_2286_, v_sz_boxed_2290_, v_i_boxed_2291_, v_b_2289_);
lean_dec_ref(v_as_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2293_, lean_object* v_00_u03c3_2294_, lean_object* v_00_u03b1_2295_, lean_object* v_ext_2296_, lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_b_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2296_, v_as_2297_, v_sz_2298_, v_i_2299_, v_b_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2302_, lean_object* v_00_u03c3_2303_, lean_object* v_00_u03b1_2304_, lean_object* v_ext_2305_, lean_object* v_as_2306_, lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_b_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2302_, v_00_u03c3_2303_, v_00_u03b1_2304_, v_ext_2305_, v_as_2306_, v_sz_boxed_2310_, v_i_boxed_2311_, v_b_2309_);
lean_dec_ref(v_as_2306_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2313_, lean_object* v_s_2314_){
_start:
{
lean_object* v_stateStack_2315_; 
v_stateStack_2315_ = lean_ctor_get(v_s_2314_, 0);
lean_inc(v_stateStack_2315_);
if (lean_obj_tag(v_stateStack_2315_) == 1)
{
lean_object* v_head_2316_; lean_object* v_scopedEntries_2317_; lean_object* v_newEntries_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2345_; 
v_head_2316_ = lean_ctor_get(v_stateStack_2315_, 0);
lean_inc(v_head_2316_);
v_scopedEntries_2317_ = lean_ctor_get(v_s_2314_, 1);
v_newEntries_2318_ = lean_ctor_get(v_s_2314_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_s_2314_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_s_2314_, 0);
lean_dec(v_unused_2346_);
v___x_2320_ = v_s_2314_;
v_isShared_2321_ = v_isSharedCheck_2345_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_newEntries_2318_);
lean_inc(v_scopedEntries_2317_);
lean_dec(v_s_2314_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2345_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_tail_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2343_; 
v_tail_2322_ = lean_ctor_get(v_stateStack_2315_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_stateStack_2315_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_stateStack_2315_, 0);
lean_dec(v_unused_2344_);
v___x_2324_ = v_stateStack_2315_;
v_isShared_2325_ = v_isSharedCheck_2343_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_tail_2322_);
lean_dec(v_stateStack_2315_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2343_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_state_2326_; lean_object* v_activeScopes_2327_; uint8_t v_delimitsLocal_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2342_; 
v_state_2326_ = lean_ctor_get(v_head_2316_, 0);
v_activeScopes_2327_ = lean_ctor_get(v_head_2316_, 1);
v_delimitsLocal_2328_ = lean_ctor_get_uint8(v_head_2316_, sizeof(void*)*2);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_head_2316_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2330_ = v_head_2316_;
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_activeScopes_2327_);
lean_inc(v_state_2326_);
lean_dec(v_head_2316_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2332_ = lean_apply_1(v_f_2313_, v_state_2326_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2332_);
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_activeScopes_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2341_, sizeof(void*)*2, v_delimitsLocal_2328_);
v___x_2334_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2334_);
v___x_2336_ = v___x_2324_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_tail_2322_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2336_);
v___x_2338_ = v___x_2320_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_scopedEntries_2317_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_newEntries_2318_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2315_);
lean_dec(v_f_2313_);
return v_s_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2347_, lean_object* v_env_2348_, lean_object* v_f_2349_){
_start:
{
lean_object* v_ext_2350_; lean_object* v_toEnvExtension_2351_; lean_object* v_asyncMode_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_ext_2350_ = lean_ctor_get(v_ext_2347_, 1);
lean_inc_ref(v_ext_2350_);
lean_dec_ref(v_ext_2347_);
v_toEnvExtension_2351_ = lean_ctor_get(v_ext_2350_, 0);
v_asyncMode_2352_ = lean_ctor_get(v_toEnvExtension_2351_, 2);
lean_inc(v_asyncMode_2352_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2353_, 0, v_f_2349_);
v___x_2354_ = lean_box(0);
v___x_2355_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2350_, v_env_2348_, v___f_2353_, v_asyncMode_2352_, v___x_2354_);
lean_dec(v_asyncMode_2352_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_00_u03c3_2358_, lean_object* v_ext_2359_, lean_object* v_env_2360_, lean_object* v_f_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2359_, v_env_2360_, v_f_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2363_, lean_object* v_____s_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_apply_2(v_toPure_2363_, lean_box(0), v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2367_, lean_object* v_toPure_2368_, lean_object* v_r_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2367_);
v___x_2371_ = lean_apply_2(v_toPure_2368_, lean_box(0), v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2372_, lean_object* v_toBind_2373_, lean_object* v___f_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_modifyEnv_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_modifyEnv_2378_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc(v_modifyEnv_2378_);
lean_dec_ref(v_inst_2372_);
v___x_2379_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2379_, 0, lean_box(0));
lean_closure_set(v___x_2379_, 1, lean_box(0));
lean_closure_set(v___x_2379_, 2, lean_box(0));
lean_closure_set(v___x_2379_, 3, v_a_2375_);
v___x_2380_ = lean_apply_1(v_modifyEnv_2378_, v___x_2379_);
v___x_2381_ = lean_apply_4(v_toBind_2373_, lean_box(0), lean_box(0), v___x_2380_, v___f_2374_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2382_, lean_object* v_inst_2383_, lean_object* v_toBind_2384_, lean_object* v_inst_2385_, lean_object* v___f_2386_, lean_object* v_____do__lift_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2388_ = lean_box(0);
v___f_2389_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2389_, 0, v___x_2388_);
lean_closure_set(v___f_2389_, 1, v_toPure_2382_);
lean_inc(v_toBind_2384_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2390_, 0, v_inst_2383_);
lean_closure_set(v___f_2390_, 1, v_toBind_2384_);
lean_closure_set(v___f_2390_, 2, v___f_2389_);
v_sz_2391_ = lean_array_size(v_____do__lift_2387_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2385_, v_____do__lift_2387_, v___f_2390_, v_sz_2391_, v___x_2392_, v___x_2388_);
v___x_2394_ = lean_apply_4(v_toBind_2384_, lean_box(0), lean_box(0), v___x_2393_, v___f_2386_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = l_Lean_scopedEnvExtensionsRef;
v___x_2396_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2396_, 0, lean_box(0));
lean_closure_set(v___x_2396_, 1, lean_box(0));
lean_closure_set(v___x_2396_, 2, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_){
_start:
{
lean_object* v_toApplicative_2400_; lean_object* v_toBind_2401_; lean_object* v_toPure_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; 
v_toApplicative_2400_ = lean_ctor_get(v_inst_2397_, 0);
v_toBind_2401_ = lean_ctor_get(v_inst_2397_, 1);
lean_inc_n(v_toBind_2401_, 2);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2400_, 1);
lean_inc_n(v_toPure_2402_, 2);
v___x_2403_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2404_ = lean_apply_2(v_inst_2399_, lean_box(0), v___x_2403_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2405_, 0, v_toPure_2402_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2406_, 0, v_toPure_2402_);
lean_closure_set(v___f_2406_, 1, v_inst_2398_);
lean_closure_set(v___f_2406_, 2, v_toBind_2401_);
lean_closure_set(v___f_2406_, 3, v_inst_2397_);
lean_closure_set(v___f_2406_, 4, v___f_2405_);
v___x_2407_ = lean_apply_4(v_toBind_2401_, lean_box(0), lean_box(0), v___x_2404_, v___f_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_pushScope___redArg(v_inst_2409_, v_inst_2410_, v_inst_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2413_, lean_object* v_toBind_2414_, lean_object* v___f_2415_, lean_object* v_a_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_modifyEnv_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_modifyEnv_2419_ = lean_ctor_get(v_inst_2413_, 1);
lean_inc(v_modifyEnv_2419_);
lean_dec_ref(v_inst_2413_);
v___x_2420_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2420_, 0, lean_box(0));
lean_closure_set(v___x_2420_, 1, lean_box(0));
lean_closure_set(v___x_2420_, 2, lean_box(0));
lean_closure_set(v___x_2420_, 3, v_a_2416_);
v___x_2421_ = lean_apply_1(v_modifyEnv_2419_, v___x_2420_);
v___x_2422_ = lean_apply_4(v_toBind_2414_, lean_box(0), lean_box(0), v___x_2421_, v___f_2415_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2423_, lean_object* v_inst_2424_, lean_object* v_toBind_2425_, lean_object* v_inst_2426_, lean_object* v___f_2427_, lean_object* v_____do__lift_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; size_t v_sz_2432_; size_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2429_ = lean_box(0);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2430_, 0, v___x_2429_);
lean_closure_set(v___f_2430_, 1, v_toPure_2423_);
lean_inc(v_toBind_2425_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2431_, 0, v_inst_2424_);
lean_closure_set(v___f_2431_, 1, v_toBind_2425_);
lean_closure_set(v___f_2431_, 2, v___f_2430_);
v_sz_2432_ = lean_array_size(v_____do__lift_2428_);
v___x_2433_ = ((size_t)0ULL);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2426_, v_____do__lift_2428_, v___f_2431_, v_sz_2432_, v___x_2433_, v___x_2429_);
v___x_2435_ = lean_apply_4(v_toBind_2425_, lean_box(0), lean_box(0), v___x_2434_, v___f_2427_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_){
_start:
{
lean_object* v_toApplicative_2439_; lean_object* v_toBind_2440_; lean_object* v_toPure_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; 
v_toApplicative_2439_ = lean_ctor_get(v_inst_2436_, 0);
v_toBind_2440_ = lean_ctor_get(v_inst_2436_, 1);
lean_inc_n(v_toBind_2440_, 2);
v_toPure_2441_ = lean_ctor_get(v_toApplicative_2439_, 1);
lean_inc_n(v_toPure_2441_, 2);
v___x_2442_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2443_ = lean_apply_2(v_inst_2438_, lean_box(0), v___x_2442_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2444_, 0, v_toPure_2441_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2445_, 0, v_toPure_2441_);
lean_closure_set(v___f_2445_, 1, v_inst_2437_);
lean_closure_set(v___f_2445_, 2, v_toBind_2440_);
lean_closure_set(v___f_2445_, 3, v_inst_2436_);
lean_closure_set(v___f_2445_, 4, v___f_2444_);
v___x_2446_ = lean_apply_4(v_toBind_2440_, lean_box(0), lean_box(0), v___x_2443_, v___f_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_popScope___redArg(v_inst_2448_, v_inst_2449_, v_inst_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2452_, lean_object* v_depth_2453_, lean_object* v_x_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2452_, v_x_2454_, v_depth_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2456_, lean_object* v_depth_2457_, lean_object* v_toBind_2458_, lean_object* v___f_2459_, lean_object* v_a_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_modifyEnv_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_modifyEnv_2463_ = lean_ctor_get(v_inst_2456_, 1);
lean_inc(v_modifyEnv_2463_);
lean_dec_ref(v_inst_2456_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2464_, 0, v_a_2460_);
lean_closure_set(v___f_2464_, 1, v_depth_2457_);
v___x_2465_ = lean_apply_1(v_modifyEnv_2463_, v___f_2464_);
v___x_2466_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v___x_2465_, v___f_2459_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2467_, lean_object* v_inst_2468_, lean_object* v_depth_2469_, lean_object* v_toBind_2470_, lean_object* v_inst_2471_, lean_object* v___f_2472_, lean_object* v_____do__lift_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; size_t v_sz_2477_; size_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2474_ = lean_box(0);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2475_, 0, v___x_2474_);
lean_closure_set(v___f_2475_, 1, v_toPure_2467_);
lean_inc(v_toBind_2470_);
v___f_2476_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2476_, 0, v_inst_2468_);
lean_closure_set(v___f_2476_, 1, v_depth_2469_);
lean_closure_set(v___f_2476_, 2, v_toBind_2470_);
lean_closure_set(v___f_2476_, 3, v___f_2475_);
v_sz_2477_ = lean_array_size(v_____do__lift_2473_);
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2471_, v_____do__lift_2473_, v___f_2476_, v_sz_2477_, v___x_2478_, v___x_2474_);
v___x_2480_ = lean_apply_4(v_toBind_2470_, lean_box(0), lean_box(0), v___x_2479_, v___f_2472_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_depth_2484_){
_start:
{
lean_object* v_toApplicative_2485_; lean_object* v_toBind_2486_; lean_object* v_toPure_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
v_toApplicative_2485_ = lean_ctor_get(v_inst_2481_, 0);
v_toBind_2486_ = lean_ctor_get(v_inst_2481_, 1);
lean_inc_n(v_toBind_2486_, 2);
v_toPure_2487_ = lean_ctor_get(v_toApplicative_2485_, 1);
lean_inc_n(v_toPure_2487_, 2);
v___x_2488_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2489_ = lean_apply_2(v_inst_2483_, lean_box(0), v___x_2488_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2490_, 0, v_toPure_2487_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2491_, 0, v_toPure_2487_);
lean_closure_set(v___f_2491_, 1, v_inst_2482_);
lean_closure_set(v___f_2491_, 2, v_depth_2484_);
lean_closure_set(v___f_2491_, 3, v_toBind_2486_);
lean_closure_set(v___f_2491_, 4, v_inst_2481_);
lean_closure_set(v___f_2491_, 5, v___f_2490_);
v___x_2492_ = lean_apply_4(v_toBind_2486_, lean_box(0), lean_box(0), v___x_2489_, v___f_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_depth_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_setDelimitsLocal___redArg(v_inst_2494_, v_inst_2495_, v_inst_2496_, v_depth_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2499_, lean_object* v_namespaceName_2500_, lean_object* v_x_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2499_, v_x_2501_, v_namespaceName_2500_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2503_, lean_object* v_namespaceName_2504_, lean_object* v_toBind_2505_, lean_object* v___f_2506_, lean_object* v_a_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_modifyEnv_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_modifyEnv_2510_ = lean_ctor_get(v_inst_2503_, 1);
lean_inc(v_modifyEnv_2510_);
lean_dec_ref(v_inst_2503_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2511_, 0, v_a_2507_);
lean_closure_set(v___f_2511_, 1, v_namespaceName_2504_);
v___x_2512_ = lean_apply_1(v_modifyEnv_2510_, v___f_2511_);
v___x_2513_ = lean_apply_4(v_toBind_2505_, lean_box(0), lean_box(0), v___x_2512_, v___f_2506_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2514_, lean_object* v_inst_2515_, lean_object* v_namespaceName_2516_, lean_object* v_toBind_2517_, lean_object* v_inst_2518_, lean_object* v___f_2519_, lean_object* v_____do__lift_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___f_2522_; lean_object* v___f_2523_; size_t v_sz_2524_; size_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2521_ = lean_box(0);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2522_, 0, v___x_2521_);
lean_closure_set(v___f_2522_, 1, v_toPure_2514_);
lean_inc(v_toBind_2517_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2523_, 0, v_inst_2515_);
lean_closure_set(v___f_2523_, 1, v_namespaceName_2516_);
lean_closure_set(v___f_2523_, 2, v_toBind_2517_);
lean_closure_set(v___f_2523_, 3, v___f_2522_);
v_sz_2524_ = lean_array_size(v_____do__lift_2520_);
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2518_, v_____do__lift_2520_, v___f_2523_, v_sz_2524_, v___x_2525_, v___x_2521_);
v___x_2527_ = lean_apply_4(v_toBind_2517_, lean_box(0), lean_box(0), v___x_2526_, v___f_2519_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_namespaceName_2531_){
_start:
{
lean_object* v_toApplicative_2532_; lean_object* v_toBind_2533_; lean_object* v_toPure_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; 
v_toApplicative_2532_ = lean_ctor_get(v_inst_2528_, 0);
v_toBind_2533_ = lean_ctor_get(v_inst_2528_, 1);
lean_inc_n(v_toBind_2533_, 2);
v_toPure_2534_ = lean_ctor_get(v_toApplicative_2532_, 1);
lean_inc_n(v_toPure_2534_, 2);
v___x_2535_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2536_ = lean_apply_2(v_inst_2530_, lean_box(0), v___x_2535_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2537_, 0, v_toPure_2534_);
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2538_, 0, v_toPure_2534_);
lean_closure_set(v___f_2538_, 1, v_inst_2529_);
lean_closure_set(v___f_2538_, 2, v_namespaceName_2531_);
lean_closure_set(v___f_2538_, 3, v_toBind_2533_);
lean_closure_set(v___f_2538_, 4, v_inst_2528_);
lean_closure_set(v___f_2538_, 5, v___f_2537_);
v___x_2539_ = lean_apply_4(v_toBind_2533_, lean_box(0), lean_box(0), v___x_2536_, v___f_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_namespaceName_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_activateScoped___redArg(v_inst_2541_, v_inst_2542_, v_inst_2543_, v_namespaceName_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2547_){
_start:
{
lean_inc(v___y_2547_);
return v___y_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2548_);
lean_dec(v___y_2548_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2550_, lean_object* v_a_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_a_2551_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2555_, lean_object* v_a_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2555_, v_a_2556_, v___y_2557_);
lean_dec_ref(v___y_2557_);
lean_dec(v_x_2555_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_initial_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2568_){
_start:
{
lean_object* v_name_2570_; lean_object* v_addEntry_2571_; lean_object* v_initial_2572_; lean_object* v_finalizeImport_2573_; lean_object* v_exportEntry_x3f_2574_; lean_object* v___f_2575_; lean_object* v___f_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_name_2570_ = lean_ctor_get(v_descr_2568_, 0);
lean_inc(v_name_2570_);
v_addEntry_2571_ = lean_ctor_get(v_descr_2568_, 1);
lean_inc(v_addEntry_2571_);
v_initial_2572_ = lean_ctor_get(v_descr_2568_, 2);
lean_inc(v_initial_2572_);
v_finalizeImport_2573_ = lean_ctor_get(v_descr_2568_, 3);
lean_inc(v_finalizeImport_2573_);
v_exportEntry_x3f_2574_ = lean_ctor_get(v_descr_2568_, 4);
lean_inc_ref(v_exportEntry_x3f_2574_);
lean_dec_ref(v_descr_2568_);
v___f_2575_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2576_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2577_, 0, v_initial_2572_);
v___x_2578_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2578_, 0, v_name_2570_);
lean_ctor_set(v___x_2578_, 1, v___f_2577_);
lean_ctor_set(v___x_2578_, 2, v___f_2576_);
lean_ctor_set(v___x_2578_, 3, v___f_2575_);
lean_ctor_set(v___x_2578_, 4, v_addEntry_2571_);
lean_ctor_set(v___x_2578_, 5, v_finalizeImport_2573_);
lean_ctor_set(v___x_2578_, 6, v_exportEntry_x3f_2574_);
v___x_2579_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2580_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2583_, lean_object* v_00_u03c3_2584_, lean_object* v_descr_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2588_, lean_object* v_00_u03c3_2589_, lean_object* v_descr_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2588_, v_00_u03c3_2589_, v_descr_2590_);
return v_res_2592_;
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
