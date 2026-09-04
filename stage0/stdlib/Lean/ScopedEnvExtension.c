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
size_t v_x_1052__boxed_332_; lean_object* v_res_333_; 
v_x_1052__boxed_332_ = lean_unbox_usize(v_x_330_);
lean_dec(v_x_330_);
v_res_333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_329_, v_x_1052__boxed_332_, v_x_331_);
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
lean_object* v_ks_575_; lean_object* v_vs_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_594_; 
v_ks_575_ = lean_ctor_get(v_x_524_, 0);
v_vs_576_ = lean_ctor_get(v_x_524_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_594_ == 0)
{
v___x_578_ = v_x_524_;
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_vs_576_);
lean_inc(v_ks_575_);
lean_dec(v_x_524_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_594_;
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
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_ks_575_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_vs_576_);
v___x_581_ = v_reuseFailAlloc_593_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v_newNode_582_; size_t v___x_583_; uint8_t v___x_584_; 
v_newNode_582_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_581_, v_x_527_, v_x_528_);
v___x_583_ = ((size_t)7ULL);
v___x_584_ = lean_usize_dec_le(v___x_583_, v_x_526_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_582_);
v___x_586_ = lean_unsigned_to_nat(4u);
v___x_587_ = lean_nat_dec_lt(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
if (v___x_587_ == 0)
{
lean_object* v_ks_588_; lean_object* v_vs_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_ks_588_ = lean_ctor_get(v_newNode_582_, 0);
lean_inc_ref(v_ks_588_);
v_vs_589_ = lean_ctor_get(v_newNode_582_, 1);
lean_inc_ref(v_vs_589_);
lean_dec_ref(v_newNode_582_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_592_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_526_, v_ks_588_, v_vs_589_, v___x_590_, v___x_591_);
lean_dec_ref(v_vs_589_);
lean_dec_ref(v_ks_588_);
return v___x_592_;
}
else
{
return v_newNode_582_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_595_, lean_object* v_keys_596_, lean_object* v_vals_597_, lean_object* v_i_598_, lean_object* v_entries_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_keys_596_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v_entries_599_;
}
else
{
lean_object* v_k_602_; lean_object* v_v_603_; uint64_t v___y_605_; 
v_k_602_ = lean_array_fget_borrowed(v_keys_596_, v_i_598_);
v_v_603_ = lean_array_fget_borrowed(v_vals_597_, v_i_598_);
if (lean_obj_tag(v_k_602_) == 0)
{
uint64_t v___x_616_; 
v___x_616_ = 1723ULL;
v___y_605_ = v___x_616_;
goto v___jp_604_;
}
else
{
uint64_t v_hash_617_; 
v_hash_617_ = lean_ctor_get_uint64(v_k_602_, sizeof(void*)*2);
v___y_605_ = v_hash_617_;
goto v___jp_604_;
}
v___jp_604_:
{
size_t v_h_606_; size_t v___x_607_; lean_object* v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v_h_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_h_606_ = lean_uint64_to_usize(v___y_605_);
v___x_607_ = ((size_t)5ULL);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v_depth_595_, v___x_609_);
v___x_611_ = lean_usize_mul(v___x_607_, v___x_610_);
v_h_612_ = lean_usize_shift_right(v_h_606_, v___x_611_);
v___x_613_ = lean_nat_add(v_i_598_, v___x_608_);
lean_dec(v_i_598_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_599_, v_h_612_, v_depth_595_, v_k_602_, v_v_603_);
v_i_598_ = v___x_613_;
v_entries_599_ = v___x_614_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_618_, lean_object* v_keys_619_, lean_object* v_vals_620_, lean_object* v_i_621_, lean_object* v_entries_622_){
_start:
{
size_t v_depth_boxed_623_; lean_object* v_res_624_; 
v_depth_boxed_623_ = lean_unbox_usize(v_depth_618_);
lean_dec(v_depth_618_);
v_res_624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_623_, v_keys_619_, v_vals_620_, v_i_621_, v_entries_622_);
lean_dec_ref(v_vals_620_);
lean_dec_ref(v_keys_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_1426__boxed_630_; size_t v_x_1427__boxed_631_; lean_object* v_res_632_; 
v_x_1426__boxed_630_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_x_1427__boxed_631_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_res_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_625_, v_x_1426__boxed_630_, v_x_1427__boxed_631_, v_x_628_, v_x_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
uint64_t v___y_637_; 
if (lean_obj_tag(v_x_634_) == 0)
{
uint64_t v___x_641_; 
v___x_641_ = 1723ULL;
v___y_637_ = v___x_641_;
goto v___jp_636_;
}
else
{
uint64_t v_hash_642_; 
v_hash_642_ = lean_ctor_get_uint64(v_x_634_, sizeof(void*)*2);
v___y_637_ = v_hash_642_;
goto v___jp_636_;
}
v___jp_636_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_uint64_to_usize(v___y_637_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_633_, v___x_638_, v___x_639_, v_x_634_, v_x_635_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_stage_u2081_646_; 
v_stage_u2081_646_ = lean_ctor_get_uint8(v_x_643_, sizeof(void*)*2);
if (v_stage_u2081_646_ == 0)
{
lean_object* v_map_u2081_647_; lean_object* v_map_u2082_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
v_map_u2081_647_ = lean_ctor_get(v_x_643_, 0);
v_map_u2082_648_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v_x_643_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_map_u2082_648_);
lean_inc(v_map_u2081_647_);
lean_dec(v_x_643_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_648_, v_x_644_, v_x_645_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_map_u2081_647_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*2, v_stage_u2081_646_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_map_u2081_657_; lean_object* v_map_u2082_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_map_u2081_657_ = lean_ctor_get(v_x_643_, 0);
v_map_u2082_658_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v_x_643_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_map_u2082_658_);
lean_inc(v_map_u2081_657_);
lean_dec(v_x_643_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_657_, v_x_644_, v_x_645_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_map_u2082_658_);
lean_ctor_set_uint8(v_reuseFailAlloc_665_, sizeof(void*)*2, v_stage_u2081_646_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(32u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = ((size_t)5ULL);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_unsigned_to_nat(32u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_675_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_671_);
lean_ctor_set(v___x_675_, 3, v___x_671_);
lean_ctor_set_usize(v___x_675_, 4, v___x_670_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_676_, lean_object* v_ns_677_, lean_object* v_b_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_676_, v_ns_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_681_ = l_Lean_PersistentArray_push___redArg(v___x_680_, v_b_678_);
v___x_682_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_676_, v_ns_677_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_val_683_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_679_, 1);
v___x_684_ = l_Lean_PersistentArray_push___redArg(v_val_683_, v_b_678_);
v___x_685_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_676_, v_ns_677_, v___x_684_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_686_, lean_object* v_scopedEntries_687_, lean_object* v_ns_688_, lean_object* v_b_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_687_, v_ns_688_, v_b_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_692_, v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_695_, v_x_696_, v_x_697_);
lean_dec(v_x_697_);
lean_dec_ref(v_x_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_700_, v_x_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_708_, v_x_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec_ref(v_x_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_712_, lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_713_, v_a_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_716_, v_m_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_m_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_721_, v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_725_, lean_object* v_m_726_, lean_object* v_a_727_, lean_object* v_b_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_726_, v_a_727_, v_b_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, size_t v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_731_, v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
size_t v_x_1727__boxed_739_; lean_object* v_res_740_; 
v_x_1727__boxed_739_ = lean_unbox_usize(v_x_737_);
lean_dec(v_x_737_);
v_res_740_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_735_, v_x_736_, v_x_1727__boxed_739_, v_x_738_);
lean_dec(v_x_738_);
lean_dec_ref(v_x_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_741_, lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_742_, v_x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_745_, v_a_746_, v_x_747_);
lean_dec(v_x_747_);
lean_dec(v_a_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_749_, lean_object* v_x_750_, size_t v_x_751_, size_t v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_750_, v_x_751_, v_x_752_, v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
size_t v_x_1743__boxed_762_; size_t v_x_1744__boxed_763_; lean_object* v_res_764_; 
v_x_1743__boxed_762_ = lean_unbox_usize(v_x_758_);
lean_dec(v_x_758_);
v_x_1744__boxed_763_ = lean_unbox_usize(v_x_759_);
lean_dec(v_x_759_);
v_res_764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_756_, v_x_757_, v_x_1743__boxed_762_, v_x_1744__boxed_763_, v_x_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_769_, lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_769_, v_a_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec(v_a_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_774_, lean_object* v_data_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_777_, lean_object* v_a_778_, lean_object* v_b_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_778_, v_b_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_782_, lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_heq_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_783_, v_vals_784_, v_i_786_, v_k_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_789_, lean_object* v_keys_790_, lean_object* v_vals_791_, lean_object* v_heq_792_, lean_object* v_i_793_, lean_object* v_k_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_789_, v_keys_790_, v_vals_791_, v_heq_792_, v_i_793_, v_k_794_);
lean_dec(v_k_794_);
lean_dec_ref(v_vals_791_);
lean_dec_ref(v_keys_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_796_, lean_object* v_n_797_, lean_object* v_k_798_, lean_object* v_v_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_797_, v_k_798_, v_v_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_801_, size_t v_depth_802_, lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_heq_805_, lean_object* v_i_806_, lean_object* v_entries_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_802_, v_keys_803_, v_vals_804_, v_i_806_, v_entries_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_809_, lean_object* v_depth_810_, lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_heq_813_, lean_object* v_i_814_, lean_object* v_entries_815_){
_start:
{
size_t v_depth_boxed_816_; lean_object* v_res_817_; 
v_depth_boxed_816_ = lean_unbox_usize(v_depth_810_);
lean_dec(v_depth_810_);
v_res_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_809_, v_depth_boxed_816_, v_keys_811_, v_vals_812_, v_heq_813_, v_i_814_, v_entries_815_);
lean_dec_ref(v_vals_812_);
lean_dec_ref(v_keys_811_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_818_, lean_object* v_i_819_, lean_object* v_source_820_, lean_object* v_target_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_819_, v_source_820_, v_target_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_824_, v_x_825_, v_x_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_833_, lean_object* v_as_834_, size_t v_sz_835_, size_t v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_a_841_; uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_lt(v_i_836_, v_sz_835_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v_descr_833_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_b_837_);
return v___x_846_;
}
else
{
lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_887_; 
v_fst_847_ = lean_ctor_get(v_b_837_, 0);
v_snd_848_ = lean_ctor_get(v_b_837_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_b_837_);
if (v_isSharedCheck_887_ == 0)
{
v___x_850_ = v_b_837_;
v_isShared_851_ = v_isSharedCheck_887_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_inc(v_fst_847_);
lean_dec(v_b_837_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_887_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; 
v_a_852_ = lean_array_uget_borrowed(v_as_834_, v_i_836_);
if (lean_obj_tag(v_a_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_ofOLeanEntry_854_; lean_object* v_addEntry_855_; lean_object* v___x_856_; 
v_a_853_ = lean_ctor_get(v_a_852_, 0);
v_ofOLeanEntry_854_ = lean_ctor_get(v_descr_833_, 2);
v_addEntry_855_ = lean_ctor_get(v_descr_833_, 4);
lean_inc_ref(v_ofOLeanEntry_854_);
lean_inc_ref(v___y_838_);
lean_inc(v_a_853_);
lean_inc(v_fst_847_);
v___x_856_ = lean_apply_4(v_ofOLeanEntry_854_, v_fst_847_, v_a_853_, v___y_838_, lean_box(0));
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
lean_inc(v_addEntry_855_);
v___x_858_ = lean_apply_2(v_addEntry_855_, v_fst_847_, v_a_857_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_848_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v_a_841_ = v___x_860_;
goto v___jp_840_;
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_dec_ref(v_descr_833_);
v_a_862_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_856_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_856_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v_ofOLeanEntry_872_; lean_object* v___x_873_; 
v_a_870_ = lean_ctor_get(v_a_852_, 0);
v_a_871_ = lean_ctor_get(v_a_852_, 1);
v_ofOLeanEntry_872_ = lean_ctor_get(v_descr_833_, 2);
lean_inc_ref(v_ofOLeanEntry_872_);
lean_inc_ref(v___y_838_);
lean_inc(v_a_871_);
lean_inc(v_fst_847_);
v___x_873_ = lean_apply_4(v_ofOLeanEntry_872_, v_fst_847_, v_a_871_, v___y_838_, lean_box(0));
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
lean_inc(v_a_870_);
v___x_875_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_848_, v_a_870_, v_a_874_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_875_);
v___x_877_ = v___x_850_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_fst_847_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_841_ = v___x_877_;
goto v___jp_840_;
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_dec_ref(v_descr_833_);
v_a_879_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_873_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_873_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
v___jp_840_:
{
size_t v___x_842_; size_t v___x_843_; 
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_836_, v___x_842_);
v_i_836_ = v___x_843_;
v_b_837_ = v_a_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_888_, lean_object* v_as_889_, lean_object* v_sz_890_, lean_object* v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_890_);
lean_dec(v_sz_890_);
v_i_boxed_896_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_888_, v_as_889_, v_sz_boxed_895_, v_i_boxed_896_, v_b_892_, v___y_893_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v_as_889_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_898_, lean_object* v_as_899_, size_t v_sz_900_, size_t v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v_descr_898_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_902_);
return v___x_906_;
}
else
{
lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_932_; 
v_fst_907_ = lean_ctor_get(v_b_902_, 0);
v_snd_908_ = lean_ctor_get(v_b_902_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_b_902_);
if (v_isSharedCheck_932_ == 0)
{
v___x_910_ = v_b_902_;
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snd_908_);
lean_inc(v_fst_907_);
lean_dec(v_b_902_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_a_912_; lean_object* v___x_914_; 
v_a_912_ = lean_array_uget_borrowed(v_as_899_, v_i_901_);
if (v_isShared_911_ == 0)
{
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_907_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_snd_908_);
v___x_914_ = v_reuseFailAlloc_931_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_sz_915_ = lean_array_size(v_a_912_);
v___x_916_ = ((size_t)0ULL);
lean_inc_ref(v_descr_898_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_898_, v_a_912_, v_sz_915_, v___x_916_, v___x_914_, v___y_903_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v_fst_919_ = lean_ctor_get(v_a_918_, 0);
v_snd_920_ = lean_ctor_get(v_a_918_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_930_ == 0)
{
v___x_922_ = v_a_918_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_inc(v_fst_919_);
lean_dec(v_a_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_fst_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_snd_920_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
size_t v___x_926_; size_t v___x_927_; 
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_901_, v___x_926_);
v_i_901_ = v___x_927_;
v_b_902_ = v___x_925_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_898_);
return v___x_917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_933_, lean_object* v_as_934_, lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_941_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_933_, v_as_934_, v_sz_boxed_940_, v_i_boxed_941_, v_b_937_, v___y_938_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_as_934_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_943_, lean_object* v_as_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_mkInitial_947_; lean_object* v_finalizeImport_948_; lean_object* v___x_949_; 
v_mkInitial_947_ = lean_ctor_get(v_descr_943_, 1);
v_finalizeImport_948_ = lean_ctor_get(v_descr_943_, 5);
lean_inc(v_finalizeImport_948_);
lean_inc_ref(v_mkInitial_947_);
v___x_949_ = lean_apply_1(v_mkInitial_947_, lean_box(0));
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; size_t v_sz_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = 1;
v___x_952_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_a_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v_sz_954_ = lean_array_size(v_as_944_);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_943_, v_as_944_, v_sz_954_, v___x_955_, v___x_953_, v_a_945_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_978_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_978_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_978_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_978_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_977_; 
v_fst_961_ = lean_ctor_get(v_a_957_, 0);
v_snd_962_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_977_ == 0)
{
v___x_964_ = v_a_957_;
v_isShared_965_ = v_isSharedCheck_977_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v_a_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_977_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_966_ = lean_apply_1(v_finalizeImport_948_, v_fst_961_);
v___x_967_ = l_Lean_NameSet_empty;
v___x_968_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*2, v___x_951_);
v___x_969_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 1, v___x_969_);
lean_ctor_set(v___x_964_, 0, v___x_968_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_976_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_snd_962_);
lean_ctor_set(v___x_972_, 2, v___x_969_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_972_);
v___x_974_ = v___x_959_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_finalizeImport_948_);
v_a_979_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_956_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_956_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
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
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_finalizeImport_948_);
lean_dec_ref(v_descr_943_);
v_a_987_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_949_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_949_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_995_, lean_object* v_as_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_995_, v_as_996_, v_a_997_);
lean_dec_ref(v_a_997_);
lean_dec_ref(v_as_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_00_u03c3_1002_, lean_object* v_descr_1003_, lean_object* v_as_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1003_, v_as_1004_, v_a_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_00_u03c3_1010_, lean_object* v_descr_1011_, lean_object* v_as_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1008_, v_00_u03b2_1009_, v_00_u03c3_1010_, v_descr_1011_, v_as_1012_, v_a_1013_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_as_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03c3_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_descr_1019_, lean_object* v_as_1020_, size_t v_sz_1021_, size_t v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1019_, v_as_1020_, v_sz_1021_, v_i_1022_, v_b_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_00_u03c3_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_descr_1030_, lean_object* v_as_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1027_, v_00_u03c3_1028_, v_00_u03b2_1029_, v_descr_1030_, v_as_1031_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1034_, v___y_1035_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_as_1031_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03c3_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_descr_1043_, lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1043_, v_as_1044_, v_sz_1045_, v_i_1046_, v_b_1047_, v___y_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03c3_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_descr_1054_, lean_object* v_as_1055_, lean_object* v_sz_1056_, lean_object* v_i_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1056_);
lean_dec(v_sz_1056_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1051_, v_00_u03c3_1052_, v_00_u03b2_1053_, v_descr_1054_, v_as_1055_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1058_, v___y_1059_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v_as_1055_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1064_, lean_object* v_descr_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_object* v___x_1069_; 
lean_dec(v_a_1066_);
lean_dec_ref(v_descr_1065_);
v___x_1069_ = l_List_reverse___redArg(v_a_1068_);
return v___x_1069_;
}
else
{
lean_object* v_head_1070_; lean_object* v_tail_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1096_; 
v_head_1070_ = lean_ctor_get(v_a_1067_, 0);
v_tail_1071_ = lean_ctor_get(v_a_1067_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1073_ = v_a_1067_;
v_isShared_1074_ = v_isSharedCheck_1096_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_tail_1071_);
lean_inc(v_head_1070_);
lean_dec(v_a_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1096_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___y_1076_; lean_object* v_state_1081_; lean_object* v_activeScopes_1082_; uint8_t v_delimitsLocal_1083_; uint8_t v___x_1084_; 
v_state_1081_ = lean_ctor_get(v_head_1070_, 0);
v_activeScopes_1082_ = lean_ctor_get(v_head_1070_, 1);
v_delimitsLocal_1083_ = lean_ctor_get_uint8(v_head_1070_, sizeof(void*)*2);
v___x_1084_ = l_Lean_NameSet_contains(v_activeScopes_1082_, v_a_1064_);
if (v___x_1084_ == 0)
{
v___y_1076_ = v_head_1070_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_activeScopes_1082_);
lean_inc(v_state_1081_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_head_1070_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1094_ = lean_ctor_get(v_head_1070_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_head_1070_, 0);
lean_dec(v_unused_1095_);
v___x_1086_ = v_head_1070_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v_head_1070_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_addEntry_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_addEntry_1088_ = lean_ctor_get(v_descr_1065_, 4);
lean_inc(v_addEntry_1088_);
lean_inc(v_a_1066_);
v___x_1089_ = lean_apply_2(v_addEntry_1088_, v_state_1081_, v_a_1066_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_activeScopes_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*2, v_delimitsLocal_1083_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
v___y_1076_ = v___x_1091_;
goto v___jp_1075_;
}
}
}
v___jp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v_a_1068_);
lean_ctor_set(v___x_1073_, 0, v___y_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___y_1076_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1068_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_a_1067_ = v_tail_1071_;
v_a_1068_ = v___x_1078_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1097_, lean_object* v_descr_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1097_, v_descr_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_object* v___x_1107_; 
lean_dec(v_a_1104_);
lean_dec_ref(v_descr_1103_);
v___x_1107_ = l_List_reverse___redArg(v_a_1106_);
return v___x_1107_;
}
else
{
lean_object* v_head_1108_; lean_object* v_tail_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1129_; 
v_head_1108_ = lean_ctor_get(v_a_1105_, 0);
v_tail_1109_ = lean_ctor_get(v_a_1105_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1111_ = v_a_1105_;
v_isShared_1112_ = v_isSharedCheck_1129_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_tail_1109_);
lean_inc(v_head_1108_);
lean_dec(v_a_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1129_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_addEntry_1113_; lean_object* v_state_1114_; lean_object* v_activeScopes_1115_; uint8_t v_delimitsLocal_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1128_; 
v_addEntry_1113_ = lean_ctor_get(v_descr_1103_, 4);
v_state_1114_ = lean_ctor_get(v_head_1108_, 0);
v_activeScopes_1115_ = lean_ctor_get(v_head_1108_, 1);
v_delimitsLocal_1116_ = lean_ctor_get_uint8(v_head_1108_, sizeof(void*)*2);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_head_1108_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1118_ = v_head_1108_;
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_activeScopes_1115_);
lean_inc(v_state_1114_);
lean_dec(v_head_1108_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_inc(v_addEntry_1113_);
lean_inc(v_a_1104_);
v___x_1120_ = lean_apply_2(v_addEntry_1113_, v_state_1114_, v_a_1104_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_activeScopes_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*2, v_delimitsLocal_1116_);
v___x_1122_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_a_1106_);
lean_ctor_set(v___x_1111_, 0, v___x_1122_);
v___x_1124_ = v___x_1111_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1106_);
v___x_1124_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v_a_1105_ = v_tail_1109_;
v_a_1106_ = v___x_1124_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1130_, lean_object* v_s_1131_, lean_object* v_e_1132_){
_start:
{
if (lean_obj_tag(v_e_1132_) == 0)
{
lean_object* v_stateStack_1133_; lean_object* v_scopedEntries_1134_; lean_object* v_newEntries_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1155_; 
v_stateStack_1133_ = lean_ctor_get(v_s_1131_, 0);
v_scopedEntries_1134_ = lean_ctor_get(v_s_1131_, 1);
v_newEntries_1135_ = lean_ctor_get(v_s_1131_, 2);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_s_1131_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1137_ = v_s_1131_;
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_newEntries_1135_);
lean_inc(v_scopedEntries_1134_);
lean_inc(v_stateStack_1133_);
lean_dec(v_s_1131_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1154_; 
v_a_1139_ = lean_ctor_get(v_e_1132_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_e_1132_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1141_ = v_e_1132_;
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v_e_1132_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_toOLeanEntry_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_toOLeanEntry_1143_ = lean_ctor_get(v_descr_1130_, 3);
lean_inc(v_toOLeanEntry_1143_);
v___x_1144_ = lean_box(0);
lean_inc(v_a_1139_);
v___x_1145_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1130_, v_a_1139_, v_stateStack_1133_, v___x_1144_);
v___x_1146_ = lean_apply_1(v_toOLeanEntry_1143_, v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1146_);
v___x_1148_ = v___x_1141_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v_newEntries_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 2, v___x_1149_);
lean_ctor_set(v___x_1137_, 0, v___x_1145_);
v___x_1151_ = v___x_1137_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_scopedEntries_1134_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1156_; lean_object* v_scopedEntries_1157_; lean_object* v_newEntries_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1180_; 
v_stateStack_1156_ = lean_ctor_get(v_s_1131_, 0);
v_scopedEntries_1157_ = lean_ctor_get(v_s_1131_, 1);
v_newEntries_1158_ = lean_ctor_get(v_s_1131_, 2);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_s_1131_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1160_ = v_s_1131_;
v_isShared_1161_ = v_isSharedCheck_1180_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_newEntries_1158_);
lean_inc(v_scopedEntries_1157_);
lean_inc(v_stateStack_1156_);
lean_dec(v_s_1131_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1180_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1179_; 
v_a_1162_ = lean_ctor_get(v_e_1132_, 0);
v_a_1163_ = lean_ctor_get(v_e_1132_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_e_1132_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1165_ = v_e_1132_;
v_isShared_1166_ = v_isSharedCheck_1179_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_inc(v_a_1162_);
lean_dec(v_e_1132_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1179_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_toOLeanEntry_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v_toOLeanEntry_1167_ = lean_ctor_get(v_descr_1130_, 3);
lean_inc(v_toOLeanEntry_1167_);
v___x_1168_ = lean_box(0);
lean_inc_n(v_a_1163_, 2);
v___x_1169_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1162_, v_descr_1130_, v_a_1163_, v_stateStack_1156_, v___x_1168_);
lean_inc(v_a_1162_);
v___x_1170_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1157_, v_a_1162_, v_a_1163_);
v___x_1171_ = lean_apply_1(v_toOLeanEntry_1167_, v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1171_);
v___x_1173_ = v___x_1165_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1162_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_newEntries_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 2, v___x_1174_);
lean_ctor_set(v___x_1160_, 1, v___x_1170_);
lean_ctor_set(v___x_1160_, 0, v___x_1169_);
v___x_1176_ = v___x_1160_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_00_u03c3_1183_, lean_object* v_descr_1184_, lean_object* v_s_1185_, lean_object* v_e_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1184_, v_s_1185_, v_e_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_00_u03b1_1190_, lean_object* v_descr_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1196_, lean_object* v_a_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_00_u03b1_1199_, lean_object* v_descr_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1197_, v_descr_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1205_, lean_object* v_a_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_00_u03b1_1208_, lean_object* v_descr_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1205_, v_a_1206_, v_00_u03b2_1207_, v_00_u03b1_1208_, v_descr_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1214_, lean_object* v_env_1215_, lean_object* v_as_1216_, size_t v_sz_1217_, size_t v_i_1218_, lean_object* v_b_1219_){
_start:
{
lean_object* v_a_1221_; uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_lt(v_i_1218_, v_sz_1217_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v_env_1215_);
lean_dec_ref(v_descr_1214_);
return v_b_1219_;
}
else
{
lean_object* v_snd_1226_; lean_object* v_fst_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1327_; 
v_snd_1226_ = lean_ctor_get(v_b_1219_, 1);
v_fst_1227_ = lean_ctor_get(v_b_1219_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_b_1219_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1229_ = v_b_1219_;
v_isShared_1230_ = v_isSharedCheck_1327_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snd_1226_);
lean_inc(v_fst_1227_);
lean_dec(v_b_1219_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1327_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_fst_1231_; lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1326_; 
v_fst_1231_ = lean_ctor_get(v_snd_1226_, 0);
v_snd_1232_ = lean_ctor_get(v_snd_1226_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_snd_1226_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1234_ = v_snd_1226_;
v_isShared_1235_ = v_isSharedCheck_1326_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_inc(v_fst_1231_);
lean_dec(v_snd_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1326_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_a_1236_; 
v_a_1236_ = lean_array_uget(v_as_1216_, v_i_1218_);
if (lean_obj_tag(v_a_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1286_; 
v_a_1237_ = lean_ctor_get(v_a_1236_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1239_ = v_a_1236_;
v_isShared_1240_ = v_isSharedCheck_1286_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v_a_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1286_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_exportEntry_x3f_1241_; lean_object* v___x_1242_; lean_object* v_exported_1243_; lean_object* v_server_1244_; lean_object* v_private_1245_; lean_object* v___y_1247_; lean_object* v_server_1248_; lean_object* v_exported_1267_; 
v_exportEntry_x3f_1241_ = lean_ctor_get(v_descr_1214_, 6);
lean_inc_ref(v_exportEntry_x3f_1241_);
lean_inc_ref(v_env_1215_);
v___x_1242_ = lean_apply_2(v_exportEntry_x3f_1241_, v_env_1215_, v_a_1237_);
v_exported_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_exported_1243_);
v_server_1244_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_server_1244_);
v_private_1245_ = lean_ctor_get(v___x_1242_, 2);
lean_inc(v_private_1245_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v_exported_1243_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_val_1277_ = lean_ctor_get(v_exported_1243_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_exported_1243_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v_exported_1243_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_val_1277_);
lean_dec(v_exported_1243_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_val_1277_);
v___x_1282_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_array_push(v_fst_1227_, v___x_1282_);
v_exported_1267_ = v___x_1283_;
goto v___jp_1266_;
}
}
}
else
{
lean_dec(v_exported_1243_);
v_exported_1267_ = v_fst_1227_;
goto v___jp_1266_;
}
v___jp_1246_:
{
if (lean_obj_tag(v_private_1245_) == 1)
{
lean_object* v_val_1249_; lean_object* v___x_1251_; 
v_val_1249_ = lean_ctor_get(v_private_1245_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v_private_1245_, 1);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_val_1249_);
v___x_1251_ = v___x_1239_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_val_1249_);
v___x_1251_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_array_push(v_snd_1232_, v___x_1251_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1252_);
lean_ctor_set(v___x_1234_, 0, v_server_1248_);
v___x_1254_ = v___x_1234_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_server_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1254_);
lean_ctor_set(v___x_1229_, 0, v___y_1247_);
v___x_1256_ = v___x_1229_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___y_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_a_1221_ = v___x_1256_;
goto v___jp_1220_;
}
}
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_private_1245_);
lean_del_object(v___x_1239_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_server_1248_);
v___x_1261_ = v___x_1234_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_server_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_snd_1232_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1261_);
lean_ctor_set(v___x_1229_, 0, v___y_1247_);
v___x_1263_ = v___x_1229_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___y_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v_a_1221_ = v___x_1263_;
goto v___jp_1220_;
}
}
}
}
v___jp_1266_:
{
if (lean_obj_tag(v_server_1244_) == 1)
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1276_; 
v_val_1268_ = lean_ctor_get(v_server_1244_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_server_1244_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1270_ = v_server_1244_;
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v_server_1244_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_val_1268_);
v___x_1273_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_array_push(v_fst_1231_, v___x_1273_);
v___y_1247_ = v_exported_1267_;
v_server_1248_ = v___x_1274_;
goto v___jp_1246_;
}
}
}
else
{
lean_dec(v_server_1244_);
v___y_1247_ = v_exported_1267_;
v_server_1248_ = v_fst_1231_;
goto v___jp_1246_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1325_; 
v_a_1287_ = lean_ctor_get(v_a_1236_, 0);
v_a_1288_ = lean_ctor_get(v_a_1236_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1290_ = v_a_1236_;
v_isShared_1291_ = v_isSharedCheck_1325_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_inc(v_a_1287_);
lean_dec(v_a_1236_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1325_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_exportEntry_x3f_1292_; lean_object* v___x_1293_; lean_object* v_exported_1294_; lean_object* v_server_1295_; lean_object* v_private_1296_; lean_object* v___y_1298_; lean_object* v_server_1299_; lean_object* v_exported_1318_; 
v_exportEntry_x3f_1292_ = lean_ctor_get(v_descr_1214_, 6);
lean_inc_ref(v_exportEntry_x3f_1292_);
lean_inc_ref(v_env_1215_);
v___x_1293_ = lean_apply_2(v_exportEntry_x3f_1292_, v_env_1215_, v_a_1288_);
v_exported_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_exported_1294_);
v_server_1295_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_server_1295_);
v_private_1296_ = lean_ctor_get(v___x_1293_, 2);
lean_inc(v_private_1296_);
lean_dec_ref(v___x_1293_);
if (lean_obj_tag(v_exported_1294_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_val_1322_ = lean_ctor_get(v_exported_1294_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_exported_1294_, 1);
lean_inc(v_a_1287_);
v___x_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_a_1287_);
lean_ctor_set(v___x_1323_, 1, v_val_1322_);
v___x_1324_ = lean_array_push(v_fst_1227_, v___x_1323_);
v_exported_1318_ = v___x_1324_;
goto v___jp_1317_;
}
else
{
lean_dec(v_exported_1294_);
v_exported_1318_ = v_fst_1227_;
goto v___jp_1317_;
}
v___jp_1297_:
{
if (lean_obj_tag(v_private_1296_) == 1)
{
lean_object* v_val_1300_; lean_object* v___x_1302_; 
v_val_1300_ = lean_ctor_get(v_private_1296_, 0);
lean_inc(v_val_1300_);
lean_dec_ref_known(v_private_1296_, 1);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_val_1300_);
v___x_1302_ = v___x_1290_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1287_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_val_1300_);
v___x_1302_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_array_push(v_snd_1232_, v___x_1302_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1303_);
lean_ctor_set(v___x_1234_, 0, v_server_1299_);
v___x_1305_ = v___x_1234_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_server_1299_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1305_);
lean_ctor_set(v___x_1229_, 0, v___y_1298_);
v___x_1307_ = v___x_1229_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___y_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
v_a_1221_ = v___x_1307_;
goto v___jp_1220_;
}
}
}
}
else
{
lean_object* v___x_1312_; 
lean_dec(v_private_1296_);
lean_del_object(v___x_1290_);
lean_dec(v_a_1287_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_server_1299_);
v___x_1312_ = v___x_1234_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_server_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1232_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1312_);
lean_ctor_set(v___x_1229_, 0, v___y_1298_);
v___x_1314_ = v___x_1229_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___y_1298_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
v_a_1221_ = v___x_1314_;
goto v___jp_1220_;
}
}
}
}
v___jp_1317_:
{
if (lean_obj_tag(v_server_1295_) == 1)
{
lean_object* v_val_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_val_1319_ = lean_ctor_get(v_server_1295_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v_server_1295_, 1);
lean_inc(v_a_1287_);
v___x_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1287_);
lean_ctor_set(v___x_1320_, 1, v_val_1319_);
v___x_1321_ = lean_array_push(v_fst_1231_, v___x_1320_);
v___y_1298_ = v_exported_1318_;
v_server_1299_ = v___x_1321_;
goto v___jp_1297_;
}
else
{
lean_dec(v_server_1295_);
v___y_1298_ = v_exported_1318_;
v_server_1299_ = v_fst_1231_;
goto v___jp_1297_;
}
}
}
}
}
}
}
v___jp_1220_:
{
size_t v___x_1222_; size_t v___x_1223_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1218_, v___x_1222_);
v_i_1218_ = v___x_1223_;
v_b_1219_ = v_a_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1328_, lean_object* v_env_1329_, lean_object* v_as_1330_, lean_object* v_sz_1331_, lean_object* v_i_1332_, lean_object* v_b_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1331_);
lean_dec(v_sz_1331_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_res_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1328_, v_env_1329_, v_as_1330_, v_sz_boxed_1334_, v_i_boxed_1335_, v_b_1333_);
lean_dec_ref(v_as_1330_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1344_, lean_object* v_env_1345_, lean_object* v_s_1346_){
_start:
{
lean_object* v_newEntries_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1364_; 
v_newEntries_1347_ = lean_ctor_get(v_s_1346_, 2);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_s_1346_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; 
v_unused_1365_ = lean_ctor_get(v_s_1346_, 1);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_s_1346_, 0);
lean_dec(v_unused_1366_);
v___x_1349_ = v_s_1346_;
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_newEntries_1347_);
lean_dec(v_s_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v_snd_1357_; lean_object* v_fst_1358_; lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1362_; 
v___x_1351_ = lean_array_mk(v_newEntries_1347_);
v___x_1352_ = l_Array_reverse___redArg(v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1354_ = lean_array_size(v___x_1352_);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1344_, v_env_1345_, v___x_1352_, v_sz_1354_, v___x_1355_, v___x_1353_);
lean_dec_ref(v___x_1352_);
v_snd_1357_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_snd_1357_);
v_fst_1358_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_fst_1358_);
lean_dec_ref(v___x_1356_);
v_fst_1359_ = lean_ctor_get(v_snd_1357_, 0);
lean_inc(v_fst_1359_);
v_snd_1360_ = lean_ctor_get(v_snd_1357_, 1);
lean_inc(v_snd_1360_);
lean_dec(v_snd_1357_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 2, v_snd_1360_);
lean_ctor_set(v___x_1349_, 1, v_fst_1359_);
lean_ctor_set(v___x_1349_, 0, v_fst_1358_);
v___x_1362_ = v___x_1349_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_fst_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_snd_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_00_u03c3_1369_, lean_object* v_descr_1370_, lean_object* v_env_1371_, lean_object* v_s_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1370_, v_env_1371_, v_s_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_00_u03c3_1376_, lean_object* v_descr_1377_, lean_object* v_env_1378_, lean_object* v_as_1379_, size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_b_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1377_, v_env_1378_, v_as_1379_, v_sz_1380_, v_i_1381_, v_b_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_00_u03c3_1386_, lean_object* v_descr_1387_, lean_object* v_env_1388_, lean_object* v_as_1389_, lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_b_1392_){
_start:
{
size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1384_, v_00_u03b2_1385_, v_00_u03c3_1386_, v_descr_1387_, v_env_1388_, v_as_1389_, v_sz_boxed_1393_, v_i_boxed_1394_, v_b_1392_);
lean_dec_ref(v_as_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1401_, v___y_1402_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_x_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1405_, lean_object* v_x_1406_){
_start:
{
lean_inc_ref(v_s_1405_);
return v_s_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1407_, lean_object* v_x_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1407_, v_x_1408_);
lean_dec_ref(v_x_1408_);
lean_dec_ref(v_s_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1415_, v_x_1416_);
lean_dec_ref(v_x_1416_);
lean_dec_ref(v_x_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_box(0);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1420_);
lean_dec_ref(v_x_1420_);
return v_res_1421_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1427_; lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___f_1427_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1428_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1429_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1430_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1433_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___f_1430_);
lean_ctor_set(v___x_1433_, 3, v___f_1429_);
lean_ctor_set(v___x_1433_, 4, v___f_1428_);
lean_ctor_set(v___x_1433_, 5, v___f_1427_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1434_){
_start:
{
lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___f_1435_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1436_, 0, v_inst_1434_);
v___f_1437_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1438_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1441_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1442_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1439_);
lean_ctor_set(v___x_1442_, 1, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v___f_1435_);
lean_ctor_set(v___x_1442_, 3, v___f_1436_);
lean_ctor_set(v___x_1442_, 4, v___f_1437_);
lean_ctor_set(v___x_1442_, 5, v___x_1441_);
lean_ctor_set(v___x_1442_, 6, v___f_1438_);
v___x_1443_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_00_u03c3_1447_, lean_object* v_inst_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1452_, lean_object* v_inst_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1461_ = lean_st_mk_ref(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1468_){
_start:
{
lean_object* v_newEntries_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_newEntries_1469_ = lean_ctor_get(v_s_1468_, 2);
v___x_1470_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1471_ = l_List_lengthTR___redArg(v_newEntries_1469_);
v___x_1472_ = l_Nat_reprFast(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1470_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1475_);
lean_dec_ref(v_s_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1479_);
lean_dec_ref(v_x_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1483_){
_start:
{
lean_object* v_name_1485_; lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_name_1485_ = lean_ctor_get(v_descr_1483_, 0);
v___f_1486_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1487_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1483_, 4);
v___x_1488_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1488_, 0, lean_box(0));
lean_closure_set(v___x_1488_, 1, lean_box(0));
lean_closure_set(v___x_1488_, 2, lean_box(0));
lean_closure_set(v___x_1488_, 3, v_descr_1483_);
v___x_1489_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1489_, 0, lean_box(0));
lean_closure_set(v___x_1489_, 1, lean_box(0));
lean_closure_set(v___x_1489_, 2, lean_box(0));
lean_closure_set(v___x_1489_, 3, v_descr_1483_);
v___x_1490_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1490_, 0, lean_box(0));
lean_closure_set(v___x_1490_, 1, lean_box(0));
lean_closure_set(v___x_1490_, 2, lean_box(0));
lean_closure_set(v___x_1490_, 3, v_descr_1483_);
v___x_1491_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1491_, 0, lean_box(0));
lean_closure_set(v___x_1491_, 1, lean_box(0));
lean_closure_set(v___x_1491_, 2, lean_box(0));
lean_closure_set(v___x_1491_, 3, v_descr_1483_);
v___x_1492_ = lean_box(2);
v___x_1493_ = lean_box(0);
lean_inc(v_name_1485_);
v___x_1494_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1494_, 0, v_name_1485_);
lean_ctor_set(v___x_1494_, 1, v___x_1488_);
lean_ctor_set(v___x_1494_, 2, v___x_1489_);
lean_ctor_set(v___x_1494_, 3, v___x_1490_);
lean_ctor_set(v___x_1494_, 4, v___x_1491_);
lean_ctor_set(v___x_1494_, 5, v___f_1486_);
lean_ctor_set(v___x_1494_, 6, v___x_1492_);
lean_ctor_set(v___x_1494_, 7, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___f_1487_);
v___x_1496_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1509_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1501_ = l_Lean_scopedEnvExtensionsRef;
v___x_1502_ = lean_st_ref_take(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_descr_1483_);
lean_ctor_set(v___x_1503_, 1, v_a_1497_);
lean_inc_ref(v___x_1503_);
v___x_1504_ = lean_array_push(v___x_1502_, v___x_1503_);
v___x_1505_ = lean_st_ref_put(v___x_1501_, v___x_1504_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1507_ = v___x_1499_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1503_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_descr_1483_);
v_a_1510_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1496_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1496_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_00_u03c3_1523_, lean_object* v_descr_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_00_u03b2_1528_, lean_object* v_00_u03c3_1529_, lean_object* v_descr_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1527_, v_00_u03b2_1528_, v_00_u03c3_1529_, v_descr_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1533_){
_start:
{
lean_object* v_stateStack_1534_; 
v_stateStack_1534_ = lean_ctor_get(v_s_1533_, 0);
if (lean_obj_tag(v_stateStack_1534_) == 0)
{
return v_s_1533_;
}
else
{
lean_object* v_head_1535_; lean_object* v_scopedEntries_1536_; lean_object* v_newEntries_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1555_; 
lean_inc_ref(v_stateStack_1534_);
v_head_1535_ = lean_ctor_get(v_stateStack_1534_, 0);
lean_inc(v_head_1535_);
v_scopedEntries_1536_ = lean_ctor_get(v_s_1533_, 1);
v_newEntries_1537_ = lean_ctor_get(v_s_1533_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_s_1533_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_s_1533_, 0);
lean_dec(v_unused_1556_);
v___x_1539_ = v_s_1533_;
v_isShared_1540_ = v_isSharedCheck_1555_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_newEntries_1537_);
lean_inc(v_scopedEntries_1536_);
lean_dec(v_s_1533_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1555_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_state_1541_; lean_object* v_activeScopes_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1554_; 
v_state_1541_ = lean_ctor_get(v_head_1535_, 0);
v_activeScopes_1542_ = lean_ctor_get(v_head_1535_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_head_1535_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1544_ = v_head_1535_;
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_activeScopes_1542_);
lean_inc(v_state_1541_);
lean_dec(v_head_1535_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; lean_object* v___x_1548_; 
v___x_1546_ = 1;
if (v_isShared_1545_ == 0)
{
v___x_1548_ = v___x_1544_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_state_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_activeScopes_1542_);
v___x_1548_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*2, v___x_1546_);
v___x_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_stateStack_1534_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1549_);
v___x_1551_ = v___x_1539_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_scopedEntries_1536_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_newEntries_1537_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1558_, lean_object* v_env_1559_){
_start:
{
lean_object* v_ext_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_ext_1560_ = lean_ctor_get(v_ext_1558_, 1);
lean_inc_ref(v_ext_1560_);
lean_dec_ref(v_ext_1558_);
v___f_1561_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1562_ = lean_box(1);
v___x_1563_ = lean_box(0);
v___x_1564_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1560_, v_env_1559_, v___f_1561_, v___x_1562_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_00_u03c3_1567_, lean_object* v_ext_1568_, lean_object* v_env_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1568_, v_env_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1571_){
_start:
{
lean_object* v_stateStack_1572_; 
v_stateStack_1572_ = lean_ctor_get(v_s_1571_, 0);
if (lean_obj_tag(v_stateStack_1572_) == 1)
{
lean_object* v_tail_1573_; 
v_tail_1573_ = lean_ctor_get(v_stateStack_1572_, 1);
if (lean_obj_tag(v_tail_1573_) == 1)
{
lean_object* v_scopedEntries_1574_; lean_object* v_newEntries_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_inc_ref(v_tail_1573_);
v_scopedEntries_1574_ = lean_ctor_get(v_s_1571_, 1);
v_newEntries_1575_ = lean_ctor_get(v_s_1571_, 2);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_s_1571_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_s_1571_, 0);
lean_dec(v_unused_1583_);
v___x_1577_ = v_s_1571_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_newEntries_1575_);
lean_inc(v_scopedEntries_1574_);
lean_dec(v_s_1571_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_tail_1573_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_tail_1573_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_scopedEntries_1574_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_newEntries_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
return v_s_1571_;
}
}
else
{
return v_s_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1585_, lean_object* v_env_1586_){
_start:
{
lean_object* v_ext_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_ext_1587_ = lean_ctor_get(v_ext_1585_, 1);
lean_inc_ref(v_ext_1587_);
lean_dec_ref(v_ext_1585_);
v___f_1588_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1589_ = lean_box(1);
v___x_1590_ = lean_box(0);
v___x_1591_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1587_, v_env_1586_, v___f_1588_, v___x_1589_, v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1592_, lean_object* v_00_u03b2_1593_, lean_object* v_00_u03c3_1594_, lean_object* v_ext_1595_, lean_object* v_env_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1595_, v_env_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_zero_1600_; uint8_t v_isZero_1601_; 
v_zero_1600_ = lean_unsigned_to_nat(0u);
v_isZero_1601_ = lean_nat_dec_eq(v_a_1598_, v_zero_1600_);
if (v_isZero_1601_ == 1)
{
return v_a_1599_;
}
else
{
if (lean_obj_tag(v_a_1599_) == 0)
{
return v_a_1599_;
}
else
{
lean_object* v_head_1602_; lean_object* v_tail_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1622_; 
v_head_1602_ = lean_ctor_get(v_a_1599_, 0);
v_tail_1603_ = lean_ctor_get(v_a_1599_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1605_ = v_a_1599_;
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_tail_1603_);
lean_inc(v_head_1602_);
lean_dec(v_a_1599_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_state_1607_; lean_object* v_activeScopes_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1621_; 
v_state_1607_ = lean_ctor_get(v_head_1602_, 0);
v_activeScopes_1608_ = lean_ctor_get(v_head_1602_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_head_1602_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1610_ = v_head_1602_;
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_activeScopes_1608_);
lean_inc(v_state_1607_);
lean_dec(v_head_1602_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_one_1612_; lean_object* v_n_1613_; lean_object* v___x_1615_; 
v_one_1612_ = lean_unsigned_to_nat(1u);
v_n_1613_ = lean_nat_sub(v_a_1598_, v_one_1612_);
if (v_isShared_1611_ == 0)
{
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_state_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_activeScopes_1608_);
v___x_1615_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*2, v_isZero_1601_);
v___x_1616_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1613_, v_tail_1603_);
lean_dec(v_n_1613_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1616_);
lean_ctor_set(v___x_1605_, 0, v___x_1615_);
v___x_1618_ = v___x_1605_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1623_, v_a_1624_);
lean_dec(v_a_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1627_, v_a_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1634_, lean_object* v_s_1635_){
_start:
{
lean_object* v_stateStack_1636_; lean_object* v_scopedEntries_1637_; lean_object* v_newEntries_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
v_stateStack_1636_ = lean_ctor_get(v_s_1635_, 0);
v_scopedEntries_1637_ = lean_ctor_get(v_s_1635_, 1);
v_newEntries_1638_ = lean_ctor_get(v_s_1635_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_s_1635_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v_s_1635_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_newEntries_1638_);
lean_inc(v_scopedEntries_1637_);
lean_inc(v_stateStack_1636_);
lean_dec(v_s_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1634_, v_stateStack_1636_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_scopedEntries_1637_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_newEntries_1638_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1647_, lean_object* v_s_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1647_, v_s_1648_);
lean_dec(v_depth_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1650_, lean_object* v_env_1651_, lean_object* v_depth_1652_){
_start:
{
lean_object* v_ext_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_ext_1653_ = lean_ctor_get(v_ext_1650_, 1);
lean_inc_ref(v_ext_1653_);
lean_dec_ref(v_ext_1650_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1654_, 0, v_depth_1652_);
v___x_1655_ = lean_box(1);
v___x_1656_ = lean_box(0);
v___x_1657_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1653_, v_env_1651_, v___f_1654_, v___x_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1658_, lean_object* v_00_u03b2_1659_, lean_object* v_00_u03c3_1660_, lean_object* v_ext_1661_, lean_object* v_env_1662_, lean_object* v_depth_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1661_, v_env_1662_, v_depth_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1665_, lean_object* v_env_1666_, lean_object* v_b_1667_){
_start:
{
lean_object* v_ext_1668_; lean_object* v_toEnvExtension_1669_; lean_object* v_asyncMode_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_ext_1668_ = lean_ctor_get(v_ext_1665_, 1);
lean_inc_ref(v_ext_1668_);
lean_dec_ref(v_ext_1665_);
v_toEnvExtension_1669_ = lean_ctor_get(v_ext_1668_, 0);
v_asyncMode_1670_ = lean_ctor_get(v_toEnvExtension_1669_, 2);
lean_inc(v_asyncMode_1670_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_b_1667_);
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1668_, v_env_1666_, v___x_1671_, v_asyncMode_1670_, v___x_1672_);
lean_dec(v_asyncMode_1670_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1674_, lean_object* v_00_u03b2_1675_, lean_object* v_00_u03c3_1676_, lean_object* v_ext_1677_, lean_object* v_env_1678_, lean_object* v_b_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1677_, v_env_1678_, v_b_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1681_, lean_object* v_env_1682_, lean_object* v_namespaceName_1683_, lean_object* v_b_1684_){
_start:
{
lean_object* v_ext_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1696_; 
v_ext_1685_ = lean_ctor_get(v_ext_1681_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_ext_1681_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_ext_1681_, 0);
lean_dec(v_unused_1697_);
v___x_1687_ = v_ext_1681_;
v_isShared_1688_ = v_isSharedCheck_1696_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_ext_1685_);
lean_dec(v_ext_1681_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1696_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_toEnvExtension_1689_; lean_object* v_asyncMode_1690_; lean_object* v___x_1692_; 
v_toEnvExtension_1689_ = lean_ctor_get(v_ext_1685_, 0);
v_asyncMode_1690_ = lean_ctor_get(v_toEnvExtension_1689_, 2);
lean_inc(v_asyncMode_1690_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
lean_ctor_set(v___x_1687_, 1, v_b_1684_);
lean_ctor_set(v___x_1687_, 0, v_namespaceName_1683_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_namespaceName_1683_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_b_1684_);
v___x_1692_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1685_, v_env_1682_, v___x_1692_, v_asyncMode_1690_, v___x_1693_);
lean_dec(v_asyncMode_1690_);
return v___x_1694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1698_, lean_object* v_00_u03b2_1699_, lean_object* v_00_u03c3_1700_, lean_object* v_ext_1701_, lean_object* v_env_1702_, lean_object* v_namespaceName_1703_, lean_object* v_b_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1701_, v_env_1702_, v_namespaceName_1703_, v_b_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1706_, lean_object* v_states_1707_, lean_object* v_b_1708_){
_start:
{
if (lean_obj_tag(v_states_1707_) == 0)
{
lean_dec(v_b_1708_);
lean_dec_ref(v_ext_1706_);
return v_states_1707_;
}
else
{
lean_object* v_descr_1709_; lean_object* v_head_1710_; lean_object* v_tail_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1734_; 
v_descr_1709_ = lean_ctor_get(v_ext_1706_, 0);
v_head_1710_ = lean_ctor_get(v_states_1707_, 0);
v_tail_1711_ = lean_ctor_get(v_states_1707_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_states_1707_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1713_ = v_states_1707_;
v_isShared_1714_ = v_isSharedCheck_1734_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_tail_1711_);
lean_inc(v_head_1710_);
lean_dec(v_states_1707_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1734_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_addEntry_1715_; lean_object* v_state_1716_; lean_object* v_activeScopes_1717_; uint8_t v_delimitsLocal_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1733_; 
v_addEntry_1715_ = lean_ctor_get(v_descr_1709_, 4);
v_state_1716_ = lean_ctor_get(v_head_1710_, 0);
v_activeScopes_1717_ = lean_ctor_get(v_head_1710_, 1);
v_delimitsLocal_1718_ = lean_ctor_get_uint8(v_head_1710_, sizeof(void*)*2);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_head_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1720_ = v_head_1710_;
v_isShared_1721_ = v_isSharedCheck_1733_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_activeScopes_1717_);
lean_inc(v_state_1716_);
lean_dec(v_head_1710_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1733_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v_top_1724_; 
lean_inc(v_addEntry_1715_);
lean_inc(v_b_1708_);
v___x_1722_ = lean_apply_2(v_addEntry_1715_, v_state_1716_, v_b_1708_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v_top_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_activeScopes_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*2, v_delimitsLocal_1718_);
v_top_1724_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
if (v_delimitsLocal_1718_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = l_Lean_stateStackModify___redArg(v_ext_1706_, v_tail_1711_, v_b_1708_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1725_);
lean_ctor_set(v___x_1713_, 0, v_top_1724_);
v___x_1727_ = v___x_1713_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_top_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
else
{
lean_object* v___x_1730_; 
lean_dec(v_b_1708_);
lean_dec_ref(v_ext_1706_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v_top_1724_);
v___x_1730_ = v___x_1713_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_top_1724_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_tail_1711_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_00_u03c3_1737_, lean_object* v_ext_1738_, lean_object* v_states_1739_, lean_object* v_b_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_stateStackModify___redArg(v_ext_1738_, v_states_1739_, v_b_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1742_, lean_object* v_b_1743_, lean_object* v_s_1744_){
_start:
{
lean_object* v_stateStack_1745_; lean_object* v_scopedEntries_1746_; lean_object* v_newEntries_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_stateStack_1745_ = lean_ctor_get(v_s_1744_, 0);
v_scopedEntries_1746_ = lean_ctor_get(v_s_1744_, 1);
v_newEntries_1747_ = lean_ctor_get(v_s_1744_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_s_1744_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v_s_1744_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_newEntries_1747_);
lean_inc(v_scopedEntries_1746_);
lean_inc(v_stateStack_1745_);
lean_dec(v_s_1744_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = l_Lean_stateStackModify___redArg(v_ext_1742_, v_stateStack_1745_, v_b_1743_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_scopedEntries_1746_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_newEntries_1747_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1756_, lean_object* v_env_1757_, lean_object* v_b_1758_){
_start:
{
lean_object* v_ext_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_ext_1759_ = lean_ctor_get(v_ext_1756_, 1);
lean_inc_ref(v_ext_1759_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1760_, 0, v_ext_1756_);
lean_closure_set(v___f_1760_, 1, v_b_1758_);
v___x_1761_ = lean_box(1);
v___x_1762_ = lean_box(0);
v___x_1763_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1759_, v_env_1757_, v___f_1760_, v___x_1761_, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_00_u03c3_1766_, lean_object* v_ext_1767_, lean_object* v_env_1768_, lean_object* v_b_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1767_, v_env_1768_, v_b_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1771_, lean_object* v_ext_1772_, lean_object* v_b_1773_, uint8_t v_kind_1774_, lean_object* v_namespaceName_1775_){
_start:
{
switch(v_kind_1774_)
{
case 0:
{
lean_object* v___x_1776_; 
lean_dec(v_namespaceName_1775_);
v___x_1776_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1772_, v_env_1771_, v_b_1773_);
return v___x_1776_;
}
case 1:
{
lean_object* v___x_1777_; 
lean_dec(v_namespaceName_1775_);
v___x_1777_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1772_, v_env_1771_, v_b_1773_);
return v___x_1777_;
}
default: 
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1772_, v_env_1771_, v_namespaceName_1775_, v_b_1773_);
return v___x_1778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1779_, lean_object* v_ext_1780_, lean_object* v_b_1781_, lean_object* v_kind_1782_, lean_object* v_namespaceName_1783_){
_start:
{
uint8_t v_kind_boxed_1784_; lean_object* v_res_1785_; 
v_kind_boxed_1784_ = lean_unbox(v_kind_1782_);
v_res_1785_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1779_, v_ext_1780_, v_b_1781_, v_kind_boxed_1784_, v_namespaceName_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_00_u03c3_1788_, lean_object* v_env_1789_, lean_object* v_ext_1790_, lean_object* v_b_1791_, uint8_t v_kind_1792_, lean_object* v_namespaceName_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1789_, v_ext_1790_, v_b_1791_, v_kind_1792_, v_namespaceName_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_00_u03c3_1797_, lean_object* v_env_1798_, lean_object* v_ext_1799_, lean_object* v_b_1800_, lean_object* v_kind_1801_, lean_object* v_namespaceName_1802_){
_start:
{
uint8_t v_kind_boxed_1803_; lean_object* v_res_1804_; 
v_kind_boxed_1803_ = lean_unbox(v_kind_1801_);
v_res_1804_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1795_, v_00_u03b2_1796_, v_00_u03c3_1797_, v_env_1798_, v_ext_1799_, v_b_1800_, v_kind_boxed_1803_, v_namespaceName_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1805_, lean_object* v_b_1806_, uint8_t v_kind_1807_, lean_object* v_ns_1808_, lean_object* v_x_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1809_, v_ext_1805_, v_b_1806_, v_kind_1807_, v_ns_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1811_, lean_object* v_b_1812_, lean_object* v_kind_1813_, lean_object* v_ns_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v_kind_boxed_1816_; lean_object* v_res_1817_; 
v_kind_boxed_1816_ = lean_unbox(v_kind_1813_);
v_res_1817_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1811_, v_b_1812_, v_kind_boxed_1816_, v_ns_1814_, v_x_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1818_, lean_object* v_ext_1819_, lean_object* v_b_1820_, uint8_t v_kind_1821_, lean_object* v_ns_1822_){
_start:
{
lean_object* v_modifyEnv_1823_; lean_object* v___x_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; 
v_modifyEnv_1823_ = lean_ctor_get(v_inst_1818_, 1);
lean_inc(v_modifyEnv_1823_);
lean_dec_ref(v_inst_1818_);
v___x_1824_ = lean_box(v_kind_1821_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1825_, 0, v_ext_1819_);
lean_closure_set(v___f_1825_, 1, v_b_1820_);
lean_closure_set(v___f_1825_, 2, v___x_1824_);
lean_closure_set(v___f_1825_, 3, v_ns_1822_);
v___x_1826_ = lean_apply_1(v_modifyEnv_1823_, v___f_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1827_, lean_object* v_ext_1828_, lean_object* v_b_1829_, lean_object* v_kind_1830_, lean_object* v_ns_1831_){
_start:
{
uint8_t v_kind_boxed_1832_; lean_object* v_res_1833_; 
v_kind_boxed_1832_ = lean_unbox(v_kind_1830_);
v_res_1833_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1827_, v_ext_1828_, v_b_1829_, v_kind_boxed_1832_, v_ns_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_ext_1837_, lean_object* v_b_1838_, uint8_t v_kind_1839_){
_start:
{
lean_object* v_toBind_1840_; lean_object* v_getCurrNamespace_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v_toBind_1840_ = lean_ctor_get(v_inst_1834_, 1);
lean_inc(v_toBind_1840_);
lean_dec_ref(v_inst_1834_);
v_getCurrNamespace_1841_ = lean_ctor_get(v_inst_1835_, 0);
lean_inc(v_getCurrNamespace_1841_);
lean_dec_ref(v_inst_1835_);
v___x_1842_ = lean_box(v_kind_1839_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1843_, 0, v_inst_1836_);
lean_closure_set(v___f_1843_, 1, v_ext_1837_);
lean_closure_set(v___f_1843_, 2, v_b_1838_);
lean_closure_set(v___f_1843_, 3, v___x_1842_);
v___x_1844_ = lean_apply_4(v_toBind_1840_, lean_box(0), lean_box(0), v_getCurrNamespace_1841_, v___f_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_ext_1848_, lean_object* v_b_1849_, lean_object* v_kind_1850_){
_start:
{
uint8_t v_kind_boxed_1851_; lean_object* v_res_1852_; 
v_kind_boxed_1851_ = lean_unbox(v_kind_1850_);
v_res_1852_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1845_, v_inst_1846_, v_inst_1847_, v_ext_1848_, v_b_1849_, v_kind_boxed_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1853_, lean_object* v_00_u03b1_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_00_u03c3_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_ext_1860_, lean_object* v_b_1861_, uint8_t v_kind_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1857_, v_inst_1858_, v_inst_1859_, v_ext_1860_, v_b_1861_, v_kind_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1864_, lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_00_u03c3_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_ext_1871_, lean_object* v_b_1872_, lean_object* v_kind_1873_){
_start:
{
uint8_t v_kind_boxed_1874_; lean_object* v_res_1875_; 
v_kind_boxed_1874_ = lean_unbox(v_kind_1873_);
v_res_1875_ = l_Lean_ScopedEnvExtension_add(v_m_1864_, v_00_u03b1_1865_, v_00_u03b2_1866_, v_00_u03c3_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, v_ext_1871_, v_b_1872_, v_kind_boxed_1874_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1879_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1880_ = lean_unsigned_to_nat(16u);
v___x_1881_ = lean_unsigned_to_nat(209u);
v___x_1882_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1883_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1884_ = l_mkPanicMessageWithDecl(v___x_1883_, v___x_1882_, v___x_1881_, v___x_1880_, v___x_1879_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1885_, lean_object* v_ext_1886_, lean_object* v_env_1887_, lean_object* v_asyncMode_1888_){
_start:
{
lean_object* v_ext_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_stateStack_1893_; 
v_ext_1889_ = lean_ctor_get(v_ext_1886_, 1);
v___x_1890_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1891_ = lean_box(0);
v___x_1892_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1890_, v_ext_1889_, v_env_1887_, v_asyncMode_1888_, v___x_1891_);
v_stateStack_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_stateStack_1893_);
lean_dec(v___x_1892_);
if (lean_obj_tag(v_stateStack_1893_) == 1)
{
lean_object* v_head_1894_; lean_object* v_state_1895_; 
v_head_1894_ = lean_ctor_get(v_stateStack_1893_, 0);
lean_inc(v_head_1894_);
lean_dec_ref_known(v_stateStack_1893_, 2);
v_state_1895_ = lean_ctor_get(v_head_1894_, 0);
lean_inc(v_state_1895_);
lean_dec(v_head_1894_);
return v_state_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_stateStack_1893_);
v___x_1896_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1897_ = l_panic___redArg(v_inst_1885_, v___x_1896_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1898_, lean_object* v_ext_1899_, lean_object* v_env_1900_, lean_object* v_asyncMode_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1898_, v_ext_1899_, v_env_1900_, v_asyncMode_1901_);
lean_dec(v_asyncMode_1901_);
lean_dec_ref(v_ext_1899_);
lean_dec(v_inst_1898_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1903_, lean_object* v_00_u03b1_1904_, lean_object* v_00_u03b2_1905_, lean_object* v_inst_1906_, lean_object* v_ext_1907_, lean_object* v_env_1908_, lean_object* v_asyncMode_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1906_, v_ext_1907_, v_env_1908_, v_asyncMode_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1911_, lean_object* v_00_u03b1_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_inst_1914_, lean_object* v_ext_1915_, lean_object* v_env_1916_, lean_object* v_asyncMode_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1911_, v_00_u03b1_1912_, v_00_u03b2_1913_, v_inst_1914_, v_ext_1915_, v_env_1916_, v_asyncMode_1917_);
lean_dec(v_asyncMode_1917_);
lean_dec_ref(v_ext_1915_);
lean_dec(v_inst_1914_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1919_, lean_object* v_as_1920_, size_t v_sz_1921_, size_t v_i_1922_, lean_object* v_b_1923_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1922_, v_sz_1921_);
if (v___x_1924_ == 0)
{
lean_dec_ref(v_ext_1919_);
return v_b_1923_;
}
else
{
lean_object* v_descr_1925_; lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1940_; 
v_descr_1925_ = lean_ctor_get(v_ext_1919_, 0);
v_snd_1926_ = lean_ctor_get(v_b_1923_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_b_1923_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_b_1923_, 0);
lean_dec(v_unused_1941_);
v___x_1928_ = v_b_1923_;
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_dec(v_b_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_addEntry_1930_; lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v_state_1933_; lean_object* v___x_1935_; 
v_addEntry_1930_ = lean_ctor_get(v_descr_1925_, 4);
v___x_1931_ = lean_box(0);
v_a_1932_ = lean_array_uget_borrowed(v_as_1920_, v_i_1922_);
lean_inc(v_addEntry_1930_);
lean_inc(v_a_1932_);
v_state_1933_ = lean_apply_2(v_addEntry_1930_, v_snd_1926_, v_a_1932_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_state_1933_);
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1935_ = v___x_1928_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_state_1933_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
size_t v___x_1936_; size_t v___x_1937_; 
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1922_, v___x_1936_);
v_i_1922_ = v___x_1937_;
v_b_1923_ = v___x_1935_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1942_, lean_object* v_as_1943_, lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_b_1946_){
_start:
{
size_t v_sz_boxed_1947_; size_t v_i_boxed_1948_; lean_object* v_res_1949_; 
v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1942_, v_as_1943_, v_sz_boxed_1947_, v_i_boxed_1948_, v_b_1946_);
lean_dec_ref(v_as_1943_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1950_, lean_object* v_as_1951_, size_t v_sz_1952_, size_t v_i_1953_, lean_object* v_b_1954_){
_start:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_usize_dec_lt(v_i_1953_, v_sz_1952_);
if (v___x_1955_ == 0)
{
lean_dec_ref(v_ext_1950_);
return v_b_1954_;
}
else
{
lean_object* v_descr_1956_; lean_object* v_snd_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1971_; 
v_descr_1956_ = lean_ctor_get(v_ext_1950_, 0);
v_snd_1957_ = lean_ctor_get(v_b_1954_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_b_1954_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_b_1954_, 0);
lean_dec(v_unused_1972_);
v___x_1959_ = v_b_1954_;
v_isShared_1960_ = v_isSharedCheck_1971_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_snd_1957_);
lean_dec(v_b_1954_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1971_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_addEntry_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v_state_1964_; lean_object* v___x_1966_; 
v_addEntry_1961_ = lean_ctor_get(v_descr_1956_, 4);
v___x_1962_ = lean_box(0);
v_a_1963_ = lean_array_uget_borrowed(v_as_1951_, v_i_1953_);
lean_inc(v_addEntry_1961_);
lean_inc(v_a_1963_);
v_state_1964_ = lean_apply_2(v_addEntry_1961_, v_snd_1957_, v_a_1963_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v_state_1964_);
lean_ctor_set(v___x_1959_, 0, v___x_1962_);
v___x_1966_ = v___x_1959_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_state_1964_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = lean_usize_add(v_i_1953_, v___x_1967_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1950_, v_as_1951_, v_sz_1952_, v___x_1968_, v___x_1966_);
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1973_, lean_object* v_as_1974_, lean_object* v_sz_1975_, lean_object* v_i_1976_, lean_object* v_b_1977_){
_start:
{
size_t v_sz_boxed_1978_; size_t v_i_boxed_1979_; lean_object* v_res_1980_; 
v_sz_boxed_1978_ = lean_unbox_usize(v_sz_1975_);
lean_dec(v_sz_1975_);
v_i_boxed_1979_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_res_1980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1973_, v_as_1974_, v_sz_boxed_1978_, v_i_boxed_1979_, v_b_1977_);
lean_dec_ref(v_as_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1981_, lean_object* v_ext_1982_, lean_object* v_n_1983_, lean_object* v_b_1984_){
_start:
{
if (lean_obj_tag(v_n_1983_) == 0)
{
lean_object* v_cs_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; size_t v_sz_1988_; size_t v___x_1989_; lean_object* v___x_1990_; lean_object* v_fst_1991_; 
v_cs_1985_ = lean_ctor_get(v_n_1983_, 0);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v_b_1984_);
v_sz_1988_ = lean_array_size(v_cs_1985_);
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1981_, v_ext_1982_, v_cs_1985_, v_sz_1988_, v___x_1989_, v___x_1987_);
v_fst_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_fst_1991_);
if (lean_obj_tag(v_fst_1991_) == 0)
{
lean_object* v_snd_1992_; lean_object* v___x_1993_; 
v_snd_1992_ = lean_ctor_get(v___x_1990_, 1);
lean_inc(v_snd_1992_);
lean_dec_ref(v___x_1990_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_snd_1992_);
return v___x_1993_;
}
else
{
lean_object* v_val_1994_; 
lean_dec_ref(v___x_1990_);
v_val_1994_ = lean_ctor_get(v_fst_1991_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v_fst_1991_, 1);
return v_val_1994_;
}
}
else
{
lean_object* v_vs_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; size_t v_sz_1998_; size_t v___x_1999_; lean_object* v___x_2000_; lean_object* v_fst_2001_; 
v_vs_1995_ = lean_ctor_get(v_n_1983_, 0);
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_b_1984_);
v_sz_1998_ = lean_array_size(v_vs_1995_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1982_, v_vs_1995_, v_sz_1998_, v___x_1999_, v___x_1997_);
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
lean_dec_ref_known(v_fst_2001_, 1);
return v_val_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2005_, lean_object* v_ext_2006_, lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v_ext_2006_);
return v_b_2010_;
}
else
{
lean_object* v_snd_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2030_; 
v_snd_2012_ = lean_ctor_get(v_b_2010_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_b_2010_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_b_2010_, 0);
lean_dec(v_unused_2031_);
v___x_2014_ = v_b_2010_;
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2012_);
lean_dec(v_b_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
lean_inc(v_snd_2012_);
lean_inc_ref(v_ext_2006_);
v___x_2017_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2005_, v_ext_2006_, v_a_2016_, v_snd_2012_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec_ref(v_ext_2006_);
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2018_);
v___x_2020_ = v___x_2014_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_snd_2012_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
lean_dec(v_snd_2012_);
v_a_2022_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2023_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v_a_2022_);
lean_ctor_set(v___x_2014_, 0, v___x_2023_);
v___x_2025_ = v___x_2014_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_a_2022_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
size_t v___x_2026_; size_t v___x_2027_; 
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2009_, v___x_2026_);
v_i_2009_ = v___x_2027_;
v_b_2010_ = v___x_2025_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2032_, lean_object* v_ext_2033_, lean_object* v_as_2034_, lean_object* v_sz_2035_, lean_object* v_i_2036_, lean_object* v_b_2037_){
_start:
{
size_t v_sz_boxed_2038_; size_t v_i_boxed_2039_; lean_object* v_res_2040_; 
v_sz_boxed_2038_ = lean_unbox_usize(v_sz_2035_);
lean_dec(v_sz_2035_);
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2032_, v_ext_2033_, v_as_2034_, v_sz_boxed_2038_, v_i_boxed_2039_, v_b_2037_);
lean_dec_ref(v_as_2034_);
lean_dec(v_init_2032_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2041_, lean_object* v_ext_2042_, lean_object* v_n_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2041_, v_ext_2042_, v_n_2043_, v_b_2044_);
lean_dec_ref(v_n_2043_);
lean_dec(v_init_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2046_, lean_object* v_as_2047_, size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_b_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v_ext_2046_);
return v_b_2050_;
}
else
{
lean_object* v_descr_2052_; lean_object* v_snd_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2067_; 
v_descr_2052_ = lean_ctor_get(v_ext_2046_, 0);
v_snd_2053_ = lean_ctor_get(v_b_2050_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_b_2050_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v_b_2050_, 0);
lean_dec(v_unused_2068_);
v___x_2055_ = v_b_2050_;
v_isShared_2056_ = v_isSharedCheck_2067_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_snd_2053_);
lean_dec(v_b_2050_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2067_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_addEntry_2057_; lean_object* v___x_2058_; lean_object* v_a_2059_; lean_object* v_state_2060_; lean_object* v___x_2062_; 
v_addEntry_2057_ = lean_ctor_get(v_descr_2052_, 4);
v___x_2058_ = lean_box(0);
v_a_2059_ = lean_array_uget_borrowed(v_as_2047_, v_i_2049_);
lean_inc(v_addEntry_2057_);
lean_inc(v_a_2059_);
v_state_2060_ = lean_apply_2(v_addEntry_2057_, v_snd_2053_, v_a_2059_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v_state_2060_);
lean_ctor_set(v___x_2055_, 0, v___x_2058_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_state_2060_);
v___x_2062_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
size_t v___x_2063_; size_t v___x_2064_; 
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2049_, v___x_2063_);
v_i_2049_ = v___x_2064_;
v_b_2050_ = v___x_2062_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2069_, lean_object* v_as_2070_, lean_object* v_sz_2071_, lean_object* v_i_2072_, lean_object* v_b_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2071_);
lean_dec(v_sz_2071_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2072_);
lean_dec(v_i_2072_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2069_, v_as_2070_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2073_);
lean_dec_ref(v_as_2070_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v_ext_2077_);
return v_b_2081_;
}
else
{
lean_object* v_descr_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_descr_2083_ = lean_ctor_get(v_ext_2077_, 0);
v_snd_2084_ = lean_ctor_get(v_b_2081_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_b_2081_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_b_2081_, 0);
lean_dec(v_unused_2099_);
v___x_2086_ = v_b_2081_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_dec(v_b_2081_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_addEntry_2088_; lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v_state_2091_; lean_object* v___x_2093_; 
v_addEntry_2088_ = lean_ctor_get(v_descr_2083_, 4);
v___x_2089_ = lean_box(0);
v_a_2090_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
lean_inc(v_addEntry_2088_);
lean_inc(v_a_2090_);
v_state_2091_ = lean_apply_2(v_addEntry_2088_, v_snd_2084_, v_a_2090_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_state_2091_);
lean_ctor_set(v___x_2086_, 0, v___x_2089_);
v___x_2093_ = v___x_2086_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_state_2091_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_add(v_i_2080_, v___x_2094_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2077_, v_as_2078_, v_sz_2079_, v___x_2095_, v___x_2093_);
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2100_, lean_object* v_as_2101_, lean_object* v_sz_2102_, lean_object* v_i_2103_, lean_object* v_b_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2102_);
lean_dec(v_sz_2102_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2103_);
lean_dec(v_i_2103_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2100_, v_as_2101_, v_sz_boxed_2105_, v_i_boxed_2106_, v_b_2104_);
lean_dec_ref(v_as_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2108_, lean_object* v_t_2109_, lean_object* v_init_2110_){
_start:
{
lean_object* v_root_2111_; lean_object* v_tail_2112_; lean_object* v___x_2113_; 
v_root_2111_ = lean_ctor_get(v_t_2109_, 0);
v_tail_2112_ = lean_ctor_get(v_t_2109_, 1);
lean_inc_ref(v_ext_2108_);
lean_inc(v_init_2110_);
v___x_2113_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2110_, v_ext_2108_, v_root_2111_, v_init_2110_);
lean_dec(v_init_2110_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; 
lean_dec_ref(v_ext_2108_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
return v_a_2114_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v_fst_2121_; 
v_a_2115_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v_a_2115_);
v_sz_2118_ = lean_array_size(v_tail_2112_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2108_, v_tail_2112_, v_sz_2118_, v___x_2119_, v___x_2117_);
v_fst_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_fst_2121_);
if (lean_obj_tag(v_fst_2121_) == 0)
{
lean_object* v_snd_2122_; 
v_snd_2122_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_snd_2122_);
lean_dec_ref(v___x_2120_);
return v_snd_2122_;
}
else
{
lean_object* v_val_2123_; 
lean_dec_ref(v___x_2120_);
v_val_2123_ = lean_ctor_get(v_fst_2121_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v_fst_2121_, 1);
return v_val_2123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2124_, lean_object* v_t_2125_, lean_object* v_init_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2124_, v_t_2125_, v_init_2126_);
lean_dec_ref(v_t_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2128_, lean_object* v_ext_2129_, lean_object* v_s_2130_){
_start:
{
lean_object* v_stateStack_2131_; 
v_stateStack_2131_ = lean_ctor_get(v_s_2130_, 0);
lean_inc(v_stateStack_2131_);
if (lean_obj_tag(v_stateStack_2131_) == 1)
{
lean_object* v_scopedEntries_2132_; lean_object* v_newEntries_2133_; lean_object* v_head_2134_; lean_object* v_tail_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2164_; 
v_scopedEntries_2132_ = lean_ctor_get(v_s_2130_, 1);
v_newEntries_2133_ = lean_ctor_get(v_s_2130_, 2);
v_head_2134_ = lean_ctor_get(v_stateStack_2131_, 0);
v_tail_2135_ = lean_ctor_get(v_stateStack_2131_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_stateStack_2131_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2137_ = v_stateStack_2131_;
v_isShared_2138_ = v_isSharedCheck_2164_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_tail_2135_);
lean_inc(v_head_2134_);
lean_dec(v_stateStack_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2164_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___y_2140_; lean_object* v_state_2145_; lean_object* v_activeScopes_2146_; uint8_t v_delimitsLocal_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2163_; 
v_state_2145_ = lean_ctor_get(v_head_2134_, 0);
v_activeScopes_2146_ = lean_ctor_get(v_head_2134_, 1);
v_delimitsLocal_2147_ = lean_ctor_get_uint8(v_head_2134_, sizeof(void*)*2);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_head_2134_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2149_ = v_head_2134_;
v_isShared_2150_ = v_isSharedCheck_2163_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_activeScopes_2146_);
lean_inc(v_state_2145_);
lean_dec(v_head_2134_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2163_;
goto v_resetjp_2148_;
}
v___jp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___y_2140_);
v___x_2142_ = v___x_2137_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___y_2140_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_tail_2135_);
v___x_2142_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_scopedEntries_2132_);
lean_ctor_set(v___x_2143_, 2, v_newEntries_2133_);
return v___x_2143_;
}
}
v_resetjp_2148_:
{
uint8_t v___x_2151_; 
v___x_2151_ = l_Lean_NameSet_contains(v_activeScopes_2146_, v_namespaceName_2128_);
if (v___x_2151_ == 0)
{
lean_object* v_activeScopes_2152_; lean_object* v___x_2153_; 
lean_inc(v_newEntries_2133_);
lean_inc_ref(v_scopedEntries_2132_);
lean_dec_ref(v_s_2130_);
lean_inc(v_namespaceName_2128_);
v_activeScopes_2152_ = l_Lean_NameSet_insert(v_activeScopes_2146_, v_namespaceName_2128_);
v___x_2153_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2132_, v_namespaceName_2128_);
lean_dec(v_namespaceName_2128_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref(v_ext_2129_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_activeScopes_2152_);
v___x_2155_ = v___x_2149_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_state_2145_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_activeScopes_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*2, v_delimitsLocal_2147_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v___y_2140_ = v___x_2155_;
goto v___jp_2139_;
}
}
else
{
lean_object* v_val_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v_val_2157_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2158_ = 1;
v___x_2159_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2129_, v_val_2157_, v_state_2145_);
lean_dec(v_val_2157_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_activeScopes_2152_);
lean_ctor_set(v___x_2149_, 0, v___x_2159_);
v___x_2161_ = v___x_2149_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_activeScopes_2152_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*2, v___x_2158_);
v___y_2140_ = v___x_2161_;
goto v___jp_2139_;
}
}
}
else
{
lean_del_object(v___x_2149_);
lean_dec(v_activeScopes_2146_);
lean_dec(v_state_2145_);
lean_del_object(v___x_2137_);
lean_dec(v_tail_2135_);
lean_dec_ref(v_ext_2129_);
lean_dec(v_namespaceName_2128_);
return v_s_2130_;
}
}
}
}
else
{
lean_dec(v_stateStack_2131_);
lean_dec_ref(v_ext_2129_);
lean_dec(v_namespaceName_2128_);
return v_s_2130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2165_, lean_object* v_env_2166_, lean_object* v_namespaceName_2167_){
_start:
{
lean_object* v_ext_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_ext_2168_ = lean_ctor_get(v_ext_2165_, 1);
lean_inc_ref(v_ext_2168_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2169_, 0, v_namespaceName_2167_);
lean_closure_set(v___f_2169_, 1, v_ext_2165_);
v___x_2170_ = lean_box(1);
v___x_2171_ = lean_box(0);
v___x_2172_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2168_, v_env_2166_, v___f_2169_, v___x_2170_, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_00_u03c3_2175_, lean_object* v_ext_2176_, lean_object* v_env_2177_, lean_object* v_namespaceName_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2176_, v_env_2177_, v_namespaceName_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2180_, lean_object* v_00_u03c3_2181_, lean_object* v_00_u03b1_2182_, lean_object* v_ext_2183_, lean_object* v_t_2184_, lean_object* v_init_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2183_, v_t_2184_, v_init_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_00_u03c3_2188_, lean_object* v_00_u03b1_2189_, lean_object* v_ext_2190_, lean_object* v_t_2191_, lean_object* v_init_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2187_, v_00_u03c3_2188_, v_00_u03b1_2189_, v_ext_2190_, v_t_2191_, v_init_2192_);
lean_dec_ref(v_t_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2194_, lean_object* v_00_u03c3_2195_, lean_object* v_init_2196_, lean_object* v_00_u03b1_2197_, lean_object* v_ext_2198_, lean_object* v_n_2199_, lean_object* v_b_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2196_, v_ext_2198_, v_n_2199_, v_b_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2202_, lean_object* v_00_u03c3_2203_, lean_object* v_init_2204_, lean_object* v_00_u03b1_2205_, lean_object* v_ext_2206_, lean_object* v_n_2207_, lean_object* v_b_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2202_, v_00_u03c3_2203_, v_init_2204_, v_00_u03b1_2205_, v_ext_2206_, v_n_2207_, v_b_2208_);
lean_dec_ref(v_n_2207_);
lean_dec(v_init_2204_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2210_, lean_object* v_00_u03c3_2211_, lean_object* v_00_u03b1_2212_, lean_object* v_ext_2213_, lean_object* v_as_2214_, size_t v_sz_2215_, size_t v_i_2216_, lean_object* v_b_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2213_, v_as_2214_, v_sz_2215_, v_i_2216_, v_b_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_00_u03c3_2220_, lean_object* v_00_u03b1_2221_, lean_object* v_ext_2222_, lean_object* v_as_2223_, lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_b_2226_){
_start:
{
size_t v_sz_boxed_2227_; size_t v_i_boxed_2228_; lean_object* v_res_2229_; 
v_sz_boxed_2227_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2228_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2219_, v_00_u03c3_2220_, v_00_u03b1_2221_, v_ext_2222_, v_as_2223_, v_sz_boxed_2227_, v_i_boxed_2228_, v_b_2226_);
lean_dec_ref(v_as_2223_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2230_, lean_object* v_00_u03c3_2231_, lean_object* v_init_2232_, lean_object* v_00_u03b1_2233_, lean_object* v_ext_2234_, lean_object* v_as_2235_, size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_b_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2232_, v_ext_2234_, v_as_2235_, v_sz_2236_, v_i_2237_, v_b_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_00_u03c3_2241_, lean_object* v_init_2242_, lean_object* v_00_u03b1_2243_, lean_object* v_ext_2244_, lean_object* v_as_2245_, lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_b_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; lean_object* v_res_2251_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2240_, v_00_u03c3_2241_, v_init_2242_, v_00_u03b1_2243_, v_ext_2244_, v_as_2245_, v_sz_boxed_2249_, v_i_boxed_2250_, v_b_2248_);
lean_dec_ref(v_as_2245_);
lean_dec(v_init_2242_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2252_, lean_object* v_00_u03c3_2253_, lean_object* v_00_u03b1_2254_, lean_object* v_ext_2255_, lean_object* v_as_2256_, size_t v_sz_2257_, size_t v_i_2258_, lean_object* v_b_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2255_, v_as_2256_, v_sz_2257_, v_i_2258_, v_b_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2261_, lean_object* v_00_u03c3_2262_, lean_object* v_00_u03b1_2263_, lean_object* v_ext_2264_, lean_object* v_as_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_b_2268_){
_start:
{
size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2261_, v_00_u03c3_2262_, v_00_u03b1_2263_, v_ext_2264_, v_as_2265_, v_sz_boxed_2269_, v_i_boxed_2270_, v_b_2268_);
lean_dec_ref(v_as_2265_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2272_, lean_object* v_00_u03c3_2273_, lean_object* v_00_u03b1_2274_, lean_object* v_ext_2275_, lean_object* v_as_2276_, size_t v_sz_2277_, size_t v_i_2278_, lean_object* v_b_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2275_, v_as_2276_, v_sz_2277_, v_i_2278_, v_b_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2281_, lean_object* v_00_u03c3_2282_, lean_object* v_00_u03b1_2283_, lean_object* v_ext_2284_, lean_object* v_as_2285_, lean_object* v_sz_2286_, lean_object* v_i_2287_, lean_object* v_b_2288_){
_start:
{
size_t v_sz_boxed_2289_; size_t v_i_boxed_2290_; lean_object* v_res_2291_; 
v_sz_boxed_2289_ = lean_unbox_usize(v_sz_2286_);
lean_dec(v_sz_2286_);
v_i_boxed_2290_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2281_, v_00_u03c3_2282_, v_00_u03b1_2283_, v_ext_2284_, v_as_2285_, v_sz_boxed_2289_, v_i_boxed_2290_, v_b_2288_);
lean_dec_ref(v_as_2285_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2292_, lean_object* v_00_u03c3_2293_, lean_object* v_00_u03b1_2294_, lean_object* v_ext_2295_, lean_object* v_as_2296_, size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_b_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2295_, v_as_2296_, v_sz_2297_, v_i_2298_, v_b_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2301_, lean_object* v_00_u03c3_2302_, lean_object* v_00_u03b1_2303_, lean_object* v_ext_2304_, lean_object* v_as_2305_, lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_b_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2301_, v_00_u03c3_2302_, v_00_u03b1_2303_, v_ext_2304_, v_as_2305_, v_sz_boxed_2309_, v_i_boxed_2310_, v_b_2308_);
lean_dec_ref(v_as_2305_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2312_, lean_object* v_s_2313_){
_start:
{
lean_object* v_stateStack_2314_; 
v_stateStack_2314_ = lean_ctor_get(v_s_2313_, 0);
lean_inc(v_stateStack_2314_);
if (lean_obj_tag(v_stateStack_2314_) == 1)
{
lean_object* v_head_2315_; lean_object* v_scopedEntries_2316_; lean_object* v_newEntries_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2344_; 
v_head_2315_ = lean_ctor_get(v_stateStack_2314_, 0);
lean_inc(v_head_2315_);
v_scopedEntries_2316_ = lean_ctor_get(v_s_2313_, 1);
v_newEntries_2317_ = lean_ctor_get(v_s_2313_, 2);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_s_2313_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_s_2313_, 0);
lean_dec(v_unused_2345_);
v___x_2319_ = v_s_2313_;
v_isShared_2320_ = v_isSharedCheck_2344_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_newEntries_2317_);
lean_inc(v_scopedEntries_2316_);
lean_dec(v_s_2313_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2344_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_tail_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2342_; 
v_tail_2321_ = lean_ctor_get(v_stateStack_2314_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_stateStack_2314_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_stateStack_2314_, 0);
lean_dec(v_unused_2343_);
v___x_2323_ = v_stateStack_2314_;
v_isShared_2324_ = v_isSharedCheck_2342_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_tail_2321_);
lean_dec(v_stateStack_2314_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2342_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_state_2325_; lean_object* v_activeScopes_2326_; uint8_t v_delimitsLocal_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2341_; 
v_state_2325_ = lean_ctor_get(v_head_2315_, 0);
v_activeScopes_2326_ = lean_ctor_get(v_head_2315_, 1);
v_delimitsLocal_2327_ = lean_ctor_get_uint8(v_head_2315_, sizeof(void*)*2);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_head_2315_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2329_ = v_head_2315_;
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_activeScopes_2326_);
lean_inc(v_state_2325_);
lean_dec(v_head_2315_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_apply_1(v_f_2312_, v_state_2325_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_activeScopes_2326_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, sizeof(void*)*2, v_delimitsLocal_2327_);
v___x_2333_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2333_);
v___x_2335_ = v___x_2323_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_tail_2321_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2335_);
v___x_2337_ = v___x_2319_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_scopedEntries_2316_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_newEntries_2317_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2314_);
lean_dec(v_f_2312_);
return v_s_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2346_, lean_object* v_env_2347_, lean_object* v_f_2348_){
_start:
{
lean_object* v_ext_2349_; lean_object* v_toEnvExtension_2350_; lean_object* v_asyncMode_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_ext_2349_ = lean_ctor_get(v_ext_2346_, 1);
lean_inc_ref(v_ext_2349_);
lean_dec_ref(v_ext_2346_);
v_toEnvExtension_2350_ = lean_ctor_get(v_ext_2349_, 0);
v_asyncMode_2351_ = lean_ctor_get(v_toEnvExtension_2350_, 2);
lean_inc(v_asyncMode_2351_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2352_, 0, v_f_2348_);
v___x_2353_ = lean_box(0);
v___x_2354_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2349_, v_env_2347_, v___f_2352_, v_asyncMode_2351_, v___x_2353_);
lean_dec(v_asyncMode_2351_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2355_, lean_object* v_00_u03b2_2356_, lean_object* v_00_u03c3_2357_, lean_object* v_ext_2358_, lean_object* v_env_2359_, lean_object* v_f_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2358_, v_env_2359_, v_f_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2362_, lean_object* v_____s_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_apply_2(v_toPure_2362_, lean_box(0), v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2366_, lean_object* v_toPure_2367_, lean_object* v_r_2368_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2366_);
v___x_2370_ = lean_apply_2(v_toPure_2367_, lean_box(0), v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2371_, lean_object* v_toBind_2372_, lean_object* v___f_2373_, lean_object* v_a_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_modifyEnv_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_modifyEnv_2377_ = lean_ctor_get(v_inst_2371_, 1);
lean_inc(v_modifyEnv_2377_);
lean_dec_ref(v_inst_2371_);
v___x_2378_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2378_, 0, lean_box(0));
lean_closure_set(v___x_2378_, 1, lean_box(0));
lean_closure_set(v___x_2378_, 2, lean_box(0));
lean_closure_set(v___x_2378_, 3, v_a_2374_);
v___x_2379_ = lean_apply_1(v_modifyEnv_2377_, v___x_2378_);
v___x_2380_ = lean_apply_4(v_toBind_2372_, lean_box(0), lean_box(0), v___x_2379_, v___f_2373_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2381_, lean_object* v_inst_2382_, lean_object* v_toBind_2383_, lean_object* v_inst_2384_, lean_object* v___f_2385_, lean_object* v_____do__lift_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___f_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2387_ = lean_box(0);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2388_, 0, v___x_2387_);
lean_closure_set(v___f_2388_, 1, v_toPure_2381_);
lean_inc(v_toBind_2383_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2389_, 0, v_inst_2382_);
lean_closure_set(v___f_2389_, 1, v_toBind_2383_);
lean_closure_set(v___f_2389_, 2, v___f_2388_);
v_sz_2390_ = lean_array_size(v_____do__lift_2386_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2384_, v_____do__lift_2386_, v___f_2389_, v_sz_2390_, v___x_2391_, v___x_2387_);
v___x_2393_ = lean_apply_4(v_toBind_2383_, lean_box(0), lean_box(0), v___x_2392_, v___f_2385_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = l_Lean_scopedEnvExtensionsRef;
v___x_2395_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2395_, 0, lean_box(0));
lean_closure_set(v___x_2395_, 1, lean_box(0));
lean_closure_set(v___x_2395_, 2, v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_){
_start:
{
lean_object* v_toApplicative_2399_; lean_object* v_toBind_2400_; lean_object* v_toPure_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___f_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; 
v_toApplicative_2399_ = lean_ctor_get(v_inst_2396_, 0);
v_toBind_2400_ = lean_ctor_get(v_inst_2396_, 1);
lean_inc_n(v_toBind_2400_, 2);
v_toPure_2401_ = lean_ctor_get(v_toApplicative_2399_, 1);
lean_inc_n(v_toPure_2401_, 2);
v___x_2402_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2403_ = lean_apply_2(v_inst_2398_, lean_box(0), v___x_2402_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2404_, 0, v_toPure_2401_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2405_, 0, v_toPure_2401_);
lean_closure_set(v___f_2405_, 1, v_inst_2397_);
lean_closure_set(v___f_2405_, 2, v_toBind_2400_);
lean_closure_set(v___f_2405_, 3, v_inst_2396_);
lean_closure_set(v___f_2405_, 4, v___f_2404_);
v___x_2406_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v___x_2403_, v___f_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_pushScope___redArg(v_inst_2408_, v_inst_2409_, v_inst_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2412_, lean_object* v_toBind_2413_, lean_object* v___f_2414_, lean_object* v_a_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_modifyEnv_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_modifyEnv_2418_ = lean_ctor_get(v_inst_2412_, 1);
lean_inc(v_modifyEnv_2418_);
lean_dec_ref(v_inst_2412_);
v___x_2419_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2419_, 0, lean_box(0));
lean_closure_set(v___x_2419_, 1, lean_box(0));
lean_closure_set(v___x_2419_, 2, lean_box(0));
lean_closure_set(v___x_2419_, 3, v_a_2415_);
v___x_2420_ = lean_apply_1(v_modifyEnv_2418_, v___x_2419_);
v___x_2421_ = lean_apply_4(v_toBind_2413_, lean_box(0), lean_box(0), v___x_2420_, v___f_2414_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2422_, lean_object* v_inst_2423_, lean_object* v_toBind_2424_, lean_object* v_inst_2425_, lean_object* v___f_2426_, lean_object* v_____do__lift_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___f_2429_; lean_object* v___f_2430_; size_t v_sz_2431_; size_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2428_ = lean_box(0);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2429_, 0, v___x_2428_);
lean_closure_set(v___f_2429_, 1, v_toPure_2422_);
lean_inc(v_toBind_2424_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2430_, 0, v_inst_2423_);
lean_closure_set(v___f_2430_, 1, v_toBind_2424_);
lean_closure_set(v___f_2430_, 2, v___f_2429_);
v_sz_2431_ = lean_array_size(v_____do__lift_2427_);
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2425_, v_____do__lift_2427_, v___f_2430_, v_sz_2431_, v___x_2432_, v___x_2428_);
v___x_2434_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v___x_2433_, v___f_2426_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_){
_start:
{
lean_object* v_toApplicative_2438_; lean_object* v_toBind_2439_; lean_object* v_toPure_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; 
v_toApplicative_2438_ = lean_ctor_get(v_inst_2435_, 0);
v_toBind_2439_ = lean_ctor_get(v_inst_2435_, 1);
lean_inc_n(v_toBind_2439_, 2);
v_toPure_2440_ = lean_ctor_get(v_toApplicative_2438_, 1);
lean_inc_n(v_toPure_2440_, 2);
v___x_2441_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2442_ = lean_apply_2(v_inst_2437_, lean_box(0), v___x_2441_);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2443_, 0, v_toPure_2440_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2444_, 0, v_toPure_2440_);
lean_closure_set(v___f_2444_, 1, v_inst_2436_);
lean_closure_set(v___f_2444_, 2, v_toBind_2439_);
lean_closure_set(v___f_2444_, 3, v_inst_2435_);
lean_closure_set(v___f_2444_, 4, v___f_2443_);
v___x_2445_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2442_, v___f_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_popScope___redArg(v_inst_2447_, v_inst_2448_, v_inst_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2451_, lean_object* v_depth_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2451_, v_x_2453_, v_depth_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2455_, lean_object* v_depth_2456_, lean_object* v_toBind_2457_, lean_object* v___f_2458_, lean_object* v_a_2459_, lean_object* v_x_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_modifyEnv_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_modifyEnv_2462_ = lean_ctor_get(v_inst_2455_, 1);
lean_inc(v_modifyEnv_2462_);
lean_dec_ref(v_inst_2455_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2463_, 0, v_a_2459_);
lean_closure_set(v___f_2463_, 1, v_depth_2456_);
v___x_2464_ = lean_apply_1(v_modifyEnv_2462_, v___f_2463_);
v___x_2465_ = lean_apply_4(v_toBind_2457_, lean_box(0), lean_box(0), v___x_2464_, v___f_2458_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2466_, lean_object* v_inst_2467_, lean_object* v_depth_2468_, lean_object* v_toBind_2469_, lean_object* v_inst_2470_, lean_object* v___f_2471_, lean_object* v_____do__lift_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; size_t v_sz_2476_; size_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2473_ = lean_box(0);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2474_, 0, v___x_2473_);
lean_closure_set(v___f_2474_, 1, v_toPure_2466_);
lean_inc(v_toBind_2469_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2475_, 0, v_inst_2467_);
lean_closure_set(v___f_2475_, 1, v_depth_2468_);
lean_closure_set(v___f_2475_, 2, v_toBind_2469_);
lean_closure_set(v___f_2475_, 3, v___f_2474_);
v_sz_2476_ = lean_array_size(v_____do__lift_2472_);
v___x_2477_ = ((size_t)0ULL);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2470_, v_____do__lift_2472_, v___f_2475_, v_sz_2476_, v___x_2477_, v___x_2473_);
v___x_2479_ = lean_apply_4(v_toBind_2469_, lean_box(0), lean_box(0), v___x_2478_, v___f_2471_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_depth_2483_){
_start:
{
lean_object* v_toApplicative_2484_; lean_object* v_toBind_2485_; lean_object* v_toPure_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
v_toApplicative_2484_ = lean_ctor_get(v_inst_2480_, 0);
v_toBind_2485_ = lean_ctor_get(v_inst_2480_, 1);
lean_inc_n(v_toBind_2485_, 2);
v_toPure_2486_ = lean_ctor_get(v_toApplicative_2484_, 1);
lean_inc_n(v_toPure_2486_, 2);
v___x_2487_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2488_ = lean_apply_2(v_inst_2482_, lean_box(0), v___x_2487_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2489_, 0, v_toPure_2486_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2490_, 0, v_toPure_2486_);
lean_closure_set(v___f_2490_, 1, v_inst_2481_);
lean_closure_set(v___f_2490_, 2, v_depth_2483_);
lean_closure_set(v___f_2490_, 3, v_toBind_2485_);
lean_closure_set(v___f_2490_, 4, v_inst_2480_);
lean_closure_set(v___f_2490_, 5, v___f_2489_);
v___x_2491_ = lean_apply_4(v_toBind_2485_, lean_box(0), lean_box(0), v___x_2488_, v___f_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_depth_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_setDelimitsLocal___redArg(v_inst_2493_, v_inst_2494_, v_inst_2495_, v_depth_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2498_, lean_object* v_namespaceName_2499_, lean_object* v_x_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2498_, v_x_2500_, v_namespaceName_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2502_, lean_object* v_namespaceName_2503_, lean_object* v_toBind_2504_, lean_object* v___f_2505_, lean_object* v_a_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_modifyEnv_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_modifyEnv_2509_ = lean_ctor_get(v_inst_2502_, 1);
lean_inc(v_modifyEnv_2509_);
lean_dec_ref(v_inst_2502_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2510_, 0, v_a_2506_);
lean_closure_set(v___f_2510_, 1, v_namespaceName_2503_);
v___x_2511_ = lean_apply_1(v_modifyEnv_2509_, v___f_2510_);
v___x_2512_ = lean_apply_4(v_toBind_2504_, lean_box(0), lean_box(0), v___x_2511_, v___f_2505_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2513_, lean_object* v_inst_2514_, lean_object* v_namespaceName_2515_, lean_object* v_toBind_2516_, lean_object* v_inst_2517_, lean_object* v___f_2518_, lean_object* v_____do__lift_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; size_t v_sz_2523_; size_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2520_ = lean_box(0);
v___f_2521_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
lean_closure_set(v___f_2521_, 1, v_toPure_2513_);
lean_inc(v_toBind_2516_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2522_, 0, v_inst_2514_);
lean_closure_set(v___f_2522_, 1, v_namespaceName_2515_);
lean_closure_set(v___f_2522_, 2, v_toBind_2516_);
lean_closure_set(v___f_2522_, 3, v___f_2521_);
v_sz_2523_ = lean_array_size(v_____do__lift_2519_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2517_, v_____do__lift_2519_, v___f_2522_, v_sz_2523_, v___x_2524_, v___x_2520_);
v___x_2526_ = lean_apply_4(v_toBind_2516_, lean_box(0), lean_box(0), v___x_2525_, v___f_2518_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_namespaceName_2530_){
_start:
{
lean_object* v_toApplicative_2531_; lean_object* v_toBind_2532_; lean_object* v_toPure_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; 
v_toApplicative_2531_ = lean_ctor_get(v_inst_2527_, 0);
v_toBind_2532_ = lean_ctor_get(v_inst_2527_, 1);
lean_inc_n(v_toBind_2532_, 2);
v_toPure_2533_ = lean_ctor_get(v_toApplicative_2531_, 1);
lean_inc_n(v_toPure_2533_, 2);
v___x_2534_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2535_ = lean_apply_2(v_inst_2529_, lean_box(0), v___x_2534_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2536_, 0, v_toPure_2533_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2537_, 0, v_toPure_2533_);
lean_closure_set(v___f_2537_, 1, v_inst_2528_);
lean_closure_set(v___f_2537_, 2, v_namespaceName_2530_);
lean_closure_set(v___f_2537_, 3, v_toBind_2532_);
lean_closure_set(v___f_2537_, 4, v_inst_2527_);
lean_closure_set(v___f_2537_, 5, v___f_2536_);
v___x_2538_ = lean_apply_4(v_toBind_2532_, lean_box(0), lean_box(0), v___x_2535_, v___f_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_namespaceName_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_activateScoped___redArg(v_inst_2540_, v_inst_2541_, v_inst_2542_, v_namespaceName_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2546_){
_start:
{
lean_inc(v___y_2546_);
return v___y_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2547_);
lean_dec(v___y_2547_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2549_, lean_object* v_a_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2550_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2554_, lean_object* v_a_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2554_, v_a_2555_, v___y_2556_);
lean_dec_ref(v___y_2556_);
lean_dec(v_x_2554_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_initial_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2562_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2567_){
_start:
{
lean_object* v_name_2569_; lean_object* v_addEntry_2570_; lean_object* v_initial_2571_; lean_object* v_finalizeImport_2572_; lean_object* v_exportEntry_x3f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_name_2569_ = lean_ctor_get(v_descr_2567_, 0);
lean_inc(v_name_2569_);
v_addEntry_2570_ = lean_ctor_get(v_descr_2567_, 1);
lean_inc(v_addEntry_2570_);
v_initial_2571_ = lean_ctor_get(v_descr_2567_, 2);
lean_inc(v_initial_2571_);
v_finalizeImport_2572_ = lean_ctor_get(v_descr_2567_, 3);
lean_inc(v_finalizeImport_2572_);
v_exportEntry_x3f_2573_ = lean_ctor_get(v_descr_2567_, 4);
lean_inc_ref(v_exportEntry_x3f_2573_);
lean_dec_ref(v_descr_2567_);
v___f_2574_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2575_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2576_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2576_, 0, v_initial_2571_);
v___x_2577_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2577_, 0, v_name_2569_);
lean_ctor_set(v___x_2577_, 1, v___f_2576_);
lean_ctor_set(v___x_2577_, 2, v___f_2575_);
lean_ctor_set(v___x_2577_, 3, v___f_2574_);
lean_ctor_set(v___x_2577_, 4, v_addEntry_2570_);
lean_ctor_set(v___x_2577_, 5, v_finalizeImport_2572_);
lean_ctor_set(v___x_2577_, 6, v_exportEntry_x3f_2573_);
v___x_2578_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03c3_2583_, lean_object* v_descr_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2584_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2587_, lean_object* v_00_u03c3_2588_, lean_object* v_descr_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2587_, v_00_u03c3_2588_, v_descr_2589_);
return v_res_2591_;
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
