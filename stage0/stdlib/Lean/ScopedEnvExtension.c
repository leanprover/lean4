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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_308_, size_t v_x_309_, lean_object* v_x_310_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_es_311_; lean_object* v___x_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v_j_315_; lean_object* v___x_316_; 
v_es_311_ = lean_ctor_get(v_x_308_, 0);
v___x_312_ = lean_box(2);
v___x_313_ = ((size_t)31ULL);
v___x_314_ = lean_usize_land(v_x_309_, v___x_313_);
v_j_315_ = lean_usize_to_nat(v___x_314_);
v___x_316_ = lean_array_get_borrowed(v___x_312_, v_es_311_, v_j_315_);
lean_dec(v_j_315_);
switch(lean_obj_tag(v___x_316_))
{
case 0:
{
lean_object* v_key_317_; lean_object* v_val_318_; uint8_t v___x_319_; 
v_key_317_ = lean_ctor_get(v___x_316_, 0);
v_val_318_ = lean_ctor_get(v___x_316_, 1);
v___x_319_ = lean_name_eq(v_x_310_, v_key_317_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
else
{
lean_object* v___x_321_; 
lean_inc(v_val_318_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_val_318_);
return v___x_321_;
}
}
case 1:
{
lean_object* v_node_322_; size_t v___x_323_; size_t v___x_324_; 
v_node_322_ = lean_ctor_get(v___x_316_, 0);
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_usize_shift_right(v_x_309_, v___x_323_);
v_x_308_ = v_node_322_;
v_x_309_ = v___x_324_;
goto _start;
}
default: 
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
return v___x_326_;
}
}
}
else
{
lean_object* v_ks_327_; lean_object* v_vs_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_ks_327_ = lean_ctor_get(v_x_308_, 0);
v_vs_328_ = lean_ctor_get(v_x_308_, 1);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_327_, v_vs_328_, v___x_329_, v_x_310_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
size_t v_x_1058__boxed_334_; lean_object* v_res_335_; 
v_x_1058__boxed_334_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_res_335_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_331_, v_x_1058__boxed_334_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_x_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint64_t v___y_339_; 
if (lean_obj_tag(v_x_337_) == 0)
{
uint64_t v___x_342_; 
v___x_342_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_339_ = v___x_342_;
goto v___jp_338_;
}
else
{
uint64_t v_hash_343_; 
v_hash_343_ = lean_ctor_get_uint64(v_x_337_, sizeof(void*)*2);
v___y_339_ = v_hash_343_;
goto v___jp_338_;
}
v___jp_338_:
{
size_t v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_uint64_to_usize(v___y_339_);
v___x_341_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_336_, v___x_340_, v_x_337_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_x_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_stage_u2081_349_; 
v_stage_u2081_349_ = lean_ctor_get_uint8(v_x_347_, sizeof(void*)*2);
if (v_stage_u2081_349_ == 0)
{
lean_object* v_map_u2081_350_; lean_object* v_map_u2082_351_; lean_object* v___x_352_; 
v_map_u2081_350_ = lean_ctor_get(v_x_347_, 0);
v_map_u2082_351_ = lean_ctor_get(v_x_347_, 1);
v___x_352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_351_, v_x_348_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_350_, v_x_348_);
return v___x_353_;
}
else
{
return v___x_352_;
}
}
else
{
lean_object* v_map_u2081_354_; lean_object* v___x_355_; 
v_map_u2081_354_ = lean_ctor_get(v_x_347_, 0);
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_354_, v_x_348_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec_ref(v_x_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_359_, lean_object* v_b_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_dec(v_b_360_);
lean_dec(v_a_359_);
return v_x_361_;
}
else
{
lean_object* v_key_362_; lean_object* v_value_363_; lean_object* v_tail_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_376_; 
v_key_362_ = lean_ctor_get(v_x_361_, 0);
v_value_363_ = lean_ctor_get(v_x_361_, 1);
v_tail_364_ = lean_ctor_get(v_x_361_, 2);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_376_ == 0)
{
v___x_366_ = v_x_361_;
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_tail_364_);
lean_inc(v_value_363_);
lean_inc(v_key_362_);
lean_dec(v_x_361_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_376_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; 
v___x_368_ = lean_name_eq(v_key_362_, v_a_359_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_359_, v_b_360_, v_tail_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 2, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_key_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_value_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v___x_374_; 
lean_dec(v_value_363_);
lean_dec(v_key_362_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_b_360_);
lean_ctor_set(v___x_366_, 0, v_a_359_);
v___x_374_ = v___x_366_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_359_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_b_360_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_tail_364_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
return v_x_377_;
}
else
{
lean_object* v_key_379_; lean_object* v_value_380_; lean_object* v_tail_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_407_; 
v_key_379_ = lean_ctor_get(v_x_378_, 0);
v_value_380_ = lean_ctor_get(v_x_378_, 1);
v_tail_381_ = lean_ctor_get(v_x_378_, 2);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_407_ == 0)
{
v___x_383_ = v_x_378_;
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_tail_381_);
lean_inc(v_value_380_);
lean_inc(v_key_379_);
lean_dec(v_x_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; uint64_t v___y_387_; 
v___x_385_ = lean_array_get_size(v_x_377_);
if (lean_obj_tag(v_key_379_) == 0)
{
uint64_t v___x_405_; 
v___x_405_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_387_ = v___x_405_;
goto v___jp_386_;
}
else
{
uint64_t v_hash_406_; 
v_hash_406_ = lean_ctor_get_uint64(v_key_379_, sizeof(void*)*2);
v___y_387_ = v_hash_406_;
goto v___jp_386_;
}
v___jp_386_:
{
uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v_fold_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_388_ = 32ULL;
v___x_389_ = lean_uint64_shift_right(v___y_387_, v___x_388_);
v_fold_390_ = lean_uint64_xor(v___y_387_, v___x_389_);
v___x_391_ = 16ULL;
v___x_392_ = lean_uint64_shift_right(v_fold_390_, v___x_391_);
v___x_393_ = lean_uint64_xor(v_fold_390_, v___x_392_);
v___x_394_ = lean_uint64_to_usize(v___x_393_);
v___x_395_ = lean_usize_of_nat(v___x_385_);
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_sub(v___x_395_, v___x_396_);
v___x_398_ = lean_usize_land(v___x_394_, v___x_397_);
v___x_399_ = lean_array_uget_borrowed(v_x_377_, v___x_398_);
lean_inc(v___x_399_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 2, v___x_399_);
v___x_401_ = v___x_383_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_key_379_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_value_380_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_399_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; 
v___x_402_ = lean_array_uset(v_x_377_, v___x_398_, v___x_401_);
v_x_377_ = v___x_402_;
v_x_378_ = v_tail_381_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_408_, lean_object* v_source_409_, lean_object* v_target_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_source_409_);
v___x_412_ = lean_nat_dec_lt(v_i_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_source_409_);
lean_dec(v_i_408_);
return v_target_410_;
}
else
{
lean_object* v_es_413_; lean_object* v___x_414_; lean_object* v_source_415_; lean_object* v_target_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_es_413_ = lean_array_fget(v_source_409_, v_i_408_);
v___x_414_ = lean_box(0);
v_source_415_ = lean_array_fset(v_source_409_, v_i_408_, v___x_414_);
v_target_416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_410_, v_es_413_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_i_408_, v___x_417_);
lean_dec(v_i_408_);
v_i_408_ = v___x_418_;
v_source_409_ = v_source_415_;
v_target_410_ = v_target_416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_nbuckets_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = lean_array_get_size(v_data_420_);
v___x_422_ = lean_unsigned_to_nat(2u);
v_nbuckets_423_ = lean_nat_mul(v___x_421_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_box(0);
v___x_426_ = lean_mk_array(v_nbuckets_423_, v___x_425_);
v___x_427_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_424_, v_data_420_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_name_eq(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_439_, lean_object* v_a_440_, lean_object* v_b_441_){
_start:
{
lean_object* v_size_442_; lean_object* v_buckets_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_489_; 
v_size_442_ = lean_ctor_get(v_m_439_, 0);
v_buckets_443_ = lean_ctor_get(v_m_439_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_m_439_);
if (v_isSharedCheck_489_ == 0)
{
v___x_445_ = v_m_439_;
v_isShared_446_ = v_isSharedCheck_489_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_buckets_443_);
lean_inc(v_size_442_);
lean_dec(v_m_439_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_489_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; uint64_t v___y_449_; 
v___x_447_ = lean_array_get_size(v_buckets_443_);
if (lean_obj_tag(v_a_440_) == 0)
{
uint64_t v___x_487_; 
v___x_487_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_449_ = v___x_487_;
goto v___jp_448_;
}
else
{
uint64_t v_hash_488_; 
v_hash_488_ = lean_ctor_get_uint64(v_a_440_, sizeof(void*)*2);
v___y_449_ = v_hash_488_;
goto v___jp_448_;
}
v___jp_448_:
{
uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v_fold_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v_bkt_461_; uint8_t v___x_462_; 
v___x_450_ = 32ULL;
v___x_451_ = lean_uint64_shift_right(v___y_449_, v___x_450_);
v_fold_452_ = lean_uint64_xor(v___y_449_, v___x_451_);
v___x_453_ = 16ULL;
v___x_454_ = lean_uint64_shift_right(v_fold_452_, v___x_453_);
v___x_455_ = lean_uint64_xor(v_fold_452_, v___x_454_);
v___x_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = lean_usize_of_nat(v___x_447_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_sub(v___x_457_, v___x_458_);
v___x_460_ = lean_usize_land(v___x_456_, v___x_459_);
v_bkt_461_ = lean_array_uget_borrowed(v_buckets_443_, v___x_460_);
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_440_, v_bkt_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v_size_x27_464_; lean_object* v___x_465_; lean_object* v_buckets_x27_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v_size_x27_464_ = lean_nat_add(v_size_442_, v___x_463_);
lean_dec(v_size_442_);
lean_inc(v_bkt_461_);
v___x_465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_465_, 0, v_a_440_);
lean_ctor_set(v___x_465_, 1, v_b_441_);
lean_ctor_set(v___x_465_, 2, v_bkt_461_);
v_buckets_x27_466_ = lean_array_uset(v_buckets_443_, v___x_460_, v___x_465_);
v___x_467_ = lean_unsigned_to_nat(4u);
v___x_468_ = lean_nat_mul(v_size_x27_464_, v___x_467_);
v___x_469_ = lean_unsigned_to_nat(3u);
v___x_470_ = lean_nat_div(v___x_468_, v___x_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_array_get_size(v_buckets_x27_466_);
v___x_472_ = lean_nat_dec_le(v___x_470_, v___x_471_);
lean_dec(v___x_470_);
if (v___x_472_ == 0)
{
lean_object* v_val_473_; lean_object* v___x_475_; 
v_val_473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_466_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_val_473_);
lean_ctor_set(v___x_445_, 0, v_size_x27_464_);
v___x_475_ = v___x_445_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_x27_464_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_val_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_478_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_buckets_x27_466_);
lean_ctor_set(v___x_445_, 0, v_size_x27_464_);
v___x_478_ = v___x_445_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_size_x27_464_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_buckets_x27_466_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
else
{
lean_object* v___x_480_; lean_object* v_buckets_x27_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc(v_bkt_461_);
v___x_480_ = lean_box(0);
v_buckets_x27_481_ = lean_array_uset(v_buckets_443_, v___x_460_, v___x_480_);
v___x_482_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_440_, v_b_441_, v_bkt_461_);
v___x_483_ = lean_array_uset(v_buckets_x27_481_, v___x_460_, v___x_482_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_483_);
v___x_485_ = v___x_445_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_size_442_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_ks_494_; lean_object* v_vs_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_519_; 
v_ks_494_ = lean_ctor_get(v_x_490_, 0);
v_vs_495_ = lean_ctor_get(v_x_490_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_490_);
if (v_isSharedCheck_519_ == 0)
{
v___x_497_ = v_x_490_;
v_isShared_498_ = v_isSharedCheck_519_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_vs_495_);
lean_inc(v_ks_494_);
lean_dec(v_x_490_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_519_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_get_size(v_ks_494_);
v___x_500_ = lean_nat_dec_lt(v_x_491_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec(v_x_491_);
v___x_501_ = lean_array_push(v_ks_494_, v_x_492_);
v___x_502_ = lean_array_push(v_vs_495_, v_x_493_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_502_);
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_504_ = v___x_497_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
else
{
lean_object* v_k_x27_506_; uint8_t v___x_507_; 
v_k_x27_506_ = lean_array_fget_borrowed(v_ks_494_, v_x_491_);
v___x_507_ = lean_name_eq(v_x_492_, v_k_x27_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_509_; 
if (v_isShared_498_ == 0)
{
v___x_509_ = v___x_497_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_ks_494_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_vs_495_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v_x_491_, v___x_510_);
lean_dec(v_x_491_);
v_x_490_ = v___x_509_;
v_x_491_ = v___x_511_;
goto _start;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_array_fset(v_ks_494_, v_x_491_, v_x_492_);
v___x_515_ = lean_array_fset(v_vs_495_, v_x_491_, v_x_493_);
lean_dec(v_x_491_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_515_);
lean_ctor_set(v___x_497_, 0, v___x_514_);
v___x_517_ = v___x_497_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_520_, lean_object* v_k_521_, lean_object* v_v_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_520_, v___x_523_, v_k_521_, v_v_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_526_, size_t v_x_527_, size_t v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_es_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v_j_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_es_531_ = lean_ctor_get(v_x_526_, 0);
v___x_532_ = ((size_t)31ULL);
v___x_533_ = lean_usize_land(v_x_527_, v___x_532_);
v_j_534_ = lean_usize_to_nat(v___x_533_);
v___x_535_ = lean_array_get_size(v_es_531_);
v___x_536_ = lean_nat_dec_lt(v_j_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec(v_j_534_);
lean_dec(v_x_530_);
lean_dec(v_x_529_);
return v_x_526_;
}
else
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_575_; 
lean_inc_ref(v_es_531_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_x_526_, 0);
lean_dec(v_unused_576_);
v___x_538_ = v_x_526_;
v_isShared_539_ = v_isSharedCheck_575_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_x_526_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_575_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_v_540_; lean_object* v___x_541_; lean_object* v_xs_x27_542_; lean_object* v___y_544_; 
v_v_540_ = lean_array_fget(v_es_531_, v_j_534_);
v___x_541_ = lean_box(0);
v_xs_x27_542_ = lean_array_fset(v_es_531_, v_j_534_, v___x_541_);
switch(lean_obj_tag(v_v_540_))
{
case 0:
{
lean_object* v_key_549_; lean_object* v_val_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v_key_549_ = lean_ctor_get(v_v_540_, 0);
v_val_550_ = lean_ctor_get(v_v_540_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_v_540_);
if (v_isSharedCheck_560_ == 0)
{
v___x_552_ = v_v_540_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_val_550_);
lean_inc(v_key_549_);
lean_dec(v_v_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_name_eq(v_x_529_, v_key_549_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_del_object(v___x_552_);
v___x_555_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_549_, v_val_550_, v_x_529_, v_x_530_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___y_544_ = v___x_556_;
goto v___jp_543_;
}
else
{
lean_object* v___x_558_; 
lean_dec(v_val_550_);
lean_dec(v_key_549_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_x_530_);
lean_ctor_set(v___x_552_, 0, v_x_529_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_x_529_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_x_530_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v___y_544_ = v___x_558_;
goto v___jp_543_;
}
}
}
}
case 1:
{
lean_object* v_node_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_573_; 
v_node_561_ = lean_ctor_get(v_v_540_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_v_540_);
if (v_isSharedCheck_573_ == 0)
{
v___x_563_ = v_v_540_;
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_node_561_);
lean_dec(v_v_540_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_565_ = ((size_t)5ULL);
v___x_566_ = lean_usize_shift_right(v_x_527_, v___x_565_);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_x_528_, v___x_567_);
v___x_569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_561_, v___x_566_, v___x_568_, v_x_529_, v_x_530_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_569_);
v___x_571_ = v___x_563_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v___y_544_ = v___x_571_;
goto v___jp_543_;
}
}
}
default: 
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_x_529_);
lean_ctor_set(v___x_574_, 1, v_x_530_);
v___y_544_ = v___x_574_;
goto v___jp_543_;
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_array_fset(v_xs_x27_542_, v_j_534_, v___y_544_);
lean_dec(v_j_534_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_545_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_ks_577_; lean_object* v_vs_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_598_; 
v_ks_577_ = lean_ctor_get(v_x_526_, 0);
v_vs_578_ = lean_ctor_get(v_x_526_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_598_ == 0)
{
v___x_580_ = v_x_526_;
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_vs_578_);
lean_inc(v_ks_577_);
lean_dec(v_x_526_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_ks_577_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_vs_578_);
v___x_583_ = v_reuseFailAlloc_597_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v_newNode_584_; uint8_t v___y_586_; size_t v___x_592_; uint8_t v___x_593_; 
v_newNode_584_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_583_, v_x_529_, v_x_530_);
v___x_592_ = ((size_t)7ULL);
v___x_593_ = lean_usize_dec_le(v___x_592_, v_x_528_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_584_);
v___x_595_ = lean_unsigned_to_nat(4u);
v___x_596_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
v___y_586_ = v___x_596_;
goto v___jp_585_;
}
else
{
v___y_586_ = v___x_593_;
goto v___jp_585_;
}
v___jp_585_:
{
if (v___y_586_ == 0)
{
lean_object* v_ks_587_; lean_object* v_vs_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_ks_587_ = lean_ctor_get(v_newNode_584_, 0);
lean_inc_ref(v_ks_587_);
v_vs_588_ = lean_ctor_get(v_newNode_584_, 1);
lean_inc_ref(v_vs_588_);
lean_dec_ref(v_newNode_584_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_528_, v_ks_587_, v_vs_588_, v___x_589_, v___x_590_);
lean_dec_ref(v_vs_588_);
lean_dec_ref(v_ks_587_);
return v___x_591_;
}
else
{
return v_newNode_584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_599_, lean_object* v_keys_600_, lean_object* v_vals_601_, lean_object* v_i_602_, lean_object* v_entries_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_keys_600_);
v___x_605_ = lean_nat_dec_lt(v_i_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_i_602_);
return v_entries_603_;
}
else
{
lean_object* v_k_606_; lean_object* v_v_607_; uint64_t v___y_609_; 
v_k_606_ = lean_array_fget_borrowed(v_keys_600_, v_i_602_);
v_v_607_ = lean_array_fget_borrowed(v_vals_601_, v_i_602_);
if (lean_obj_tag(v_k_606_) == 0)
{
uint64_t v___x_620_; 
v___x_620_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_609_ = v___x_620_;
goto v___jp_608_;
}
else
{
uint64_t v_hash_621_; 
v_hash_621_ = lean_ctor_get_uint64(v_k_606_, sizeof(void*)*2);
v___y_609_ = v_hash_621_;
goto v___jp_608_;
}
v___jp_608_:
{
size_t v_h_610_; size_t v___x_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v_h_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_h_610_ = lean_uint64_to_usize(v___y_609_);
v___x_611_ = ((size_t)5ULL);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_sub(v_depth_599_, v___x_613_);
v___x_615_ = lean_usize_mul(v___x_611_, v___x_614_);
v_h_616_ = lean_usize_shift_right(v_h_610_, v___x_615_);
v___x_617_ = lean_nat_add(v_i_602_, v___x_612_);
lean_dec(v_i_602_);
lean_inc(v_v_607_);
lean_inc(v_k_606_);
v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_603_, v_h_616_, v_depth_599_, v_k_606_, v_v_607_);
v_i_602_ = v___x_617_;
v_entries_603_ = v___x_618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_622_, lean_object* v_keys_623_, lean_object* v_vals_624_, lean_object* v_i_625_, lean_object* v_entries_626_){
_start:
{
size_t v_depth_boxed_627_; lean_object* v_res_628_; 
v_depth_boxed_627_ = lean_unbox_usize(v_depth_622_);
lean_dec(v_depth_622_);
v_res_628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_627_, v_keys_623_, v_vals_624_, v_i_625_, v_entries_626_);
lean_dec_ref(v_vals_624_);
lean_dec_ref(v_keys_623_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_1444__boxed_634_; size_t v_x_1445__boxed_635_; lean_object* v_res_636_; 
v_x_1444__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_x_1445__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_629_, v_x_1444__boxed_634_, v_x_1445__boxed_635_, v_x_632_, v_x_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
uint64_t v___y_641_; 
if (lean_obj_tag(v_x_638_) == 0)
{
uint64_t v___x_645_; 
v___x_645_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
v___y_641_ = v___x_645_;
goto v___jp_640_;
}
else
{
uint64_t v_hash_646_; 
v_hash_646_ = lean_ctor_get_uint64(v_x_638_, sizeof(void*)*2);
v___y_641_ = v_hash_646_;
goto v___jp_640_;
}
v___jp_640_:
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_uint64_to_usize(v___y_641_);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_637_, v___x_642_, v___x_643_, v_x_638_, v_x_639_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_stage_u2081_650_; 
v_stage_u2081_650_ = lean_ctor_get_uint8(v_x_647_, sizeof(void*)*2);
if (v_stage_u2081_650_ == 0)
{
lean_object* v_map_u2081_651_; lean_object* v_map_u2082_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_map_u2081_651_ = lean_ctor_get(v_x_647_, 0);
v_map_u2082_652_ = lean_ctor_get(v_x_647_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v_x_647_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_map_u2082_652_);
lean_inc(v_map_u2081_651_);
lean_dec(v_x_647_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_652_, v_x_648_, v_x_649_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_map_u2081_651_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_656_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*2, v_stage_u2081_650_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_map_u2081_661_; lean_object* v_map_u2082_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_map_u2081_661_ = lean_ctor_get(v_x_647_, 0);
v_map_u2082_662_ = lean_ctor_get(v_x_647_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v_x_647_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_map_u2082_662_);
lean_inc(v_map_u2081_661_);
lean_dec(v_x_647_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_661_, v_x_648_, v_x_649_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_map_u2082_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*2, v_stage_u2081_650_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(32u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_674_ = ((size_t)5ULL);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_unsigned_to_nat(32u);
v___x_677_ = lean_mk_empty_array_with_capacity(v___x_676_);
v___x_678_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_679_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v___x_675_);
lean_ctor_set(v___x_679_, 3, v___x_675_);
lean_ctor_set_usize(v___x_679_, 4, v___x_674_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_680_, lean_object* v_ns_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_680_, v_ns_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_685_ = l_Lean_PersistentArray_push___redArg(v___x_684_, v_b_682_);
v___x_686_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_680_, v_ns_681_, v___x_685_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_val_687_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_683_, 1);
v___x_688_ = l_Lean_PersistentArray_push___redArg(v_val_687_, v_b_682_);
v___x_689_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_680_, v_ns_681_, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_690_, lean_object* v_scopedEntries_691_, lean_object* v_ns_692_, lean_object* v_b_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_691_, v_ns_692_, v_b_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_699_, v_x_700_, v_x_701_);
lean_dec(v_x_701_);
lean_dec_ref(v_x_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_704_, v_x_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_712_, v_x_713_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_717_, v_a_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_720_, lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_720_, v_m_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_m_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_725_, v_x_726_, v_x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_a_731_, lean_object* v_b_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_730_, v_a_731_, v_b_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, size_t v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_735_, v_x_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
size_t v_x_1752__boxed_743_; lean_object* v_res_744_; 
v_x_1752__boxed_743_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_res_744_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_739_, v_x_740_, v_x_1752__boxed_743_, v_x_742_);
lean_dec(v_x_742_);
lean_dec_ref(v_x_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_749_, v_a_750_, v_x_751_);
lean_dec(v_x_751_);
lean_dec(v_a_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_753_, lean_object* v_x_754_, size_t v_x_755_, size_t v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_754_, v_x_755_, v_x_756_, v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
size_t v_x_1768__boxed_766_; size_t v_x_1769__boxed_767_; lean_object* v_res_768_; 
v_x_1768__boxed_766_ = lean_unbox_usize(v_x_762_);
lean_dec(v_x_762_);
v_x_1769__boxed_767_ = lean_unbox_usize(v_x_763_);
lean_dec(v_x_763_);
v_res_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_760_, v_x_761_, v_x_1768__boxed_766_, v_x_1769__boxed_767_, v_x_764_, v_x_765_);
return v_res_768_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_769_, lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
uint8_t v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_773_, lean_object* v_a_774_, lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_773_, v_a_774_, v_x_775_);
lean_dec(v_x_775_);
lean_dec(v_a_774_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_778_, lean_object* v_data_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_781_, lean_object* v_a_782_, lean_object* v_b_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_782_, v_b_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_786_, lean_object* v_keys_787_, lean_object* v_vals_788_, lean_object* v_heq_789_, lean_object* v_i_790_, lean_object* v_k_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_787_, v_vals_788_, v_i_790_, v_k_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_heq_796_, lean_object* v_i_797_, lean_object* v_k_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_793_, v_keys_794_, v_vals_795_, v_heq_796_, v_i_797_, v_k_798_);
lean_dec(v_k_798_);
lean_dec_ref(v_vals_795_);
lean_dec_ref(v_keys_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_800_, lean_object* v_n_801_, lean_object* v_k_802_, lean_object* v_v_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_801_, v_k_802_, v_v_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_805_, size_t v_depth_806_, lean_object* v_keys_807_, lean_object* v_vals_808_, lean_object* v_heq_809_, lean_object* v_i_810_, lean_object* v_entries_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_806_, v_keys_807_, v_vals_808_, v_i_810_, v_entries_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_813_, lean_object* v_depth_814_, lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_heq_817_, lean_object* v_i_818_, lean_object* v_entries_819_){
_start:
{
size_t v_depth_boxed_820_; lean_object* v_res_821_; 
v_depth_boxed_820_ = lean_unbox_usize(v_depth_814_);
lean_dec(v_depth_814_);
v_res_821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_813_, v_depth_boxed_820_, v_keys_815_, v_vals_816_, v_heq_817_, v_i_818_, v_entries_819_);
lean_dec_ref(v_vals_816_);
lean_dec_ref(v_keys_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_822_, lean_object* v_i_823_, lean_object* v_source_824_, lean_object* v_target_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_823_, v_source_824_, v_target_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_828_, v_x_829_, v_x_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_837_, lean_object* v_as_838_, size_t v_sz_839_, size_t v_i_840_, lean_object* v_b_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_a_845_; uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_lt(v_i_840_, v_sz_839_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec_ref(v_descr_837_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_b_841_);
return v___x_850_;
}
else
{
lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_891_; 
v_fst_851_ = lean_ctor_get(v_b_841_, 0);
v_snd_852_ = lean_ctor_get(v_b_841_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_b_841_);
if (v_isSharedCheck_891_ == 0)
{
v___x_854_ = v_b_841_;
v_isShared_855_ = v_isSharedCheck_891_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_inc(v_fst_851_);
lean_dec(v_b_841_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_891_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_a_856_; 
v_a_856_ = lean_array_uget_borrowed(v_as_838_, v_i_840_);
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_ofOLeanEntry_858_; lean_object* v_addEntry_859_; lean_object* v___x_860_; 
v_a_857_ = lean_ctor_get(v_a_856_, 0);
v_ofOLeanEntry_858_ = lean_ctor_get(v_descr_837_, 2);
v_addEntry_859_ = lean_ctor_get(v_descr_837_, 4);
lean_inc_ref(v_ofOLeanEntry_858_);
lean_inc_ref(v___y_842_);
lean_inc(v_a_857_);
lean_inc(v_fst_851_);
v___x_860_ = lean_apply_4(v_ofOLeanEntry_858_, v_fst_851_, v_a_857_, v___y_842_, lean_box(0));
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
lean_inc(v_addEntry_859_);
v___x_862_ = lean_apply_2(v_addEntry_859_, v_fst_851_, v_a_861_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_862_);
v___x_864_ = v___x_854_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_snd_852_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
v_a_845_ = v___x_864_;
goto v___jp_844_;
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
lean_dec(v_fst_851_);
lean_dec_ref(v_descr_837_);
v_a_866_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_860_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_860_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v_a_875_; lean_object* v_ofOLeanEntry_876_; lean_object* v___x_877_; 
v_a_874_ = lean_ctor_get(v_a_856_, 0);
v_a_875_ = lean_ctor_get(v_a_856_, 1);
v_ofOLeanEntry_876_ = lean_ctor_get(v_descr_837_, 2);
lean_inc_ref(v_ofOLeanEntry_876_);
lean_inc_ref(v___y_842_);
lean_inc(v_a_875_);
lean_inc(v_fst_851_);
v___x_877_ = lean_apply_4(v_ofOLeanEntry_876_, v_fst_851_, v_a_875_, v___y_842_, lean_box(0));
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
lean_inc(v_a_874_);
v___x_879_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_852_, v_a_874_, v_a_878_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_879_);
v___x_881_ = v___x_854_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_fst_851_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
v_a_845_ = v___x_881_;
goto v___jp_844_;
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
lean_dec(v_fst_851_);
lean_dec_ref(v_descr_837_);
v_a_883_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_877_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_877_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
v___jp_844_:
{
size_t v___x_846_; size_t v___x_847_; 
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_840_, v___x_846_);
v_i_840_ = v___x_847_;
v_b_841_ = v_a_845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_892_, lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_900_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_892_, v_as_893_, v_sz_boxed_899_, v_i_boxed_900_, v_b_896_, v___y_897_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_as_893_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_902_, lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_, lean_object* v___y_907_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec_ref(v_descr_902_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v_b_906_);
return v___x_910_;
}
else
{
lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_936_; 
v_fst_911_ = lean_ctor_get(v_b_906_, 0);
v_snd_912_ = lean_ctor_get(v_b_906_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_b_906_);
if (v_isSharedCheck_936_ == 0)
{
v___x_914_ = v_b_906_;
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v_b_906_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_a_916_; lean_object* v___x_918_; 
v_a_916_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
if (v_isShared_915_ == 0)
{
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_912_);
v___x_918_ = v_reuseFailAlloc_935_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
size_t v_sz_919_; size_t v___x_920_; lean_object* v___x_921_; 
v_sz_919_ = lean_array_size(v_a_916_);
v___x_920_ = ((size_t)0ULL);
lean_inc_ref(v_descr_902_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_902_, v_a_916_, v_sz_919_, v___x_920_, v___x_918_, v___y_907_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_fst_923_ = lean_ctor_get(v_a_922_, 0);
v_snd_924_ = lean_ctor_get(v_a_922_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_934_ == 0)
{
v___x_926_ = v_a_922_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_inc(v_fst_923_);
lean_dec(v_a_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_snd_924_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_905_, v___x_930_);
v_i_905_ = v___x_931_;
v_b_906_ = v___x_929_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_902_);
return v___x_921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_937_, lean_object* v_as_938_, lean_object* v_sz_939_, lean_object* v_i_940_, lean_object* v_b_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_939_);
lean_dec(v_sz_939_);
v_i_boxed_945_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_937_, v_as_938_, v_sz_boxed_944_, v_i_boxed_945_, v_b_941_, v___y_942_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v_as_938_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_947_, lean_object* v_as_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_mkInitial_951_; lean_object* v_finalizeImport_952_; lean_object* v___x_953_; 
v_mkInitial_951_ = lean_ctor_get(v_descr_947_, 1);
v_finalizeImport_952_ = lean_ctor_get(v_descr_947_, 5);
lean_inc(v_finalizeImport_952_);
lean_inc_ref(v_mkInitial_951_);
v___x_953_ = lean_apply_1(v_mkInitial_951_, lean_box(0));
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = 1;
v___x_956_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_a_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v_sz_958_ = lean_array_size(v_as_948_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_947_, v_as_948_, v_sz_958_, v___x_959_, v___x_957_, v_a_949_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_982_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_982_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_982_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_981_; 
v_fst_965_ = lean_ctor_get(v_a_961_, 0);
v_snd_966_ = lean_ctor_get(v_a_961_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_981_ == 0)
{
v___x_968_ = v_a_961_;
v_isShared_969_ = v_isSharedCheck_981_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v_a_961_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_981_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_970_ = lean_apply_1(v_finalizeImport_952_, v_fst_965_);
v___x_971_ = l_Lean_NameSet_empty;
v___x_972_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*2, v___x_955_);
v___x_973_ = lean_box(0);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
lean_ctor_set(v___x_968_, 1, v___x_973_);
lean_ctor_set(v___x_968_, 0, v___x_972_);
v___x_975_ = v___x_968_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_980_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v_snd_966_);
lean_ctor_set(v___x_976_, 2, v___x_973_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_976_);
v___x_978_ = v___x_963_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_finalizeImport_952_);
v_a_983_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_960_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_960_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_finalizeImport_952_);
lean_dec_ref(v_descr_947_);
v_a_991_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_953_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_953_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_999_, lean_object* v_as_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_999_, v_as_1000_, v_a_1001_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_as_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_00_u03c3_1006_, lean_object* v_descr_1007_, lean_object* v_as_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1007_, v_as_1008_, v_a_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_00_u03c3_1014_, lean_object* v_descr_1015_, lean_object* v_as_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1012_, v_00_u03b2_1013_, v_00_u03c3_1014_, v_descr_1015_, v_as_1016_, v_a_1017_);
lean_dec_ref(v_a_1017_);
lean_dec_ref(v_as_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03c3_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_descr_1023_, lean_object* v_as_1024_, size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1023_, v_as_1024_, v_sz_1025_, v_i_1026_, v_b_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03c3_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_descr_1034_, lean_object* v_as_1035_, lean_object* v_sz_1036_, lean_object* v_i_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
size_t v_sz_boxed_1041_; size_t v_i_boxed_1042_; lean_object* v_res_1043_; 
v_sz_boxed_1041_ = lean_unbox_usize(v_sz_1036_);
lean_dec(v_sz_1036_);
v_i_boxed_1042_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1031_, v_00_u03c3_1032_, v_00_u03b2_1033_, v_descr_1034_, v_as_1035_, v_sz_boxed_1041_, v_i_boxed_1042_, v_b_1038_, v___y_1039_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_as_1035_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03c3_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_descr_1047_, lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1047_, v_as_1048_, v_sz_1049_, v_i_1050_, v_b_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03c3_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_descr_1058_, lean_object* v_as_1059_, lean_object* v_sz_1060_, lean_object* v_i_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1055_, v_00_u03c3_1056_, v_00_u03b2_1057_, v_descr_1058_, v_as_1059_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1062_, v___y_1063_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v_as_1059_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1068_, lean_object* v_descr_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
if (lean_obj_tag(v_a_1071_) == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_a_1070_);
lean_dec_ref(v_descr_1069_);
v___x_1073_ = l_List_reverse___redArg(v_a_1072_);
return v___x_1073_;
}
else
{
lean_object* v_head_1074_; lean_object* v_tail_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1100_; 
v_head_1074_ = lean_ctor_get(v_a_1071_, 0);
v_tail_1075_ = lean_ctor_get(v_a_1071_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_a_1071_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1077_ = v_a_1071_;
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_tail_1075_);
lean_inc(v_head_1074_);
lean_dec(v_a_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___y_1080_; lean_object* v_state_1085_; lean_object* v_activeScopes_1086_; uint8_t v_delimitsLocal_1087_; uint8_t v___x_1088_; 
v_state_1085_ = lean_ctor_get(v_head_1074_, 0);
v_activeScopes_1086_ = lean_ctor_get(v_head_1074_, 1);
v_delimitsLocal_1087_ = lean_ctor_get_uint8(v_head_1074_, sizeof(void*)*2);
v___x_1088_ = l_Lean_NameSet_contains(v_activeScopes_1086_, v_a_1068_);
if (v___x_1088_ == 0)
{
v___y_1080_ = v_head_1074_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
lean_inc(v_activeScopes_1086_);
lean_inc(v_state_1085_);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_head_1074_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1098_ = lean_ctor_get(v_head_1074_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_head_1074_, 0);
lean_dec(v_unused_1099_);
v___x_1090_ = v_head_1074_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_head_1074_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_addEntry_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v_addEntry_1092_ = lean_ctor_get(v_descr_1069_, 4);
lean_inc(v_addEntry_1092_);
lean_inc(v_a_1070_);
v___x_1093_ = lean_apply_2(v_addEntry_1092_, v_state_1085_, v_a_1070_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_activeScopes_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1096_, sizeof(void*)*2, v_delimitsLocal_1087_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1080_ = v___x_1095_;
goto v___jp_1079_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_a_1072_);
lean_ctor_set(v___x_1077_, 0, v___y_1080_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___y_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1072_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
v_a_1071_ = v_tail_1075_;
v_a_1072_ = v___x_1082_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1101_, lean_object* v_descr_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1101_, v_descr_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
if (lean_obj_tag(v_a_1109_) == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_a_1108_);
lean_dec_ref(v_descr_1107_);
v___x_1111_ = l_List_reverse___redArg(v_a_1110_);
return v___x_1111_;
}
else
{
lean_object* v_head_1112_; lean_object* v_tail_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1133_; 
v_head_1112_ = lean_ctor_get(v_a_1109_, 0);
v_tail_1113_ = lean_ctor_get(v_a_1109_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1115_ = v_a_1109_;
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_tail_1113_);
lean_inc(v_head_1112_);
lean_dec(v_a_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_addEntry_1117_; lean_object* v_state_1118_; lean_object* v_activeScopes_1119_; uint8_t v_delimitsLocal_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1132_; 
v_addEntry_1117_ = lean_ctor_get(v_descr_1107_, 4);
v_state_1118_ = lean_ctor_get(v_head_1112_, 0);
v_activeScopes_1119_ = lean_ctor_get(v_head_1112_, 1);
v_delimitsLocal_1120_ = lean_ctor_get_uint8(v_head_1112_, sizeof(void*)*2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_head_1112_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1122_ = v_head_1112_;
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_activeScopes_1119_);
lean_inc(v_state_1118_);
lean_dec(v_head_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_addEntry_1117_);
lean_inc(v_a_1108_);
v___x_1124_ = lean_apply_2(v_addEntry_1117_, v_state_1118_, v_a_1108_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_activeScopes_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1131_, sizeof(void*)*2, v_delimitsLocal_1120_);
v___x_1126_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_a_1110_);
lean_ctor_set(v___x_1115_, 0, v___x_1126_);
v___x_1128_ = v___x_1115_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_a_1110_);
v___x_1128_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v_a_1109_ = v_tail_1113_;
v_a_1110_ = v___x_1128_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1134_, lean_object* v_s_1135_, lean_object* v_e_1136_){
_start:
{
if (lean_obj_tag(v_e_1136_) == 0)
{
lean_object* v_stateStack_1137_; lean_object* v_scopedEntries_1138_; lean_object* v_newEntries_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1159_; 
v_stateStack_1137_ = lean_ctor_get(v_s_1135_, 0);
v_scopedEntries_1138_ = lean_ctor_get(v_s_1135_, 1);
v_newEntries_1139_ = lean_ctor_get(v_s_1135_, 2);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_s_1135_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1141_ = v_s_1135_;
v_isShared_1142_ = v_isSharedCheck_1159_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_newEntries_1139_);
lean_inc(v_scopedEntries_1138_);
lean_inc(v_stateStack_1137_);
lean_dec(v_s_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1159_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1158_; 
v_a_1143_ = lean_ctor_get(v_e_1136_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_e_1136_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1145_ = v_e_1136_;
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v_e_1136_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_toOLeanEntry_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v_toOLeanEntry_1147_ = lean_ctor_get(v_descr_1134_, 3);
lean_inc(v_toOLeanEntry_1147_);
v___x_1148_ = lean_box(0);
lean_inc(v_a_1143_);
v___x_1149_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1134_, v_a_1143_, v_stateStack_1137_, v___x_1148_);
v___x_1150_ = lean_apply_1(v_toOLeanEntry_1147_, v_a_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1150_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_newEntries_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 2, v___x_1153_);
lean_ctor_set(v___x_1141_, 0, v___x_1149_);
v___x_1155_ = v___x_1141_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_scopedEntries_1138_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1160_; lean_object* v_scopedEntries_1161_; lean_object* v_newEntries_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1184_; 
v_stateStack_1160_ = lean_ctor_get(v_s_1135_, 0);
v_scopedEntries_1161_ = lean_ctor_get(v_s_1135_, 1);
v_newEntries_1162_ = lean_ctor_get(v_s_1135_, 2);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_s_1135_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1164_ = v_s_1135_;
v_isShared_1165_ = v_isSharedCheck_1184_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_newEntries_1162_);
lean_inc(v_scopedEntries_1161_);
lean_inc(v_stateStack_1160_);
lean_dec(v_s_1135_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1184_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_a_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1183_; 
v_a_1166_ = lean_ctor_get(v_e_1136_, 0);
v_a_1167_ = lean_ctor_get(v_e_1136_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_e_1136_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1169_ = v_e_1136_;
v_isShared_1170_ = v_isSharedCheck_1183_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_inc(v_a_1166_);
lean_dec(v_e_1136_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1183_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_toOLeanEntry_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_toOLeanEntry_1171_ = lean_ctor_get(v_descr_1134_, 3);
lean_inc(v_toOLeanEntry_1171_);
v___x_1172_ = lean_box(0);
lean_inc_n(v_a_1167_, 2);
v___x_1173_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1166_, v_descr_1134_, v_a_1167_, v_stateStack_1160_, v___x_1172_);
lean_inc(v_a_1166_);
v___x_1174_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1161_, v_a_1166_, v_a_1167_);
v___x_1175_ = lean_apply_1(v_toOLeanEntry_1171_, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1175_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1166_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_newEntries_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 2, v___x_1178_);
lean_ctor_set(v___x_1164_, 1, v___x_1174_);
lean_ctor_set(v___x_1164_, 0, v___x_1173_);
v___x_1180_ = v___x_1164_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_00_u03c3_1187_, lean_object* v_descr_1188_, lean_object* v_s_1189_, lean_object* v_e_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1188_, v_s_1189_, v_e_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_00_u03b1_1194_, lean_object* v_descr_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1200_, lean_object* v_a_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_descr_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1201_, v_descr_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1209_, lean_object* v_a_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_00_u03b1_1212_, lean_object* v_descr_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1209_, v_a_1210_, v_00_u03b2_1211_, v_00_u03b1_1212_, v_descr_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1210_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1218_, lean_object* v_env_1219_, lean_object* v_as_1220_, size_t v_sz_1221_, size_t v_i_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v_a_1225_; uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_lt(v_i_1222_, v_sz_1221_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v_env_1219_);
lean_dec_ref(v_descr_1218_);
return v_b_1223_;
}
else
{
lean_object* v_snd_1230_; lean_object* v_fst_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1331_; 
v_snd_1230_ = lean_ctor_get(v_b_1223_, 1);
v_fst_1231_ = lean_ctor_get(v_b_1223_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_b_1223_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1233_ = v_b_1223_;
v_isShared_1234_ = v_isSharedCheck_1331_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1231_);
lean_dec(v_b_1223_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1331_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_fst_1235_; lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1330_; 
v_fst_1235_ = lean_ctor_get(v_snd_1230_, 0);
v_snd_1236_ = lean_ctor_get(v_snd_1230_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_snd_1230_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1238_ = v_snd_1230_;
v_isShared_1239_ = v_isSharedCheck_1330_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1235_);
lean_dec(v_snd_1230_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1330_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_a_1240_; 
v_a_1240_ = lean_array_uget(v_as_1220_, v_i_1222_);
if (lean_obj_tag(v_a_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1290_; 
v_a_1241_ = lean_ctor_get(v_a_1240_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1240_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1243_ = v_a_1240_;
v_isShared_1244_ = v_isSharedCheck_1290_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v_a_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1290_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_exportEntry_x3f_1245_; lean_object* v___x_1246_; lean_object* v_exported_1247_; lean_object* v_server_1248_; lean_object* v_private_1249_; lean_object* v___y_1251_; lean_object* v_server_1252_; lean_object* v_exported_1271_; 
v_exportEntry_x3f_1245_ = lean_ctor_get(v_descr_1218_, 6);
lean_inc_ref(v_exportEntry_x3f_1245_);
lean_inc_ref(v_env_1219_);
v___x_1246_ = lean_apply_2(v_exportEntry_x3f_1245_, v_env_1219_, v_a_1241_);
v_exported_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_exported_1247_);
v_server_1248_ = lean_ctor_get(v___x_1246_, 1);
lean_inc(v_server_1248_);
v_private_1249_ = lean_ctor_get(v___x_1246_, 2);
lean_inc(v_private_1249_);
lean_dec_ref(v___x_1246_);
if (lean_obj_tag(v_exported_1247_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_val_1281_ = lean_ctor_get(v_exported_1247_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_exported_1247_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v_exported_1247_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_val_1281_);
lean_dec(v_exported_1247_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 0);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_val_1281_);
v___x_1286_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_array_push(v_fst_1231_, v___x_1286_);
v_exported_1271_ = v___x_1287_;
goto v___jp_1270_;
}
}
}
else
{
lean_dec(v_exported_1247_);
v_exported_1271_ = v_fst_1231_;
goto v___jp_1270_;
}
v___jp_1250_:
{
if (lean_obj_tag(v_private_1249_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1255_; 
v_val_1253_ = lean_ctor_get(v_private_1249_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v_private_1249_, 1);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_val_1253_);
v___x_1255_ = v___x_1243_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_val_1253_);
v___x_1255_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_array_push(v_snd_1236_, v___x_1255_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1256_);
lean_ctor_set(v___x_1238_, 0, v_server_1252_);
v___x_1258_ = v___x_1238_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_server_1252_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1258_);
lean_ctor_set(v___x_1233_, 0, v___y_1251_);
v___x_1260_ = v___x_1233_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___y_1251_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v_a_1225_ = v___x_1260_;
goto v___jp_1224_;
}
}
}
}
else
{
lean_object* v___x_1265_; 
lean_dec(v_private_1249_);
lean_del_object(v___x_1243_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_server_1252_);
v___x_1265_ = v___x_1238_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_server_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1236_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1265_);
lean_ctor_set(v___x_1233_, 0, v___y_1251_);
v___x_1267_ = v___x_1233_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___y_1251_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v_a_1225_ = v___x_1267_;
goto v___jp_1224_;
}
}
}
}
v___jp_1270_:
{
if (lean_obj_tag(v_server_1248_) == 1)
{
lean_object* v_val_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_val_1272_ = lean_ctor_get(v_server_1248_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_server_1248_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v_server_1248_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_val_1272_);
lean_dec(v_server_1248_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 0);
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_val_1272_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_push(v_fst_1235_, v___x_1277_);
v___y_1251_ = v_exported_1271_;
v_server_1252_ = v___x_1278_;
goto v___jp_1250_;
}
}
}
else
{
lean_dec(v_server_1248_);
v___y_1251_ = v_exported_1271_;
v_server_1252_ = v_fst_1235_;
goto v___jp_1250_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1329_; 
v_a_1291_ = lean_ctor_get(v_a_1240_, 0);
v_a_1292_ = lean_ctor_get(v_a_1240_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_a_1240_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1294_ = v_a_1240_;
v_isShared_1295_ = v_isSharedCheck_1329_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_inc(v_a_1291_);
lean_dec(v_a_1240_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1329_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_exportEntry_x3f_1296_; lean_object* v___x_1297_; lean_object* v_exported_1298_; lean_object* v_server_1299_; lean_object* v_private_1300_; lean_object* v___y_1302_; lean_object* v_server_1303_; lean_object* v_exported_1322_; 
v_exportEntry_x3f_1296_ = lean_ctor_get(v_descr_1218_, 6);
lean_inc_ref(v_exportEntry_x3f_1296_);
lean_inc_ref(v_env_1219_);
v___x_1297_ = lean_apply_2(v_exportEntry_x3f_1296_, v_env_1219_, v_a_1292_);
v_exported_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_exported_1298_);
v_server_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_server_1299_);
v_private_1300_ = lean_ctor_get(v___x_1297_, 2);
lean_inc(v_private_1300_);
lean_dec_ref(v___x_1297_);
if (lean_obj_tag(v_exported_1298_) == 1)
{
lean_object* v_val_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_val_1326_ = lean_ctor_get(v_exported_1298_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v_exported_1298_, 1);
lean_inc(v_a_1291_);
v___x_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_a_1291_);
lean_ctor_set(v___x_1327_, 1, v_val_1326_);
v___x_1328_ = lean_array_push(v_fst_1231_, v___x_1327_);
v_exported_1322_ = v___x_1328_;
goto v___jp_1321_;
}
else
{
lean_dec(v_exported_1298_);
v_exported_1322_ = v_fst_1231_;
goto v___jp_1321_;
}
v___jp_1301_:
{
if (lean_obj_tag(v_private_1300_) == 1)
{
lean_object* v_val_1304_; lean_object* v___x_1306_; 
v_val_1304_ = lean_ctor_get(v_private_1300_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v_private_1300_, 1);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v_val_1304_);
v___x_1306_ = v___x_1294_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1291_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_val_1304_);
v___x_1306_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_array_push(v_snd_1236_, v___x_1306_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1307_);
lean_ctor_set(v___x_1238_, 0, v_server_1303_);
v___x_1309_ = v___x_1238_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_server_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1309_);
lean_ctor_set(v___x_1233_, 0, v___y_1302_);
v___x_1311_ = v___x_1233_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___y_1302_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
v_a_1225_ = v___x_1311_;
goto v___jp_1224_;
}
}
}
}
else
{
lean_object* v___x_1316_; 
lean_dec(v_private_1300_);
lean_del_object(v___x_1294_);
lean_dec(v_a_1291_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_server_1303_);
v___x_1316_ = v___x_1238_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_server_1303_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_snd_1236_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1316_);
lean_ctor_set(v___x_1233_, 0, v___y_1302_);
v___x_1318_ = v___x_1233_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___y_1302_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_a_1225_ = v___x_1318_;
goto v___jp_1224_;
}
}
}
}
v___jp_1321_:
{
if (lean_obj_tag(v_server_1299_) == 1)
{
lean_object* v_val_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_val_1323_ = lean_ctor_get(v_server_1299_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v_server_1299_, 1);
lean_inc(v_a_1291_);
v___x_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_a_1291_);
lean_ctor_set(v___x_1324_, 1, v_val_1323_);
v___x_1325_ = lean_array_push(v_fst_1235_, v___x_1324_);
v___y_1302_ = v_exported_1322_;
v_server_1303_ = v___x_1325_;
goto v___jp_1301_;
}
else
{
lean_dec(v_server_1299_);
v___y_1302_ = v_exported_1322_;
v_server_1303_ = v_fst_1235_;
goto v___jp_1301_;
}
}
}
}
}
}
}
v___jp_1224_:
{
size_t v___x_1226_; size_t v___x_1227_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1222_, v___x_1226_);
v_i_1222_ = v___x_1227_;
v_b_1223_ = v_a_1225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1332_, lean_object* v_env_1333_, lean_object* v_as_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_b_1337_){
_start:
{
size_t v_sz_boxed_1338_; size_t v_i_boxed_1339_; lean_object* v_res_1340_; 
v_sz_boxed_1338_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1339_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1332_, v_env_1333_, v_as_1334_, v_sz_boxed_1338_, v_i_boxed_1339_, v_b_1337_);
lean_dec_ref(v_as_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1348_, lean_object* v_env_1349_, lean_object* v_s_1350_){
_start:
{
lean_object* v_newEntries_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1368_; 
v_newEntries_1351_ = lean_ctor_get(v_s_1350_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_s_1350_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1369_ = lean_ctor_get(v_s_1350_, 1);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_s_1350_, 0);
lean_dec(v_unused_1370_);
v___x_1353_ = v_s_1350_;
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_newEntries_1351_);
lean_dec(v_s_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; lean_object* v_snd_1361_; lean_object* v_fst_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1366_; 
v___x_1355_ = lean_array_mk(v_newEntries_1351_);
v___x_1356_ = l_Array_reverse___redArg(v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1358_ = lean_array_size(v___x_1356_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1348_, v_env_1349_, v___x_1356_, v_sz_1358_, v___x_1359_, v___x_1357_);
lean_dec_ref(v___x_1356_);
v_snd_1361_ = lean_ctor_get(v___x_1360_, 1);
lean_inc(v_snd_1361_);
v_fst_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_fst_1362_);
lean_dec_ref(v___x_1360_);
v_fst_1363_ = lean_ctor_get(v_snd_1361_, 0);
lean_inc(v_fst_1363_);
v_snd_1364_ = lean_ctor_get(v_snd_1361_, 1);
lean_inc(v_snd_1364_);
lean_dec(v_snd_1361_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 2, v_snd_1364_);
lean_ctor_set(v___x_1353_, 1, v_fst_1363_);
lean_ctor_set(v___x_1353_, 0, v_fst_1362_);
v___x_1366_ = v___x_1353_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1362_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_fst_1363_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_snd_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1371_, lean_object* v_00_u03b2_1372_, lean_object* v_00_u03c3_1373_, lean_object* v_descr_1374_, lean_object* v_env_1375_, lean_object* v_s_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1374_, v_env_1375_, v_s_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_00_u03c3_1380_, lean_object* v_descr_1381_, lean_object* v_env_1382_, lean_object* v_as_1383_, size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_b_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1381_, v_env_1382_, v_as_1383_, v_sz_1384_, v_i_1385_, v_b_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_00_u03b2_1389_, lean_object* v_00_u03c3_1390_, lean_object* v_descr_1391_, lean_object* v_env_1392_, lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1388_, v_00_u03b2_1389_, v_00_u03c3_1390_, v_descr_1391_, v_env_1392_, v_as_1393_, v_sz_boxed_1397_, v_i_boxed_1398_, v_b_1396_);
lean_dec_ref(v_as_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1405_, v___y_1406_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v_x_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1409_, lean_object* v_x_1410_){
_start:
{
lean_inc_ref(v_s_1409_);
return v_s_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1411_, v_x_1412_);
lean_dec_ref(v_x_1412_);
lean_dec_ref(v_s_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1419_, v_x_1420_);
lean_dec_ref(v_x_1420_);
lean_dec_ref(v_x_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_box(0);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1424_);
lean_dec_ref(v_x_1424_);
return v_res_1425_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___f_1431_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1432_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1433_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1434_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1437_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
lean_ctor_set(v___x_1437_, 2, v___f_1434_);
lean_ctor_set(v___x_1437_, 3, v___f_1433_);
lean_ctor_set(v___x_1437_, 4, v___f_1432_);
lean_ctor_set(v___x_1437_, 5, v___f_1431_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1438_){
_start:
{
lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___f_1439_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1440_, 0, v_inst_1438_);
v___f_1441_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1442_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1445_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1446_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1443_);
lean_ctor_set(v___x_1446_, 1, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v___f_1439_);
lean_ctor_set(v___x_1446_, 3, v___f_1440_);
lean_ctor_set(v___x_1446_, 4, v___f_1441_);
lean_ctor_set(v___x_1446_, 5, v___x_1445_);
lean_ctor_set(v___x_1446_, 6, v___f_1442_);
v___x_1447_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1449_, lean_object* v_00_u03b2_1450_, lean_object* v_00_u03c3_1451_, lean_object* v_inst_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1456_, lean_object* v_inst_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1465_ = lean_st_mk_ref(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1472_){
_start:
{
lean_object* v_newEntries_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_newEntries_1473_ = lean_ctor_get(v_s_1472_, 2);
v___x_1474_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1475_ = l_List_lengthTR___redArg(v_newEntries_1473_);
v___x_1476_ = l_Nat_reprFast(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1474_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1479_);
lean_dec_ref(v_s_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1483_);
lean_dec_ref(v_x_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1487_){
_start:
{
lean_object* v_name_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_name_1489_ = lean_ctor_get(v_descr_1487_, 0);
v___f_1490_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1491_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1487_, 4);
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, lean_box(0));
lean_closure_set(v___x_1492_, 3, v_descr_1487_);
v___x_1493_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1493_, 0, lean_box(0));
lean_closure_set(v___x_1493_, 1, lean_box(0));
lean_closure_set(v___x_1493_, 2, lean_box(0));
lean_closure_set(v___x_1493_, 3, v_descr_1487_);
v___x_1494_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1494_, 0, lean_box(0));
lean_closure_set(v___x_1494_, 1, lean_box(0));
lean_closure_set(v___x_1494_, 2, lean_box(0));
lean_closure_set(v___x_1494_, 3, v_descr_1487_);
v___x_1495_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1495_, 0, lean_box(0));
lean_closure_set(v___x_1495_, 1, lean_box(0));
lean_closure_set(v___x_1495_, 2, lean_box(0));
lean_closure_set(v___x_1495_, 3, v_descr_1487_);
v___x_1496_ = lean_box(2);
v___x_1497_ = lean_box(0);
lean_inc(v_name_1489_);
v___x_1498_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1498_, 0, v_name_1489_);
lean_ctor_set(v___x_1498_, 1, v___x_1492_);
lean_ctor_set(v___x_1498_, 2, v___x_1493_);
lean_ctor_set(v___x_1498_, 3, v___x_1494_);
lean_ctor_set(v___x_1498_, 4, v___x_1495_);
lean_ctor_set(v___x_1498_, 5, v___f_1490_);
lean_ctor_set(v___x_1498_, 6, v___x_1496_);
lean_ctor_set(v___x_1498_, 7, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___f_1491_);
v___x_1500_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1513_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1505_ = l_Lean_scopedEnvExtensionsRef;
v___x_1506_ = lean_st_ref_take(v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_descr_1487_);
lean_ctor_set(v___x_1507_, 1, v_a_1501_);
lean_inc_ref(v___x_1507_);
v___x_1508_ = lean_array_push(v___x_1506_, v___x_1507_);
v___x_1509_ = lean_st_ref_set(v___x_1505_, v___x_1508_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1511_ = v___x_1503_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1507_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_descr_1487_);
v_a_1514_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1500_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1500_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_00_u03c3_1527_, lean_object* v_descr_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_00_u03c3_1533_, lean_object* v_descr_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1531_, v_00_u03b2_1532_, v_00_u03c3_1533_, v_descr_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1537_){
_start:
{
lean_object* v_stateStack_1538_; 
v_stateStack_1538_ = lean_ctor_get(v_s_1537_, 0);
if (lean_obj_tag(v_stateStack_1538_) == 0)
{
return v_s_1537_;
}
else
{
lean_object* v_head_1539_; lean_object* v_scopedEntries_1540_; lean_object* v_newEntries_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1559_; 
lean_inc_ref(v_stateStack_1538_);
v_head_1539_ = lean_ctor_get(v_stateStack_1538_, 0);
lean_inc(v_head_1539_);
v_scopedEntries_1540_ = lean_ctor_get(v_s_1537_, 1);
v_newEntries_1541_ = lean_ctor_get(v_s_1537_, 2);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_s_1537_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_s_1537_, 0);
lean_dec(v_unused_1560_);
v___x_1543_ = v_s_1537_;
v_isShared_1544_ = v_isSharedCheck_1559_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_newEntries_1541_);
lean_inc(v_scopedEntries_1540_);
lean_dec(v_s_1537_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1559_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_state_1545_; lean_object* v_activeScopes_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1558_; 
v_state_1545_ = lean_ctor_get(v_head_1539_, 0);
v_activeScopes_1546_ = lean_ctor_get(v_head_1539_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_head_1539_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1548_ = v_head_1539_;
v_isShared_1549_ = v_isSharedCheck_1558_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_activeScopes_1546_);
lean_inc(v_state_1545_);
lean_dec(v_head_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1558_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
uint8_t v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = 1;
if (v_isShared_1549_ == 0)
{
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_state_1545_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_activeScopes_1546_);
v___x_1552_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*2, v___x_1550_);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_stateStack_1538_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1553_);
v___x_1555_ = v___x_1543_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_scopedEntries_1540_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_newEntries_1541_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1562_, lean_object* v_env_1563_){
_start:
{
lean_object* v_ext_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_ext_1564_ = lean_ctor_get(v_ext_1562_, 1);
lean_inc_ref(v_ext_1564_);
lean_dec_ref(v_ext_1562_);
v___f_1565_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1566_ = lean_box(1);
v___x_1567_ = lean_box(0);
v___x_1568_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1564_, v_env_1563_, v___f_1565_, v___x_1566_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_00_u03c3_1571_, lean_object* v_ext_1572_, lean_object* v_env_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1572_, v_env_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1575_){
_start:
{
lean_object* v_stateStack_1576_; 
v_stateStack_1576_ = lean_ctor_get(v_s_1575_, 0);
if (lean_obj_tag(v_stateStack_1576_) == 1)
{
lean_object* v_tail_1577_; 
v_tail_1577_ = lean_ctor_get(v_stateStack_1576_, 1);
if (lean_obj_tag(v_tail_1577_) == 1)
{
lean_object* v_scopedEntries_1578_; lean_object* v_newEntries_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_inc_ref(v_tail_1577_);
v_scopedEntries_1578_ = lean_ctor_get(v_s_1575_, 1);
v_newEntries_1579_ = lean_ctor_get(v_s_1575_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_s_1575_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_s_1575_, 0);
lean_dec(v_unused_1587_);
v___x_1581_ = v_s_1575_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_newEntries_1579_);
lean_inc(v_scopedEntries_1578_);
lean_dec(v_s_1575_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v_tail_1577_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_tail_1577_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_scopedEntries_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_newEntries_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
return v_s_1575_;
}
}
else
{
return v_s_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1589_, lean_object* v_env_1590_){
_start:
{
lean_object* v_ext_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_ext_1591_ = lean_ctor_get(v_ext_1589_, 1);
lean_inc_ref(v_ext_1591_);
lean_dec_ref(v_ext_1589_);
v___f_1592_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1593_ = lean_box(1);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1591_, v_env_1590_, v___f_1592_, v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_00_u03c3_1598_, lean_object* v_ext_1599_, lean_object* v_env_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1599_, v_env_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_zero_1604_; uint8_t v_isZero_1605_; 
v_zero_1604_ = lean_unsigned_to_nat(0u);
v_isZero_1605_ = lean_nat_dec_eq(v_a_1602_, v_zero_1604_);
if (v_isZero_1605_ == 1)
{
return v_a_1603_;
}
else
{
if (lean_obj_tag(v_a_1603_) == 0)
{
return v_a_1603_;
}
else
{
lean_object* v_head_1606_; lean_object* v_tail_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1626_; 
v_head_1606_ = lean_ctor_get(v_a_1603_, 0);
v_tail_1607_ = lean_ctor_get(v_a_1603_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1609_ = v_a_1603_;
v_isShared_1610_ = v_isSharedCheck_1626_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_tail_1607_);
lean_inc(v_head_1606_);
lean_dec(v_a_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1626_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_state_1611_; lean_object* v_activeScopes_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1625_; 
v_state_1611_ = lean_ctor_get(v_head_1606_, 0);
v_activeScopes_1612_ = lean_ctor_get(v_head_1606_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_head_1606_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1614_ = v_head_1606_;
v_isShared_1615_ = v_isSharedCheck_1625_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_activeScopes_1612_);
lean_inc(v_state_1611_);
lean_dec(v_head_1606_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1625_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_one_1616_; lean_object* v_n_1617_; lean_object* v___x_1619_; 
v_one_1616_ = lean_unsigned_to_nat(1u);
v_n_1617_ = lean_nat_sub(v_a_1602_, v_one_1616_);
if (v_isShared_1615_ == 0)
{
v___x_1619_ = v___x_1614_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_state_1611_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_activeScopes_1612_);
v___x_1619_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*2, v_isZero_1605_);
v___x_1620_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1617_, v_tail_1607_);
lean_dec(v_n_1617_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v___x_1620_);
lean_ctor_set(v___x_1609_, 0, v___x_1619_);
v___x_1622_ = v___x_1609_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1627_, v_a_1628_);
lean_dec(v_a_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1631_, v_a_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1638_, lean_object* v_s_1639_){
_start:
{
lean_object* v_stateStack_1640_; lean_object* v_scopedEntries_1641_; lean_object* v_newEntries_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
v_stateStack_1640_ = lean_ctor_get(v_s_1639_, 0);
v_scopedEntries_1641_ = lean_ctor_get(v_s_1639_, 1);
v_newEntries_1642_ = lean_ctor_get(v_s_1639_, 2);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_s_1639_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1644_ = v_s_1639_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_newEntries_1642_);
lean_inc(v_scopedEntries_1641_);
lean_inc(v_stateStack_1640_);
lean_dec(v_s_1639_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1638_, v_stateStack_1640_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_scopedEntries_1641_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_newEntries_1642_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1651_, lean_object* v_s_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1651_, v_s_1652_);
lean_dec(v_depth_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1654_, lean_object* v_env_1655_, lean_object* v_depth_1656_){
_start:
{
lean_object* v_ext_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_ext_1657_ = lean_ctor_get(v_ext_1654_, 1);
lean_inc_ref(v_ext_1657_);
lean_dec_ref(v_ext_1654_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1658_, 0, v_depth_1656_);
v___x_1659_ = lean_box(1);
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1657_, v_env_1655_, v___f_1658_, v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_00_u03c3_1664_, lean_object* v_ext_1665_, lean_object* v_env_1666_, lean_object* v_depth_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1665_, v_env_1666_, v_depth_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1669_, lean_object* v_env_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v_ext_1672_; lean_object* v_toEnvExtension_1673_; lean_object* v_asyncMode_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_ext_1672_ = lean_ctor_get(v_ext_1669_, 1);
lean_inc_ref(v_ext_1672_);
lean_dec_ref(v_ext_1669_);
v_toEnvExtension_1673_ = lean_ctor_get(v_ext_1672_, 0);
v_asyncMode_1674_ = lean_ctor_get(v_toEnvExtension_1673_, 2);
lean_inc(v_asyncMode_1674_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_b_1671_);
v___x_1676_ = lean_box(0);
v___x_1677_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1672_, v_env_1670_, v___x_1675_, v_asyncMode_1674_, v___x_1676_);
lean_dec(v_asyncMode_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_00_u03c3_1680_, lean_object* v_ext_1681_, lean_object* v_env_1682_, lean_object* v_b_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1681_, v_env_1682_, v_b_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1685_, lean_object* v_env_1686_, lean_object* v_namespaceName_1687_, lean_object* v_b_1688_){
_start:
{
lean_object* v_ext_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1700_; 
v_ext_1689_ = lean_ctor_get(v_ext_1685_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_ext_1685_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_ext_1685_, 0);
lean_dec(v_unused_1701_);
v___x_1691_ = v_ext_1685_;
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_ext_1689_);
lean_dec(v_ext_1685_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_toEnvExtension_1693_; lean_object* v_asyncMode_1694_; lean_object* v___x_1696_; 
v_toEnvExtension_1693_ = lean_ctor_get(v_ext_1689_, 0);
v_asyncMode_1694_ = lean_ctor_get(v_toEnvExtension_1693_, 2);
lean_inc(v_asyncMode_1694_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 1);
lean_ctor_set(v___x_1691_, 1, v_b_1688_);
lean_ctor_set(v___x_1691_, 0, v_namespaceName_1687_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_namespaceName_1687_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_b_1688_);
v___x_1696_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1689_, v_env_1686_, v___x_1696_, v_asyncMode_1694_, v___x_1697_);
lean_dec(v_asyncMode_1694_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_00_u03c3_1704_, lean_object* v_ext_1705_, lean_object* v_env_1706_, lean_object* v_namespaceName_1707_, lean_object* v_b_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1705_, v_env_1706_, v_namespaceName_1707_, v_b_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1710_, lean_object* v_states_1711_, lean_object* v_b_1712_){
_start:
{
if (lean_obj_tag(v_states_1711_) == 0)
{
lean_dec(v_b_1712_);
lean_dec_ref(v_ext_1710_);
return v_states_1711_;
}
else
{
lean_object* v_descr_1713_; lean_object* v_head_1714_; lean_object* v_tail_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1738_; 
v_descr_1713_ = lean_ctor_get(v_ext_1710_, 0);
v_head_1714_ = lean_ctor_get(v_states_1711_, 0);
v_tail_1715_ = lean_ctor_get(v_states_1711_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_states_1711_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1717_ = v_states_1711_;
v_isShared_1718_ = v_isSharedCheck_1738_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_tail_1715_);
lean_inc(v_head_1714_);
lean_dec(v_states_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1738_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_addEntry_1719_; lean_object* v_state_1720_; lean_object* v_activeScopes_1721_; uint8_t v_delimitsLocal_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1737_; 
v_addEntry_1719_ = lean_ctor_get(v_descr_1713_, 4);
v_state_1720_ = lean_ctor_get(v_head_1714_, 0);
v_activeScopes_1721_ = lean_ctor_get(v_head_1714_, 1);
v_delimitsLocal_1722_ = lean_ctor_get_uint8(v_head_1714_, sizeof(void*)*2);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_head_1714_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1724_ = v_head_1714_;
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_activeScopes_1721_);
lean_inc(v_state_1720_);
lean_dec(v_head_1714_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v_top_1728_; 
lean_inc(v_addEntry_1719_);
lean_inc(v_b_1712_);
v___x_1726_ = lean_apply_2(v_addEntry_1719_, v_state_1720_, v_b_1712_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v_top_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_activeScopes_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*2, v_delimitsLocal_1722_);
v_top_1728_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
if (v_delimitsLocal_1722_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = l_Lean_stateStackModify___redArg(v_ext_1710_, v_tail_1715_, v_b_1712_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1729_);
lean_ctor_set(v___x_1717_, 0, v_top_1728_);
v___x_1731_ = v___x_1717_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_top_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v_b_1712_);
lean_dec_ref(v_ext_1710_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_top_1728_);
v___x_1734_ = v___x_1717_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_top_1728_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_tail_1715_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_00_u03c3_1741_, lean_object* v_ext_1742_, lean_object* v_states_1743_, lean_object* v_b_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_stateStackModify___redArg(v_ext_1742_, v_states_1743_, v_b_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1746_, lean_object* v_b_1747_, lean_object* v_s_1748_){
_start:
{
lean_object* v_stateStack_1749_; lean_object* v_scopedEntries_1750_; lean_object* v_newEntries_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
v_stateStack_1749_ = lean_ctor_get(v_s_1748_, 0);
v_scopedEntries_1750_ = lean_ctor_get(v_s_1748_, 1);
v_newEntries_1751_ = lean_ctor_get(v_s_1748_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_s_1748_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1753_ = v_s_1748_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_newEntries_1751_);
lean_inc(v_scopedEntries_1750_);
lean_inc(v_stateStack_1749_);
lean_dec(v_s_1748_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Lean_stateStackModify___redArg(v_ext_1746_, v_stateStack_1749_, v_b_1747_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_scopedEntries_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_newEntries_1751_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1760_, lean_object* v_env_1761_, lean_object* v_b_1762_){
_start:
{
lean_object* v_ext_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_ext_1763_ = lean_ctor_get(v_ext_1760_, 1);
lean_inc_ref(v_ext_1763_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1764_, 0, v_ext_1760_);
lean_closure_set(v___f_1764_, 1, v_b_1762_);
v___x_1765_ = lean_box(1);
v___x_1766_ = lean_box(0);
v___x_1767_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1763_, v_env_1761_, v___f_1764_, v___x_1765_, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1768_, lean_object* v_00_u03b2_1769_, lean_object* v_00_u03c3_1770_, lean_object* v_ext_1771_, lean_object* v_env_1772_, lean_object* v_b_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1771_, v_env_1772_, v_b_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1775_, lean_object* v_ext_1776_, lean_object* v_b_1777_, uint8_t v_kind_1778_, lean_object* v_namespaceName_1779_){
_start:
{
switch(v_kind_1778_)
{
case 0:
{
lean_object* v___x_1780_; 
lean_dec(v_namespaceName_1779_);
v___x_1780_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1776_, v_env_1775_, v_b_1777_);
return v___x_1780_;
}
case 1:
{
lean_object* v___x_1781_; 
lean_dec(v_namespaceName_1779_);
v___x_1781_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1776_, v_env_1775_, v_b_1777_);
return v___x_1781_;
}
default: 
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1776_, v_env_1775_, v_namespaceName_1779_, v_b_1777_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1783_, lean_object* v_ext_1784_, lean_object* v_b_1785_, lean_object* v_kind_1786_, lean_object* v_namespaceName_1787_){
_start:
{
uint8_t v_kind_boxed_1788_; lean_object* v_res_1789_; 
v_kind_boxed_1788_ = lean_unbox(v_kind_1786_);
v_res_1789_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1783_, v_ext_1784_, v_b_1785_, v_kind_boxed_1788_, v_namespaceName_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_00_u03c3_1792_, lean_object* v_env_1793_, lean_object* v_ext_1794_, lean_object* v_b_1795_, uint8_t v_kind_1796_, lean_object* v_namespaceName_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1793_, v_ext_1794_, v_b_1795_, v_kind_1796_, v_namespaceName_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_00_u03b2_1800_, lean_object* v_00_u03c3_1801_, lean_object* v_env_1802_, lean_object* v_ext_1803_, lean_object* v_b_1804_, lean_object* v_kind_1805_, lean_object* v_namespaceName_1806_){
_start:
{
uint8_t v_kind_boxed_1807_; lean_object* v_res_1808_; 
v_kind_boxed_1807_ = lean_unbox(v_kind_1805_);
v_res_1808_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1799_, v_00_u03b2_1800_, v_00_u03c3_1801_, v_env_1802_, v_ext_1803_, v_b_1804_, v_kind_boxed_1807_, v_namespaceName_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1809_, lean_object* v_b_1810_, uint8_t v_kind_1811_, lean_object* v_ns_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1813_, v_ext_1809_, v_b_1810_, v_kind_1811_, v_ns_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1815_, lean_object* v_b_1816_, lean_object* v_kind_1817_, lean_object* v_ns_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v_kind_boxed_1820_; lean_object* v_res_1821_; 
v_kind_boxed_1820_ = lean_unbox(v_kind_1817_);
v_res_1821_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1815_, v_b_1816_, v_kind_boxed_1820_, v_ns_1818_, v_x_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1822_, lean_object* v_ext_1823_, lean_object* v_b_1824_, uint8_t v_kind_1825_, lean_object* v_ns_1826_){
_start:
{
lean_object* v_modifyEnv_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v_modifyEnv_1827_ = lean_ctor_get(v_inst_1822_, 1);
lean_inc(v_modifyEnv_1827_);
lean_dec_ref(v_inst_1822_);
v___x_1828_ = lean_box(v_kind_1825_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1829_, 0, v_ext_1823_);
lean_closure_set(v___f_1829_, 1, v_b_1824_);
lean_closure_set(v___f_1829_, 2, v___x_1828_);
lean_closure_set(v___f_1829_, 3, v_ns_1826_);
v___x_1830_ = lean_apply_1(v_modifyEnv_1827_, v___f_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1831_, lean_object* v_ext_1832_, lean_object* v_b_1833_, lean_object* v_kind_1834_, lean_object* v_ns_1835_){
_start:
{
uint8_t v_kind_boxed_1836_; lean_object* v_res_1837_; 
v_kind_boxed_1836_ = lean_unbox(v_kind_1834_);
v_res_1837_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1831_, v_ext_1832_, v_b_1833_, v_kind_boxed_1836_, v_ns_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_ext_1841_, lean_object* v_b_1842_, uint8_t v_kind_1843_){
_start:
{
lean_object* v_toBind_1844_; lean_object* v_getCurrNamespace_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; 
v_toBind_1844_ = lean_ctor_get(v_inst_1838_, 1);
lean_inc(v_toBind_1844_);
lean_dec_ref(v_inst_1838_);
v_getCurrNamespace_1845_ = lean_ctor_get(v_inst_1839_, 0);
lean_inc(v_getCurrNamespace_1845_);
lean_dec_ref(v_inst_1839_);
v___x_1846_ = lean_box(v_kind_1843_);
v___f_1847_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1847_, 0, v_inst_1840_);
lean_closure_set(v___f_1847_, 1, v_ext_1841_);
lean_closure_set(v___f_1847_, 2, v_b_1842_);
lean_closure_set(v___f_1847_, 3, v___x_1846_);
v___x_1848_ = lean_apply_4(v_toBind_1844_, lean_box(0), lean_box(0), v_getCurrNamespace_1845_, v___f_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_ext_1852_, lean_object* v_b_1853_, lean_object* v_kind_1854_){
_start:
{
uint8_t v_kind_boxed_1855_; lean_object* v_res_1856_; 
v_kind_boxed_1855_ = lean_unbox(v_kind_1854_);
v_res_1856_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1849_, v_inst_1850_, v_inst_1851_, v_ext_1852_, v_b_1853_, v_kind_boxed_1855_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1857_, lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_00_u03c3_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_ext_1864_, lean_object* v_b_1865_, uint8_t v_kind_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1861_, v_inst_1862_, v_inst_1863_, v_ext_1864_, v_b_1865_, v_kind_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1868_, lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_00_u03c3_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_ext_1875_, lean_object* v_b_1876_, lean_object* v_kind_1877_){
_start:
{
uint8_t v_kind_boxed_1878_; lean_object* v_res_1879_; 
v_kind_boxed_1878_ = lean_unbox(v_kind_1877_);
v_res_1879_ = l_Lean_ScopedEnvExtension_add(v_m_1868_, v_00_u03b1_1869_, v_00_u03b2_1870_, v_00_u03c3_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_ext_1875_, v_b_1876_, v_kind_boxed_1878_);
return v_res_1879_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1883_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1884_ = lean_unsigned_to_nat(16u);
v___x_1885_ = lean_unsigned_to_nat(209u);
v___x_1886_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1887_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1888_ = l_mkPanicMessageWithDecl(v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_, v___x_1883_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1889_, lean_object* v_ext_1890_, lean_object* v_env_1891_, lean_object* v_asyncMode_1892_){
_start:
{
lean_object* v_ext_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_stateStack_1897_; 
v_ext_1893_ = lean_ctor_get(v_ext_1890_, 1);
v___x_1894_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0);
v___x_1895_ = lean_box(0);
v___x_1896_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1894_, v_ext_1893_, v_env_1891_, v_asyncMode_1892_, v___x_1895_);
v_stateStack_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_stateStack_1897_);
lean_dec(v___x_1896_);
if (lean_obj_tag(v_stateStack_1897_) == 1)
{
lean_object* v_head_1898_; lean_object* v_state_1899_; 
v_head_1898_ = lean_ctor_get(v_stateStack_1897_, 0);
lean_inc(v_head_1898_);
lean_dec_ref_known(v_stateStack_1897_, 2);
v_state_1899_ = lean_ctor_get(v_head_1898_, 0);
lean_inc(v_state_1899_);
lean_dec(v_head_1898_);
return v_state_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v_stateStack_1897_);
v___x_1900_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1901_ = l_panic___redArg(v_inst_1889_, v___x_1900_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1902_, lean_object* v_ext_1903_, lean_object* v_env_1904_, lean_object* v_asyncMode_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1902_, v_ext_1903_, v_env_1904_, v_asyncMode_1905_);
lean_dec(v_asyncMode_1905_);
lean_dec_ref(v_ext_1903_);
lean_dec(v_inst_1902_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1907_, lean_object* v_00_u03b1_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_inst_1910_, lean_object* v_ext_1911_, lean_object* v_env_1912_, lean_object* v_asyncMode_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1910_, v_ext_1911_, v_env_1912_, v_asyncMode_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1915_, lean_object* v_00_u03b1_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_inst_1918_, lean_object* v_ext_1919_, lean_object* v_env_1920_, lean_object* v_asyncMode_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1915_, v_00_u03b1_1916_, v_00_u03b2_1917_, v_inst_1918_, v_ext_1919_, v_env_1920_, v_asyncMode_1921_);
lean_dec(v_asyncMode_1921_);
lean_dec_ref(v_ext_1919_);
lean_dec(v_inst_1918_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1923_, lean_object* v_as_1924_, size_t v_sz_1925_, size_t v_i_1926_, lean_object* v_b_1927_){
_start:
{
uint8_t v___x_1928_; 
v___x_1928_ = lean_usize_dec_lt(v_i_1926_, v_sz_1925_);
if (v___x_1928_ == 0)
{
lean_dec_ref(v_ext_1923_);
return v_b_1927_;
}
else
{
lean_object* v_descr_1929_; lean_object* v_snd_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1944_; 
v_descr_1929_ = lean_ctor_get(v_ext_1923_, 0);
v_snd_1930_ = lean_ctor_get(v_b_1927_, 1);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_b_1927_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v_b_1927_, 0);
lean_dec(v_unused_1945_);
v___x_1932_ = v_b_1927_;
v_isShared_1933_ = v_isSharedCheck_1944_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snd_1930_);
lean_dec(v_b_1927_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1944_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_addEntry_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v_state_1937_; lean_object* v___x_1939_; 
v_addEntry_1934_ = lean_ctor_get(v_descr_1929_, 4);
v___x_1935_ = lean_box(0);
v_a_1936_ = lean_array_uget_borrowed(v_as_1924_, v_i_1926_);
lean_inc(v_addEntry_1934_);
lean_inc(v_a_1936_);
v_state_1937_ = lean_apply_2(v_addEntry_1934_, v_snd_1930_, v_a_1936_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_state_1937_);
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1939_ = v___x_1932_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_state_1937_);
v___x_1939_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
size_t v___x_1940_; size_t v___x_1941_; 
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_add(v_i_1926_, v___x_1940_);
v_i_1926_ = v___x_1941_;
v_b_1927_ = v___x_1939_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1946_, lean_object* v_as_1947_, lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_b_1950_){
_start:
{
size_t v_sz_boxed_1951_; size_t v_i_boxed_1952_; lean_object* v_res_1953_; 
v_sz_boxed_1951_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1952_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1946_, v_as_1947_, v_sz_boxed_1951_, v_i_boxed_1952_, v_b_1950_);
lean_dec_ref(v_as_1947_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1954_, lean_object* v_as_1955_, size_t v_sz_1956_, size_t v_i_1957_, lean_object* v_b_1958_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_lt(v_i_1957_, v_sz_1956_);
if (v___x_1959_ == 0)
{
lean_dec_ref(v_ext_1954_);
return v_b_1958_;
}
else
{
lean_object* v_descr_1960_; lean_object* v_snd_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1975_; 
v_descr_1960_ = lean_ctor_get(v_ext_1954_, 0);
v_snd_1961_ = lean_ctor_get(v_b_1958_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_b_1958_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_b_1958_, 0);
lean_dec(v_unused_1976_);
v___x_1963_ = v_b_1958_;
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snd_1961_);
lean_dec(v_b_1958_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_addEntry_1965_; lean_object* v___x_1966_; lean_object* v_a_1967_; lean_object* v_state_1968_; lean_object* v___x_1970_; 
v_addEntry_1965_ = lean_ctor_get(v_descr_1960_, 4);
v___x_1966_ = lean_box(0);
v_a_1967_ = lean_array_uget_borrowed(v_as_1955_, v_i_1957_);
lean_inc(v_addEntry_1965_);
lean_inc(v_a_1967_);
v_state_1968_ = lean_apply_2(v_addEntry_1965_, v_snd_1961_, v_a_1967_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v_state_1968_);
lean_ctor_set(v___x_1963_, 0, v___x_1966_);
v___x_1970_ = v___x_1963_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_state_1968_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1957_, v___x_1971_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1954_, v_as_1955_, v_sz_1956_, v___x_1972_, v___x_1970_);
return v___x_1973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1977_, lean_object* v_as_1978_, lean_object* v_sz_1979_, lean_object* v_i_1980_, lean_object* v_b_1981_){
_start:
{
size_t v_sz_boxed_1982_; size_t v_i_boxed_1983_; lean_object* v_res_1984_; 
v_sz_boxed_1982_ = lean_unbox_usize(v_sz_1979_);
lean_dec(v_sz_1979_);
v_i_boxed_1983_ = lean_unbox_usize(v_i_1980_);
lean_dec(v_i_1980_);
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1977_, v_as_1978_, v_sz_boxed_1982_, v_i_boxed_1983_, v_b_1981_);
lean_dec_ref(v_as_1978_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_1985_, lean_object* v_ext_1986_, lean_object* v_n_1987_, lean_object* v_b_1988_){
_start:
{
if (lean_obj_tag(v_n_1987_) == 0)
{
lean_object* v_cs_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; size_t v_sz_1992_; size_t v___x_1993_; lean_object* v___x_1994_; lean_object* v_fst_1995_; 
v_cs_1989_ = lean_ctor_get(v_n_1987_, 0);
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_b_1988_);
v_sz_1992_ = lean_array_size(v_cs_1989_);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_1985_, v_ext_1986_, v_cs_1989_, v_sz_1992_, v___x_1993_, v___x_1991_);
v_fst_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_fst_1995_);
if (lean_obj_tag(v_fst_1995_) == 0)
{
lean_object* v_snd_1996_; lean_object* v___x_1997_; 
v_snd_1996_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_snd_1996_);
lean_dec_ref(v___x_1994_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_snd_1996_);
return v___x_1997_;
}
else
{
lean_object* v_val_1998_; 
lean_dec_ref(v___x_1994_);
v_val_1998_ = lean_ctor_get(v_fst_1995_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_fst_1995_, 1);
return v_val_1998_;
}
}
else
{
lean_object* v_vs_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; lean_object* v_fst_2005_; 
v_vs_1999_ = lean_ctor_get(v_n_1987_, 0);
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_b_1988_);
v_sz_2002_ = lean_array_size(v_vs_1999_);
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1986_, v_vs_1999_, v_sz_2002_, v___x_2003_, v___x_2001_);
v_fst_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_fst_2005_);
if (lean_obj_tag(v_fst_2005_) == 0)
{
lean_object* v_snd_2006_; lean_object* v___x_2007_; 
v_snd_2006_ = lean_ctor_get(v___x_2004_, 1);
lean_inc(v_snd_2006_);
lean_dec_ref(v___x_2004_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_snd_2006_);
return v___x_2007_;
}
else
{
lean_object* v_val_2008_; 
lean_dec_ref(v___x_2004_);
v_val_2008_ = lean_ctor_get(v_fst_2005_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_fst_2005_, 1);
return v_val_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2009_, lean_object* v_ext_2010_, lean_object* v_as_2011_, size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_b_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_lt(v_i_2013_, v_sz_2012_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v_ext_2010_);
return v_b_2014_;
}
else
{
lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2034_; 
v_snd_2016_ = lean_ctor_get(v_b_2014_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_b_2014_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_b_2014_, 0);
lean_dec(v_unused_2035_);
v___x_2018_ = v_b_2014_;
v_isShared_2019_ = v_isSharedCheck_2034_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_dec(v_b_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2034_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_array_uget_borrowed(v_as_2011_, v_i_2013_);
lean_inc(v_snd_2016_);
lean_inc_ref(v_ext_2010_);
v___x_2021_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2009_, v_ext_2010_, v_a_2020_, v_snd_2016_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_dec_ref(v_ext_2010_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2022_);
v___x_2024_ = v___x_2018_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_snd_2016_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec(v_snd_2016_);
v_a_2026_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2027_ = lean_box(0);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v_a_2026_);
lean_ctor_set(v___x_2018_, 0, v___x_2027_);
v___x_2029_ = v___x_2018_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_a_2026_);
v___x_2029_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
size_t v___x_2030_; size_t v___x_2031_; 
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2013_, v___x_2030_);
v_i_2013_ = v___x_2031_;
v_b_2014_ = v___x_2029_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2036_, lean_object* v_ext_2037_, lean_object* v_as_2038_, lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_b_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2036_, v_ext_2037_, v_as_2038_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2041_);
lean_dec_ref(v_as_2038_);
lean_dec(v_init_2036_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2045_, lean_object* v_ext_2046_, lean_object* v_n_2047_, lean_object* v_b_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2045_, v_ext_2046_, v_n_2047_, v_b_2048_);
lean_dec_ref(v_n_2047_);
lean_dec(v_init_2045_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2050_, lean_object* v_as_2051_, size_t v_sz_2052_, size_t v_i_2053_, lean_object* v_b_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
if (v___x_2055_ == 0)
{
lean_dec_ref(v_ext_2050_);
return v_b_2054_;
}
else
{
lean_object* v_descr_2056_; lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2071_; 
v_descr_2056_ = lean_ctor_get(v_ext_2050_, 0);
v_snd_2057_ = lean_ctor_get(v_b_2054_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_b_2054_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_b_2054_, 0);
lean_dec(v_unused_2072_);
v___x_2059_ = v_b_2054_;
v_isShared_2060_ = v_isSharedCheck_2071_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_dec(v_b_2054_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2071_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_addEntry_2061_; lean_object* v___x_2062_; lean_object* v_a_2063_; lean_object* v_state_2064_; lean_object* v___x_2066_; 
v_addEntry_2061_ = lean_ctor_get(v_descr_2056_, 4);
v___x_2062_ = lean_box(0);
v_a_2063_ = lean_array_uget_borrowed(v_as_2051_, v_i_2053_);
lean_inc(v_addEntry_2061_);
lean_inc(v_a_2063_);
v_state_2064_ = lean_apply_2(v_addEntry_2061_, v_snd_2057_, v_a_2063_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v_state_2064_);
lean_ctor_set(v___x_2059_, 0, v___x_2062_);
v___x_2066_ = v___x_2059_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_state_2064_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
size_t v___x_2067_; size_t v___x_2068_; 
v___x_2067_ = ((size_t)1ULL);
v___x_2068_ = lean_usize_add(v_i_2053_, v___x_2067_);
v_i_2053_ = v___x_2068_;
v_b_2054_ = v___x_2066_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2073_, lean_object* v_as_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_b_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2073_, v_as_2074_, v_sz_boxed_2078_, v_i_boxed_2079_, v_b_2077_);
lean_dec_ref(v_as_2074_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2081_, lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v_ext_2081_);
return v_b_2085_;
}
else
{
lean_object* v_descr_2087_; lean_object* v_snd_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2102_; 
v_descr_2087_ = lean_ctor_get(v_ext_2081_, 0);
v_snd_2088_ = lean_ctor_get(v_b_2085_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; 
v_unused_2103_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2103_);
v___x_2090_ = v_b_2085_;
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_snd_2088_);
lean_dec(v_b_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_addEntry_2092_; lean_object* v___x_2093_; lean_object* v_a_2094_; lean_object* v_state_2095_; lean_object* v___x_2097_; 
v_addEntry_2092_ = lean_ctor_get(v_descr_2087_, 4);
v___x_2093_ = lean_box(0);
v_a_2094_ = lean_array_uget_borrowed(v_as_2082_, v_i_2084_);
lean_inc(v_addEntry_2092_);
lean_inc(v_a_2094_);
v_state_2095_ = lean_apply_2(v_addEntry_2092_, v_snd_2088_, v_a_2094_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v_state_2095_);
lean_ctor_set(v___x_2090_, 0, v___x_2093_);
v___x_2097_ = v___x_2090_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_state_2095_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_2084_, v___x_2098_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2081_, v_as_2082_, v_sz_2083_, v___x_2099_, v___x_2097_);
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2104_, lean_object* v_as_2105_, lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_b_2108_){
_start:
{
size_t v_sz_boxed_2109_; size_t v_i_boxed_2110_; lean_object* v_res_2111_; 
v_sz_boxed_2109_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2110_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2104_, v_as_2105_, v_sz_boxed_2109_, v_i_boxed_2110_, v_b_2108_);
lean_dec_ref(v_as_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2112_, lean_object* v_t_2113_, lean_object* v_init_2114_){
_start:
{
lean_object* v_root_2115_; lean_object* v_tail_2116_; lean_object* v___x_2117_; 
v_root_2115_ = lean_ctor_get(v_t_2113_, 0);
v_tail_2116_ = lean_ctor_get(v_t_2113_, 1);
lean_inc_ref(v_ext_2112_);
lean_inc(v_init_2114_);
v___x_2117_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2114_, v_ext_2112_, v_root_2115_, v_init_2114_);
lean_dec(v_init_2114_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; 
lean_dec_ref(v_ext_2112_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
return v_a_2118_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; size_t v_sz_2122_; size_t v___x_2123_; lean_object* v___x_2124_; lean_object* v_fst_2125_; 
v_a_2119_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_a_2119_);
v_sz_2122_ = lean_array_size(v_tail_2116_);
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2112_, v_tail_2116_, v_sz_2122_, v___x_2123_, v___x_2121_);
v_fst_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_fst_2125_);
if (lean_obj_tag(v_fst_2125_) == 0)
{
lean_object* v_snd_2126_; 
v_snd_2126_ = lean_ctor_get(v___x_2124_, 1);
lean_inc(v_snd_2126_);
lean_dec_ref(v___x_2124_);
return v_snd_2126_;
}
else
{
lean_object* v_val_2127_; 
lean_dec_ref(v___x_2124_);
v_val_2127_ = lean_ctor_get(v_fst_2125_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v_fst_2125_, 1);
return v_val_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2128_, lean_object* v_t_2129_, lean_object* v_init_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2128_, v_t_2129_, v_init_2130_);
lean_dec_ref(v_t_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2132_, lean_object* v_ext_2133_, lean_object* v_s_2134_){
_start:
{
lean_object* v_stateStack_2135_; 
v_stateStack_2135_ = lean_ctor_get(v_s_2134_, 0);
lean_inc(v_stateStack_2135_);
if (lean_obj_tag(v_stateStack_2135_) == 1)
{
lean_object* v_scopedEntries_2136_; lean_object* v_newEntries_2137_; lean_object* v_head_2138_; lean_object* v_tail_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2168_; 
v_scopedEntries_2136_ = lean_ctor_get(v_s_2134_, 1);
v_newEntries_2137_ = lean_ctor_get(v_s_2134_, 2);
v_head_2138_ = lean_ctor_get(v_stateStack_2135_, 0);
v_tail_2139_ = lean_ctor_get(v_stateStack_2135_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_stateStack_2135_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2141_ = v_stateStack_2135_;
v_isShared_2142_ = v_isSharedCheck_2168_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_tail_2139_);
lean_inc(v_head_2138_);
lean_dec(v_stateStack_2135_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2168_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___y_2144_; lean_object* v_state_2149_; lean_object* v_activeScopes_2150_; uint8_t v_delimitsLocal_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2167_; 
v_state_2149_ = lean_ctor_get(v_head_2138_, 0);
v_activeScopes_2150_ = lean_ctor_get(v_head_2138_, 1);
v_delimitsLocal_2151_ = lean_ctor_get_uint8(v_head_2138_, sizeof(void*)*2);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_head_2138_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2153_ = v_head_2138_;
v_isShared_2154_ = v_isSharedCheck_2167_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_activeScopes_2150_);
lean_inc(v_state_2149_);
lean_dec(v_head_2138_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2167_;
goto v_resetjp_2152_;
}
v___jp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___y_2144_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___y_2144_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_tail_2139_);
v___x_2146_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_scopedEntries_2136_);
lean_ctor_set(v___x_2147_, 2, v_newEntries_2137_);
return v___x_2147_;
}
}
v_resetjp_2152_:
{
uint8_t v___x_2155_; 
v___x_2155_ = l_Lean_NameSet_contains(v_activeScopes_2150_, v_namespaceName_2132_);
if (v___x_2155_ == 0)
{
lean_object* v_activeScopes_2156_; lean_object* v___x_2157_; 
lean_inc(v_newEntries_2137_);
lean_inc_ref(v_scopedEntries_2136_);
lean_dec_ref(v_s_2134_);
lean_inc(v_namespaceName_2132_);
v_activeScopes_2156_ = l_Lean_NameSet_insert(v_activeScopes_2150_, v_namespaceName_2132_);
v___x_2157_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2136_, v_namespaceName_2132_);
lean_dec(v_namespaceName_2132_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2159_; 
lean_dec_ref(v_ext_2133_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_activeScopes_2156_);
v___x_2159_ = v___x_2153_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_state_2149_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_activeScopes_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2160_, sizeof(void*)*2, v_delimitsLocal_2151_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v___y_2144_ = v___x_2159_;
goto v___jp_2143_;
}
}
else
{
lean_object* v_val_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v_val_2161_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2162_ = 1;
v___x_2163_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2133_, v_val_2161_, v_state_2149_);
lean_dec(v_val_2161_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_activeScopes_2156_);
lean_ctor_set(v___x_2153_, 0, v___x_2163_);
v___x_2165_ = v___x_2153_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_activeScopes_2156_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*2, v___x_2162_);
v___y_2144_ = v___x_2165_;
goto v___jp_2143_;
}
}
}
else
{
lean_del_object(v___x_2153_);
lean_dec(v_activeScopes_2150_);
lean_dec(v_state_2149_);
lean_del_object(v___x_2141_);
lean_dec(v_tail_2139_);
lean_dec_ref(v_ext_2133_);
lean_dec(v_namespaceName_2132_);
return v_s_2134_;
}
}
}
}
else
{
lean_dec(v_stateStack_2135_);
lean_dec_ref(v_ext_2133_);
lean_dec(v_namespaceName_2132_);
return v_s_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2169_, lean_object* v_env_2170_, lean_object* v_namespaceName_2171_){
_start:
{
lean_object* v_ext_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_ext_2172_ = lean_ctor_get(v_ext_2169_, 1);
lean_inc_ref(v_ext_2172_);
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2173_, 0, v_namespaceName_2171_);
lean_closure_set(v___f_2173_, 1, v_ext_2169_);
v___x_2174_ = lean_box(1);
v___x_2175_ = lean_box(0);
v___x_2176_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2172_, v_env_2170_, v___f_2173_, v___x_2174_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2177_, lean_object* v_00_u03b2_2178_, lean_object* v_00_u03c3_2179_, lean_object* v_ext_2180_, lean_object* v_env_2181_, lean_object* v_namespaceName_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2180_, v_env_2181_, v_namespaceName_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2184_, lean_object* v_00_u03c3_2185_, lean_object* v_00_u03b1_2186_, lean_object* v_ext_2187_, lean_object* v_t_2188_, lean_object* v_init_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2187_, v_t_2188_, v_init_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_00_u03c3_2192_, lean_object* v_00_u03b1_2193_, lean_object* v_ext_2194_, lean_object* v_t_2195_, lean_object* v_init_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2191_, v_00_u03c3_2192_, v_00_u03b1_2193_, v_ext_2194_, v_t_2195_, v_init_2196_);
lean_dec_ref(v_t_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2198_, lean_object* v_00_u03c3_2199_, lean_object* v_init_2200_, lean_object* v_00_u03b1_2201_, lean_object* v_ext_2202_, lean_object* v_n_2203_, lean_object* v_b_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2200_, v_ext_2202_, v_n_2203_, v_b_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2206_, lean_object* v_00_u03c3_2207_, lean_object* v_init_2208_, lean_object* v_00_u03b1_2209_, lean_object* v_ext_2210_, lean_object* v_n_2211_, lean_object* v_b_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2206_, v_00_u03c3_2207_, v_init_2208_, v_00_u03b1_2209_, v_ext_2210_, v_n_2211_, v_b_2212_);
lean_dec_ref(v_n_2211_);
lean_dec(v_init_2208_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2214_, lean_object* v_00_u03c3_2215_, lean_object* v_00_u03b1_2216_, lean_object* v_ext_2217_, lean_object* v_as_2218_, size_t v_sz_2219_, size_t v_i_2220_, lean_object* v_b_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2217_, v_as_2218_, v_sz_2219_, v_i_2220_, v_b_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2223_, lean_object* v_00_u03c3_2224_, lean_object* v_00_u03b1_2225_, lean_object* v_ext_2226_, lean_object* v_as_2227_, lean_object* v_sz_2228_, lean_object* v_i_2229_, lean_object* v_b_2230_){
_start:
{
size_t v_sz_boxed_2231_; size_t v_i_boxed_2232_; lean_object* v_res_2233_; 
v_sz_boxed_2231_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2232_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2223_, v_00_u03c3_2224_, v_00_u03b1_2225_, v_ext_2226_, v_as_2227_, v_sz_boxed_2231_, v_i_boxed_2232_, v_b_2230_);
lean_dec_ref(v_as_2227_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2234_, lean_object* v_00_u03c3_2235_, lean_object* v_init_2236_, lean_object* v_00_u03b1_2237_, lean_object* v_ext_2238_, lean_object* v_as_2239_, size_t v_sz_2240_, size_t v_i_2241_, lean_object* v_b_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2236_, v_ext_2238_, v_as_2239_, v_sz_2240_, v_i_2241_, v_b_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2244_, lean_object* v_00_u03c3_2245_, lean_object* v_init_2246_, lean_object* v_00_u03b1_2247_, lean_object* v_ext_2248_, lean_object* v_as_2249_, lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_b_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2244_, v_00_u03c3_2245_, v_init_2246_, v_00_u03b1_2247_, v_ext_2248_, v_as_2249_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2252_);
lean_dec_ref(v_as_2249_);
lean_dec(v_init_2246_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2256_, lean_object* v_00_u03c3_2257_, lean_object* v_00_u03b1_2258_, lean_object* v_ext_2259_, lean_object* v_as_2260_, size_t v_sz_2261_, size_t v_i_2262_, lean_object* v_b_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2259_, v_as_2260_, v_sz_2261_, v_i_2262_, v_b_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2265_, lean_object* v_00_u03c3_2266_, lean_object* v_00_u03b1_2267_, lean_object* v_ext_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2265_, v_00_u03c3_2266_, v_00_u03b1_2267_, v_ext_2268_, v_as_2269_, v_sz_boxed_2273_, v_i_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2276_, lean_object* v_00_u03c3_2277_, lean_object* v_00_u03b1_2278_, lean_object* v_ext_2279_, lean_object* v_as_2280_, size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_b_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2279_, v_as_2280_, v_sz_2281_, v_i_2282_, v_b_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_00_u03c3_2286_, lean_object* v_00_u03b1_2287_, lean_object* v_ext_2288_, lean_object* v_as_2289_, lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_b_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2285_, v_00_u03c3_2286_, v_00_u03b1_2287_, v_ext_2288_, v_as_2289_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2292_);
lean_dec_ref(v_as_2289_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2296_, lean_object* v_00_u03c3_2297_, lean_object* v_00_u03b1_2298_, lean_object* v_ext_2299_, lean_object* v_as_2300_, size_t v_sz_2301_, size_t v_i_2302_, lean_object* v_b_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2299_, v_as_2300_, v_sz_2301_, v_i_2302_, v_b_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_00_u03c3_2306_, lean_object* v_00_u03b1_2307_, lean_object* v_ext_2308_, lean_object* v_as_2309_, lean_object* v_sz_2310_, lean_object* v_i_2311_, lean_object* v_b_2312_){
_start:
{
size_t v_sz_boxed_2313_; size_t v_i_boxed_2314_; lean_object* v_res_2315_; 
v_sz_boxed_2313_ = lean_unbox_usize(v_sz_2310_);
lean_dec(v_sz_2310_);
v_i_boxed_2314_ = lean_unbox_usize(v_i_2311_);
lean_dec(v_i_2311_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2305_, v_00_u03c3_2306_, v_00_u03b1_2307_, v_ext_2308_, v_as_2309_, v_sz_boxed_2313_, v_i_boxed_2314_, v_b_2312_);
lean_dec_ref(v_as_2309_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2316_, lean_object* v_s_2317_){
_start:
{
lean_object* v_stateStack_2318_; 
v_stateStack_2318_ = lean_ctor_get(v_s_2317_, 0);
lean_inc(v_stateStack_2318_);
if (lean_obj_tag(v_stateStack_2318_) == 1)
{
lean_object* v_head_2319_; lean_object* v_scopedEntries_2320_; lean_object* v_newEntries_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2348_; 
v_head_2319_ = lean_ctor_get(v_stateStack_2318_, 0);
lean_inc(v_head_2319_);
v_scopedEntries_2320_ = lean_ctor_get(v_s_2317_, 1);
v_newEntries_2321_ = lean_ctor_get(v_s_2317_, 2);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_s_2317_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; 
v_unused_2349_ = lean_ctor_get(v_s_2317_, 0);
lean_dec(v_unused_2349_);
v___x_2323_ = v_s_2317_;
v_isShared_2324_ = v_isSharedCheck_2348_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_newEntries_2321_);
lean_inc(v_scopedEntries_2320_);
lean_dec(v_s_2317_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2348_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_tail_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2346_; 
v_tail_2325_ = lean_ctor_get(v_stateStack_2318_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_stateStack_2318_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_stateStack_2318_, 0);
lean_dec(v_unused_2347_);
v___x_2327_ = v_stateStack_2318_;
v_isShared_2328_ = v_isSharedCheck_2346_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_tail_2325_);
lean_dec(v_stateStack_2318_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2346_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_state_2329_; lean_object* v_activeScopes_2330_; uint8_t v_delimitsLocal_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2345_; 
v_state_2329_ = lean_ctor_get(v_head_2319_, 0);
v_activeScopes_2330_ = lean_ctor_get(v_head_2319_, 1);
v_delimitsLocal_2331_ = lean_ctor_get_uint8(v_head_2319_, sizeof(void*)*2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_head_2319_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2333_ = v_head_2319_;
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_activeScopes_2330_);
lean_inc(v_state_2329_);
lean_dec(v_head_2319_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_apply_1(v_f_2316_, v_state_2329_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2335_);
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_activeScopes_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, sizeof(void*)*2, v_delimitsLocal_2331_);
v___x_2337_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2337_);
v___x_2339_ = v___x_2327_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_tail_2325_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2339_);
v___x_2341_ = v___x_2323_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_scopedEntries_2320_);
lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_newEntries_2321_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2318_);
lean_dec(v_f_2316_);
return v_s_2317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2350_, lean_object* v_env_2351_, lean_object* v_f_2352_){
_start:
{
lean_object* v_ext_2353_; lean_object* v_toEnvExtension_2354_; lean_object* v_asyncMode_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_ext_2353_ = lean_ctor_get(v_ext_2350_, 1);
lean_inc_ref(v_ext_2353_);
lean_dec_ref(v_ext_2350_);
v_toEnvExtension_2354_ = lean_ctor_get(v_ext_2353_, 0);
v_asyncMode_2355_ = lean_ctor_get(v_toEnvExtension_2354_, 2);
lean_inc(v_asyncMode_2355_);
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2356_, 0, v_f_2352_);
v___x_2357_ = lean_box(0);
v___x_2358_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2353_, v_env_2351_, v___f_2356_, v_asyncMode_2355_, v___x_2357_);
lean_dec(v_asyncMode_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_00_u03c3_2361_, lean_object* v_ext_2362_, lean_object* v_env_2363_, lean_object* v_f_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2362_, v_env_2363_, v_f_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2366_, lean_object* v_____s_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_apply_2(v_toPure_2366_, lean_box(0), v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2370_, lean_object* v_toPure_2371_, lean_object* v_r_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2370_);
v___x_2374_ = lean_apply_2(v_toPure_2371_, lean_box(0), v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2375_, lean_object* v_toBind_2376_, lean_object* v___f_2377_, lean_object* v_a_2378_, lean_object* v_x_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_modifyEnv_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_modifyEnv_2381_ = lean_ctor_get(v_inst_2375_, 1);
lean_inc(v_modifyEnv_2381_);
lean_dec_ref(v_inst_2375_);
v___x_2382_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2382_, 0, lean_box(0));
lean_closure_set(v___x_2382_, 1, lean_box(0));
lean_closure_set(v___x_2382_, 2, lean_box(0));
lean_closure_set(v___x_2382_, 3, v_a_2378_);
v___x_2383_ = lean_apply_1(v_modifyEnv_2381_, v___x_2382_);
v___x_2384_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v___x_2383_, v___f_2377_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2385_, lean_object* v_inst_2386_, lean_object* v_toBind_2387_, lean_object* v_inst_2388_, lean_object* v___f_2389_, lean_object* v_____do__lift_2390_){
_start:
{
lean_object* v___x_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2391_ = lean_box(0);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2392_, 0, v___x_2391_);
lean_closure_set(v___f_2392_, 1, v_toPure_2385_);
lean_inc(v_toBind_2387_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2393_, 0, v_inst_2386_);
lean_closure_set(v___f_2393_, 1, v_toBind_2387_);
lean_closure_set(v___f_2393_, 2, v___f_2392_);
v_sz_2394_ = lean_array_size(v_____do__lift_2390_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2388_, v_____do__lift_2390_, v___f_2393_, v_sz_2394_, v___x_2395_, v___x_2391_);
v___x_2397_ = lean_apply_4(v_toBind_2387_, lean_box(0), lean_box(0), v___x_2396_, v___f_2389_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_scopedEnvExtensionsRef;
v___x_2399_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2399_, 0, lean_box(0));
lean_closure_set(v___x_2399_, 1, lean_box(0));
lean_closure_set(v___x_2399_, 2, v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_){
_start:
{
lean_object* v_toApplicative_2403_; lean_object* v_toBind_2404_; lean_object* v_toPure_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; 
v_toApplicative_2403_ = lean_ctor_get(v_inst_2400_, 0);
v_toBind_2404_ = lean_ctor_get(v_inst_2400_, 1);
lean_inc_n(v_toBind_2404_, 2);
v_toPure_2405_ = lean_ctor_get(v_toApplicative_2403_, 1);
lean_inc_n(v_toPure_2405_, 2);
v___x_2406_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2407_ = lean_apply_2(v_inst_2402_, lean_box(0), v___x_2406_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2408_, 0, v_toPure_2405_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2409_, 0, v_toPure_2405_);
lean_closure_set(v___f_2409_, 1, v_inst_2401_);
lean_closure_set(v___f_2409_, 2, v_toBind_2404_);
lean_closure_set(v___f_2409_, 3, v_inst_2400_);
lean_closure_set(v___f_2409_, 4, v___f_2408_);
v___x_2410_ = lean_apply_4(v_toBind_2404_, lean_box(0), lean_box(0), v___x_2407_, v___f_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_pushScope___redArg(v_inst_2412_, v_inst_2413_, v_inst_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2416_, lean_object* v_toBind_2417_, lean_object* v___f_2418_, lean_object* v_a_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_modifyEnv_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_modifyEnv_2422_ = lean_ctor_get(v_inst_2416_, 1);
lean_inc(v_modifyEnv_2422_);
lean_dec_ref(v_inst_2416_);
v___x_2423_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2423_, 0, lean_box(0));
lean_closure_set(v___x_2423_, 1, lean_box(0));
lean_closure_set(v___x_2423_, 2, lean_box(0));
lean_closure_set(v___x_2423_, 3, v_a_2419_);
v___x_2424_ = lean_apply_1(v_modifyEnv_2422_, v___x_2423_);
v___x_2425_ = lean_apply_4(v_toBind_2417_, lean_box(0), lean_box(0), v___x_2424_, v___f_2418_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2426_, lean_object* v_inst_2427_, lean_object* v_toBind_2428_, lean_object* v_inst_2429_, lean_object* v___f_2430_, lean_object* v_____do__lift_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___f_2434_; size_t v_sz_2435_; size_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2432_ = lean_box(0);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2433_, 0, v___x_2432_);
lean_closure_set(v___f_2433_, 1, v_toPure_2426_);
lean_inc(v_toBind_2428_);
v___f_2434_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2434_, 0, v_inst_2427_);
lean_closure_set(v___f_2434_, 1, v_toBind_2428_);
lean_closure_set(v___f_2434_, 2, v___f_2433_);
v_sz_2435_ = lean_array_size(v_____do__lift_2431_);
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2429_, v_____do__lift_2431_, v___f_2434_, v_sz_2435_, v___x_2436_, v___x_2432_);
v___x_2438_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v___x_2437_, v___f_2430_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_){
_start:
{
lean_object* v_toApplicative_2442_; lean_object* v_toBind_2443_; lean_object* v_toPure_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; 
v_toApplicative_2442_ = lean_ctor_get(v_inst_2439_, 0);
v_toBind_2443_ = lean_ctor_get(v_inst_2439_, 1);
lean_inc_n(v_toBind_2443_, 2);
v_toPure_2444_ = lean_ctor_get(v_toApplicative_2442_, 1);
lean_inc_n(v_toPure_2444_, 2);
v___x_2445_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2446_ = lean_apply_2(v_inst_2441_, lean_box(0), v___x_2445_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2447_, 0, v_toPure_2444_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2448_, 0, v_toPure_2444_);
lean_closure_set(v___f_2448_, 1, v_inst_2440_);
lean_closure_set(v___f_2448_, 2, v_toBind_2443_);
lean_closure_set(v___f_2448_, 3, v_inst_2439_);
lean_closure_set(v___f_2448_, 4, v___f_2447_);
v___x_2449_ = lean_apply_4(v_toBind_2443_, lean_box(0), lean_box(0), v___x_2446_, v___f_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_popScope___redArg(v_inst_2451_, v_inst_2452_, v_inst_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2455_, lean_object* v_depth_2456_, lean_object* v_x_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2455_, v_x_2457_, v_depth_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2459_, lean_object* v_depth_2460_, lean_object* v_toBind_2461_, lean_object* v___f_2462_, lean_object* v_a_2463_, lean_object* v_x_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_modifyEnv_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_modifyEnv_2466_ = lean_ctor_get(v_inst_2459_, 1);
lean_inc(v_modifyEnv_2466_);
lean_dec_ref(v_inst_2459_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2467_, 0, v_a_2463_);
lean_closure_set(v___f_2467_, 1, v_depth_2460_);
v___x_2468_ = lean_apply_1(v_modifyEnv_2466_, v___f_2467_);
v___x_2469_ = lean_apply_4(v_toBind_2461_, lean_box(0), lean_box(0), v___x_2468_, v___f_2462_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2470_, lean_object* v_inst_2471_, lean_object* v_depth_2472_, lean_object* v_toBind_2473_, lean_object* v_inst_2474_, lean_object* v___f_2475_, lean_object* v_____do__lift_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___f_2478_; lean_object* v___f_2479_; size_t v_sz_2480_; size_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2477_ = lean_box(0);
v___f_2478_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2478_, 0, v___x_2477_);
lean_closure_set(v___f_2478_, 1, v_toPure_2470_);
lean_inc(v_toBind_2473_);
v___f_2479_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2479_, 0, v_inst_2471_);
lean_closure_set(v___f_2479_, 1, v_depth_2472_);
lean_closure_set(v___f_2479_, 2, v_toBind_2473_);
lean_closure_set(v___f_2479_, 3, v___f_2478_);
v_sz_2480_ = lean_array_size(v_____do__lift_2476_);
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2474_, v_____do__lift_2476_, v___f_2479_, v_sz_2480_, v___x_2481_, v___x_2477_);
v___x_2483_ = lean_apply_4(v_toBind_2473_, lean_box(0), lean_box(0), v___x_2482_, v___f_2475_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_depth_2487_){
_start:
{
lean_object* v_toApplicative_2488_; lean_object* v_toBind_2489_; lean_object* v_toPure_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___f_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; 
v_toApplicative_2488_ = lean_ctor_get(v_inst_2484_, 0);
v_toBind_2489_ = lean_ctor_get(v_inst_2484_, 1);
lean_inc_n(v_toBind_2489_, 2);
v_toPure_2490_ = lean_ctor_get(v_toApplicative_2488_, 1);
lean_inc_n(v_toPure_2490_, 2);
v___x_2491_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2492_ = lean_apply_2(v_inst_2486_, lean_box(0), v___x_2491_);
v___f_2493_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2493_, 0, v_toPure_2490_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2494_, 0, v_toPure_2490_);
lean_closure_set(v___f_2494_, 1, v_inst_2485_);
lean_closure_set(v___f_2494_, 2, v_depth_2487_);
lean_closure_set(v___f_2494_, 3, v_toBind_2489_);
lean_closure_set(v___f_2494_, 4, v_inst_2484_);
lean_closure_set(v___f_2494_, 5, v___f_2493_);
v___x_2495_ = lean_apply_4(v_toBind_2489_, lean_box(0), lean_box(0), v___x_2492_, v___f_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_depth_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_setDelimitsLocal___redArg(v_inst_2497_, v_inst_2498_, v_inst_2499_, v_depth_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2502_, lean_object* v_namespaceName_2503_, lean_object* v_x_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2502_, v_x_2504_, v_namespaceName_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2506_, lean_object* v_namespaceName_2507_, lean_object* v_toBind_2508_, lean_object* v___f_2509_, lean_object* v_a_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_modifyEnv_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_modifyEnv_2513_ = lean_ctor_get(v_inst_2506_, 1);
lean_inc(v_modifyEnv_2513_);
lean_dec_ref(v_inst_2506_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2514_, 0, v_a_2510_);
lean_closure_set(v___f_2514_, 1, v_namespaceName_2507_);
v___x_2515_ = lean_apply_1(v_modifyEnv_2513_, v___f_2514_);
v___x_2516_ = lean_apply_4(v_toBind_2508_, lean_box(0), lean_box(0), v___x_2515_, v___f_2509_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2517_, lean_object* v_inst_2518_, lean_object* v_namespaceName_2519_, lean_object* v_toBind_2520_, lean_object* v_inst_2521_, lean_object* v___f_2522_, lean_object* v_____do__lift_2523_){
_start:
{
lean_object* v___x_2524_; lean_object* v___f_2525_; lean_object* v___f_2526_; size_t v_sz_2527_; size_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2524_ = lean_box(0);
v___f_2525_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2525_, 0, v___x_2524_);
lean_closure_set(v___f_2525_, 1, v_toPure_2517_);
lean_inc(v_toBind_2520_);
v___f_2526_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2526_, 0, v_inst_2518_);
lean_closure_set(v___f_2526_, 1, v_namespaceName_2519_);
lean_closure_set(v___f_2526_, 2, v_toBind_2520_);
lean_closure_set(v___f_2526_, 3, v___f_2525_);
v_sz_2527_ = lean_array_size(v_____do__lift_2523_);
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2521_, v_____do__lift_2523_, v___f_2526_, v_sz_2527_, v___x_2528_, v___x_2524_);
v___x_2530_ = lean_apply_4(v_toBind_2520_, lean_box(0), lean_box(0), v___x_2529_, v___f_2522_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_namespaceName_2534_){
_start:
{
lean_object* v_toApplicative_2535_; lean_object* v_toBind_2536_; lean_object* v_toPure_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; 
v_toApplicative_2535_ = lean_ctor_get(v_inst_2531_, 0);
v_toBind_2536_ = lean_ctor_get(v_inst_2531_, 1);
lean_inc_n(v_toBind_2536_, 2);
v_toPure_2537_ = lean_ctor_get(v_toApplicative_2535_, 1);
lean_inc_n(v_toPure_2537_, 2);
v___x_2538_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2539_ = lean_apply_2(v_inst_2533_, lean_box(0), v___x_2538_);
v___f_2540_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2540_, 0, v_toPure_2537_);
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2541_, 0, v_toPure_2537_);
lean_closure_set(v___f_2541_, 1, v_inst_2532_);
lean_closure_set(v___f_2541_, 2, v_namespaceName_2534_);
lean_closure_set(v___f_2541_, 3, v_toBind_2536_);
lean_closure_set(v___f_2541_, 4, v_inst_2531_);
lean_closure_set(v___f_2541_, 5, v___f_2540_);
v___x_2542_ = lean_apply_4(v_toBind_2536_, lean_box(0), lean_box(0), v___x_2539_, v___f_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_namespaceName_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_activateScoped___redArg(v_inst_2544_, v_inst_2545_, v_inst_2546_, v_namespaceName_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2550_){
_start:
{
lean_inc(v___y_2550_);
return v___y_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2551_);
lean_dec(v___y_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2553_, lean_object* v_a_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2554_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2558_, lean_object* v_a_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2558_, v_a_2559_, v___y_2560_);
lean_dec_ref(v___y_2560_);
lean_dec(v_x_2558_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_initial_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2571_){
_start:
{
lean_object* v_name_2573_; lean_object* v_addEntry_2574_; lean_object* v_initial_2575_; lean_object* v_finalizeImport_2576_; lean_object* v_exportEntry_x3f_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_name_2573_ = lean_ctor_get(v_descr_2571_, 0);
lean_inc(v_name_2573_);
v_addEntry_2574_ = lean_ctor_get(v_descr_2571_, 1);
lean_inc(v_addEntry_2574_);
v_initial_2575_ = lean_ctor_get(v_descr_2571_, 2);
lean_inc(v_initial_2575_);
v_finalizeImport_2576_ = lean_ctor_get(v_descr_2571_, 3);
lean_inc(v_finalizeImport_2576_);
v_exportEntry_x3f_2577_ = lean_ctor_get(v_descr_2571_, 4);
lean_inc_ref(v_exportEntry_x3f_2577_);
lean_dec_ref(v_descr_2571_);
v___f_2578_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2579_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2580_, 0, v_initial_2575_);
v___x_2581_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2581_, 0, v_name_2573_);
lean_ctor_set(v___x_2581_, 1, v___f_2580_);
lean_ctor_set(v___x_2581_, 2, v___f_2579_);
lean_ctor_set(v___x_2581_, 3, v___f_2578_);
lean_ctor_set(v___x_2581_, 4, v_addEntry_2574_);
lean_ctor_set(v___x_2581_, 5, v_finalizeImport_2576_);
lean_ctor_set(v___x_2581_, 6, v_exportEntry_x3f_2577_);
v___x_2582_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2586_, lean_object* v_00_u03c3_2587_, lean_object* v_descr_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_00_u03c3_2592_, lean_object* v_descr_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2591_, v_00_u03c3_2592_, v_descr_2593_);
return v_res_2595_;
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
