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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg();
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg();
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_unsigned_to_nat(16u);
v___x_53_ = lean_mk_array(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_57_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3);
v___x_61_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1);
v___x_62_ = 1;
v___x_63_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_60_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*2, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
return v_res_67_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object* v_00_u03b2_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg(){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg___boxed(lean_object* v___dummy_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___boxed(lean_object* v___dummy_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v_res_83_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_00_u03c3_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg(){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg___boxed(lean_object* v___dummy_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_124_ = l_Lean_mkAtom(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_126_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_127_ = lean_array_push(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_137_ = l_Lean_mkAtom(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_139_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_140_ = lean_array_push(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_142_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_143_ = lean_box(2);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_146_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_149_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_150_ = lean_box(2);
v___x_151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_153_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_154_ = lean_array_push(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_156_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_157_ = lean_box(2);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_160_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_161_ = lean_array_push(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_163_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_164_ = lean_box(2);
v___x_165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_167_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_168_ = lean_array_push(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_170_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_171_ = lean_box(2);
v___x_172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_169_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object* v_descr_174_, lean_object* v_s_175_){
_start:
{
uint8_t v_trackGen_176_; 
v_trackGen_176_ = lean_ctor_get_uint8(v_descr_174_, sizeof(void*)*7);
if (v_trackGen_176_ == 0)
{
return v_s_175_;
}
else
{
lean_object* v_state_177_; lean_object* v_activeScopes_178_; uint8_t v_delimitsLocal_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_state_177_ = lean_ctor_get(v_s_175_, 0);
v_activeScopes_178_ = lean_ctor_get(v_s_175_, 1);
v_delimitsLocal_179_ = lean_ctor_get_uint8(v_s_175_, sizeof(void*)*2);
v_isSharedCheck_186_ = !lean_is_exclusive(v_s_175_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v_s_175_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_activeScopes_178_);
lean_inc(v_state_177_);
lean_dec(v_s_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_state_177_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_activeScopes_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, sizeof(void*)*2, v_delimitsLocal_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*2 + 1, v_trackGen_176_);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg___boxed(lean_object* v_descr_187_, lean_object* v_s_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_187_, v_s_188_);
lean_dec_ref(v_descr_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_00_u03c3_192_, lean_object* v_descr_193_, lean_object* v_s_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_193_, v_s_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___boxed(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_00_u03c3_198_, lean_object* v_descr_199_, lean_object* v_s_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange(v_00_u03b1_196_, v_00_u03b2_197_, v_00_u03c3_198_, v_descr_199_, v_s_200_);
lean_dec_ref(v_descr_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_211_, v___y_212_, v___y_213_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec(v_x_211_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_216_, lean_object* v_x_217_){
_start:
{
lean_inc(v_inst_216_);
return v_inst_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_218_, v_x_219_);
lean_dec(v_x_219_);
lean_dec(v_inst_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_221_, lean_object* v_x_222_){
_start:
{
lean_inc(v_s_221_);
return v_s_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_223_, v_x_224_);
lean_dec(v_x_224_);
lean_dec(v_s_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_a_227_);
lean_inc_ref_n(v___x_228_, 2);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_230_, v_a_231_);
lean_dec_ref(v_x_230_);
return v_res_232_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = l_instInhabitedError;
v___x_237_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_237_, 0, lean_box(0));
lean_closure_set(v___x_237_, 1, lean_box(0));
lean_closure_set(v___x_237_, 2, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_239_){
_start:
{
lean_object* v___f_240_; lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v___f_240_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_241_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_241_, 0, v_inst_239_);
v___f_242_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_243_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_244_ = lean_box(0);
v___x_245_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_246_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_247_ = 0;
v___x_248_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v___x_245_);
lean_ctor_set(v___x_248_, 2, v___f_240_);
lean_ctor_set(v___x_248_, 3, v___f_241_);
lean_ctor_set(v___x_248_, 4, v___f_242_);
lean_ctor_set(v___x_248_, 5, v___x_246_);
lean_ctor_set(v___x_248_, 6, v___f_243_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*7, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_00_u03c3_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_254_){
_start:
{
lean_object* v_mkInitial_256_; lean_object* v___x_257_; 
v_mkInitial_256_ = lean_ctor_get(v_descr_254_, 1);
lean_inc_ref(v_mkInitial_256_);
lean_dec_ref(v_descr_254_);
v___x_257_ = lean_apply_1(v_mkInitial_256_, lean_box(0));
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_273_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_273_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_262_ = l_Lean_NameSet_empty;
v___x_263_ = 1;
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_265_, 0, v_a_258_);
lean_ctor_set(v___x_265_, 1, v___x_262_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*2, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*2 + 1, v___x_264_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_269_);
v___x_271_ = v___x_260_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_257_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_257_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_00_u03c3_287_, lean_object* v_descr_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_00_u03c3_293_, lean_object* v_descr_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_291_, v_00_u03b2_292_, v_00_u03c3_293_, v_descr_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
return v___x_299_;
}
else
{
lean_object* v_key_300_; lean_object* v_value_301_; lean_object* v_tail_302_; uint8_t v___x_303_; 
v_key_300_ = lean_ctor_get(v_x_298_, 0);
v_value_301_ = lean_ctor_get(v_x_298_, 1);
v_tail_302_ = lean_ctor_get(v_x_298_, 2);
v___x_303_ = lean_name_eq(v_key_300_, v_a_297_);
if (v___x_303_ == 0)
{
v_x_298_ = v_tail_302_;
goto _start;
}
else
{
lean_object* v___x_305_; 
lean_inc(v_value_301_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_value_301_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_306_, lean_object* v_x_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_306_, v_x_307_);
lean_dec(v_x_307_);
lean_dec(v_a_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_buckets_311_; lean_object* v___x_312_; uint64_t v___y_314_; 
v_buckets_311_ = lean_ctor_get(v_m_309_, 1);
v___x_312_ = lean_array_get_size(v_buckets_311_);
if (lean_obj_tag(v_a_310_) == 0)
{
uint64_t v___x_328_; 
v___x_328_ = 1723ULL;
v___y_314_ = v___x_328_;
goto v___jp_313_;
}
else
{
uint64_t v_hash_329_; 
v_hash_329_ = lean_ctor_get_uint64(v_a_310_, sizeof(void*)*2);
v___y_314_ = v_hash_329_;
goto v___jp_313_;
}
v___jp_313_:
{
uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___y_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___y_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_312_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v___x_326_ = lean_array_uget_borrowed(v_buckets_311_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_310_, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_m_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_333_, lean_object* v_vals_334_, lean_object* v_i_335_, lean_object* v_k_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_keys_333_);
v___x_338_ = lean_nat_dec_lt(v_i_335_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v_i_335_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v_k_x27_340_; uint8_t v___x_341_; 
v_k_x27_340_ = lean_array_fget_borrowed(v_keys_333_, v_i_335_);
v___x_341_ = lean_name_eq(v_k_336_, v_k_x27_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_335_, v___x_342_);
lean_dec(v_i_335_);
v_i_335_ = v___x_343_;
goto _start;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_array_fget_borrowed(v_vals_334_, v_i_335_);
lean_dec(v_i_335_);
lean_inc(v___x_345_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_i_349_, lean_object* v_k_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_347_, v_vals_348_, v_i_349_, v_k_350_);
lean_dec(v_k_350_);
lean_dec_ref(v_vals_348_);
lean_dec_ref(v_keys_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_352_, size_t v_x_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
lean_object* v_es_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v_j_359_; lean_object* v___x_360_; 
v_es_355_ = lean_ctor_get(v_x_352_, 0);
v___x_356_ = lean_box(2);
v___x_357_ = ((size_t)31ULL);
v___x_358_ = lean_usize_land(v_x_353_, v___x_357_);
v_j_359_ = lean_usize_to_nat(v___x_358_);
v___x_360_ = lean_array_get_borrowed(v___x_356_, v_es_355_, v_j_359_);
lean_dec(v_j_359_);
switch(lean_obj_tag(v___x_360_))
{
case 0:
{
lean_object* v_key_361_; lean_object* v_val_362_; uint8_t v___x_363_; 
v_key_361_ = lean_ctor_get(v___x_360_, 0);
v_val_362_ = lean_ctor_get(v___x_360_, 1);
v___x_363_ = lean_name_eq(v_x_354_, v_key_361_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
lean_inc(v_val_362_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_val_362_);
return v___x_365_;
}
}
case 1:
{
lean_object* v_node_366_; size_t v___x_367_; size_t v___x_368_; 
v_node_366_ = lean_ctor_get(v___x_360_, 0);
v___x_367_ = ((size_t)5ULL);
v___x_368_ = lean_usize_shift_right(v_x_353_, v___x_367_);
v_x_352_ = v_node_366_;
v_x_353_ = v___x_368_;
goto _start;
}
default: 
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
}
else
{
lean_object* v_ks_371_; lean_object* v_vs_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_ks_371_ = lean_ctor_get(v_x_352_, 0);
v_vs_372_ = lean_ctor_get(v_x_352_, 1);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_371_, v_vs_372_, v___x_373_, v_x_354_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_1059__boxed_378_; lean_object* v_res_379_; 
v_x_1059__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_res_379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_375_, v_x_1059__boxed_378_, v_x_377_);
lean_dec(v_x_377_);
lean_dec_ref(v_x_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint64_t v___y_383_; 
if (lean_obj_tag(v_x_381_) == 0)
{
uint64_t v___x_386_; 
v___x_386_ = 1723ULL;
v___y_383_ = v___x_386_;
goto v___jp_382_;
}
else
{
uint64_t v_hash_387_; 
v_hash_387_ = lean_ctor_get_uint64(v_x_381_, sizeof(void*)*2);
v___y_383_ = v_hash_387_;
goto v___jp_382_;
}
v___jp_382_:
{
size_t v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_uint64_to_usize(v___y_383_);
v___x_385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_380_, v___x_384_, v_x_381_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_388_, v_x_389_);
lean_dec(v_x_389_);
lean_dec_ref(v_x_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
uint8_t v_stage_u2081_393_; 
v_stage_u2081_393_ = lean_ctor_get_uint8(v_x_391_, sizeof(void*)*2);
if (v_stage_u2081_393_ == 0)
{
lean_object* v_map_u2081_394_; lean_object* v_map_u2082_395_; lean_object* v___x_396_; 
v_map_u2081_394_ = lean_ctor_get(v_x_391_, 0);
v_map_u2082_395_ = lean_ctor_get(v_x_391_, 1);
v___x_396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_395_, v_x_392_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_394_, v_x_392_);
return v___x_397_;
}
else
{
return v___x_396_;
}
}
else
{
lean_object* v_map_u2081_398_; lean_object* v___x_399_; 
v_map_u2081_398_ = lean_ctor_get(v_x_391_, 0);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_398_, v_x_392_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_400_, v_x_401_);
lean_dec(v_x_401_);
lean_dec_ref(v_x_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_403_, lean_object* v_b_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_dec(v_b_404_);
lean_dec(v_a_403_);
return v_x_405_;
}
else
{
lean_object* v_key_406_; lean_object* v_value_407_; lean_object* v_tail_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_420_; 
v_key_406_ = lean_ctor_get(v_x_405_, 0);
v_value_407_ = lean_ctor_get(v_x_405_, 1);
v_tail_408_ = lean_ctor_get(v_x_405_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_420_ == 0)
{
v___x_410_ = v_x_405_;
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tail_408_);
lean_inc(v_value_407_);
lean_inc(v_key_406_);
lean_dec(v_x_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint8_t v___x_412_; 
v___x_412_ = lean_name_eq(v_key_406_, v_a_403_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_403_, v_b_404_, v_tail_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_key_406_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_value_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v___x_418_; 
lean_dec(v_value_407_);
lean_dec(v_key_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_b_404_);
lean_ctor_set(v___x_410_, 0, v_a_403_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_b_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_tail_408_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
return v_x_421_;
}
else
{
lean_object* v_key_423_; lean_object* v_value_424_; lean_object* v_tail_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_451_; 
v_key_423_ = lean_ctor_get(v_x_422_, 0);
v_value_424_ = lean_ctor_get(v_x_422_, 1);
v_tail_425_ = lean_ctor_get(v_x_422_, 2);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_451_ == 0)
{
v___x_427_ = v_x_422_;
v_isShared_428_ = v_isSharedCheck_451_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_tail_425_);
lean_inc(v_value_424_);
lean_inc(v_key_423_);
lean_dec(v_x_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_451_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; uint64_t v___y_431_; 
v___x_429_ = lean_array_get_size(v_x_421_);
if (lean_obj_tag(v_key_423_) == 0)
{
uint64_t v___x_449_; 
v___x_449_ = 1723ULL;
v___y_431_ = v___x_449_;
goto v___jp_430_;
}
else
{
uint64_t v_hash_450_; 
v_hash_450_ = lean_ctor_get_uint64(v_key_423_, sizeof(void*)*2);
v___y_431_ = v_hash_450_;
goto v___jp_430_;
}
v___jp_430_:
{
uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v_fold_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_432_ = 32ULL;
v___x_433_ = lean_uint64_shift_right(v___y_431_, v___x_432_);
v_fold_434_ = lean_uint64_xor(v___y_431_, v___x_433_);
v___x_435_ = 16ULL;
v___x_436_ = lean_uint64_shift_right(v_fold_434_, v___x_435_);
v___x_437_ = lean_uint64_xor(v_fold_434_, v___x_436_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = lean_usize_of_nat(v___x_429_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_usize_land(v___x_438_, v___x_441_);
v___x_443_ = lean_array_uget_borrowed(v_x_421_, v___x_442_);
lean_inc(v___x_443_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 2, v___x_443_);
v___x_445_ = v___x_427_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_key_423_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_value_424_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v___x_443_);
v___x_445_ = v_reuseFailAlloc_448_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_array_uset(v_x_421_, v___x_442_, v___x_445_);
v_x_421_ = v___x_446_;
v_x_422_ = v_tail_425_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_452_, lean_object* v_source_453_, lean_object* v_target_454_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_source_453_);
v___x_456_ = lean_nat_dec_lt(v_i_452_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_source_453_);
lean_dec(v_i_452_);
return v_target_454_;
}
else
{
lean_object* v_es_457_; lean_object* v___x_458_; lean_object* v_source_459_; lean_object* v_target_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_es_457_ = lean_array_fget(v_source_453_, v_i_452_);
v___x_458_ = lean_box(0);
v_source_459_ = lean_array_fset(v_source_453_, v_i_452_, v___x_458_);
v_target_460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_454_, v_es_457_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v_i_452_, v___x_461_);
lean_dec(v_i_452_);
v_i_452_ = v___x_462_;
v_source_453_ = v_source_459_;
v_target_454_ = v_target_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_nbuckets_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_465_ = lean_array_get_size(v_data_464_);
v___x_466_ = lean_unsigned_to_nat(2u);
v_nbuckets_467_ = lean_nat_mul(v___x_465_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_box(0);
v___x_470_ = lean_mk_array(v_nbuckets_467_, v___x_469_);
v___x_471_ = lean_array_propagate_mark(v_data_464_, v___x_470_);
v___x_472_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_468_, v_data_464_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
else
{
lean_object* v_key_476_; lean_object* v_tail_477_; uint8_t v___x_478_; 
v_key_476_ = lean_ctor_get(v_x_474_, 0);
v_tail_477_ = lean_ctor_get(v_x_474_, 2);
v___x_478_ = lean_name_eq(v_key_476_, v_a_473_);
if (v___x_478_ == 0)
{
v_x_474_ = v_tail_477_;
goto _start;
}
else
{
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_a_480_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_size_487_; lean_object* v_buckets_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_534_; 
v_size_487_ = lean_ctor_get(v_m_484_, 0);
v_buckets_488_ = lean_ctor_get(v_m_484_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_m_484_);
if (v_isSharedCheck_534_ == 0)
{
v___x_490_ = v_m_484_;
v_isShared_491_ = v_isSharedCheck_534_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_buckets_488_);
lean_inc(v_size_487_);
lean_dec(v_m_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_534_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; uint64_t v___y_494_; 
v___x_492_ = lean_array_get_size(v_buckets_488_);
if (lean_obj_tag(v_a_485_) == 0)
{
uint64_t v___x_532_; 
v___x_532_ = 1723ULL;
v___y_494_ = v___x_532_;
goto v___jp_493_;
}
else
{
uint64_t v_hash_533_; 
v_hash_533_ = lean_ctor_get_uint64(v_a_485_, sizeof(void*)*2);
v___y_494_ = v_hash_533_;
goto v___jp_493_;
}
v___jp_493_:
{
uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v_fold_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v_bkt_506_; uint8_t v___x_507_; 
v___x_495_ = 32ULL;
v___x_496_ = lean_uint64_shift_right(v___y_494_, v___x_495_);
v_fold_497_ = lean_uint64_xor(v___y_494_, v___x_496_);
v___x_498_ = 16ULL;
v___x_499_ = lean_uint64_shift_right(v_fold_497_, v___x_498_);
v___x_500_ = lean_uint64_xor(v_fold_497_, v___x_499_);
v___x_501_ = lean_uint64_to_usize(v___x_500_);
v___x_502_ = lean_usize_of_nat(v___x_492_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_sub(v___x_502_, v___x_503_);
v___x_505_ = lean_usize_land(v___x_501_, v___x_504_);
v_bkt_506_ = lean_array_uget_borrowed(v_buckets_488_, v___x_505_);
v___x_507_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_485_, v_bkt_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v_size_x27_509_; lean_object* v___x_510_; lean_object* v_buckets_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v_size_x27_509_ = lean_nat_add(v_size_487_, v___x_508_);
lean_dec(v_size_487_);
lean_inc(v_bkt_506_);
v___x_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_510_, 0, v_a_485_);
lean_ctor_set(v___x_510_, 1, v_b_486_);
lean_ctor_set(v___x_510_, 2, v_bkt_506_);
v_buckets_x27_511_ = lean_array_uset(v_buckets_488_, v___x_505_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(4u);
v___x_513_ = lean_nat_mul(v_size_x27_509_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(3u);
v___x_515_ = lean_nat_div(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_array_get_size(v_buckets_x27_511_);
v___x_517_ = lean_nat_dec_le(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
if (v___x_517_ == 0)
{
lean_object* v_val_518_; lean_object* v___x_520_; 
v_val_518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_511_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_val_518_);
lean_ctor_set(v___x_490_, 0, v_size_x27_509_);
v___x_520_ = v___x_490_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_val_518_);
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
lean_object* v___x_523_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_buckets_x27_511_);
lean_ctor_set(v___x_490_, 0, v_size_x27_509_);
v___x_523_ = v___x_490_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_size_x27_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_buckets_x27_511_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v___x_525_; lean_object* v_buckets_x27_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_inc(v_bkt_506_);
v___x_525_ = lean_box(0);
v_buckets_x27_526_ = lean_array_uset(v_buckets_488_, v___x_505_, v___x_525_);
v___x_527_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_485_, v_b_486_, v_bkt_506_);
v___x_528_ = lean_array_uset(v_buckets_x27_526_, v___x_505_, v___x_527_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_528_);
v___x_530_ = v___x_490_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_size_487_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_564_; 
v_ks_539_ = lean_ctor_get(v_x_535_, 0);
v_vs_540_ = lean_ctor_get(v_x_535_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_564_ == 0)
{
v___x_542_ = v_x_535_;
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_535_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_get_size(v_ks_539_);
v___x_545_ = lean_nat_dec_lt(v_x_536_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
lean_dec(v_x_536_);
v___x_546_ = lean_array_push(v_ks_539_, v_x_537_);
v___x_547_ = lean_array_push(v_vs_540_, v_x_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_547_);
lean_ctor_set(v___x_542_, 0, v___x_546_);
v___x_549_ = v___x_542_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v_k_x27_551_; uint8_t v___x_552_; 
v_k_x27_551_ = lean_array_fget_borrowed(v_ks_539_, v_x_536_);
v___x_552_ = lean_name_eq(v_x_537_, v_k_x27_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_554_; 
if (v_isShared_543_ == 0)
{
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_vs_540_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_x_536_, v___x_555_);
lean_dec(v_x_536_);
v_x_535_ = v___x_554_;
v_x_536_ = v___x_556_;
goto _start;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = lean_array_fset(v_ks_539_, v_x_536_, v_x_537_);
v___x_560_ = lean_array_fset(v_vs_540_, v_x_536_, v_x_538_);
lean_dec(v_x_536_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_560_);
lean_ctor_set(v___x_542_, 0, v___x_559_);
v___x_562_ = v___x_542_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_565_, lean_object* v_k_566_, lean_object* v_v_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_565_, v___x_568_, v_k_566_, v_v_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_571_, size_t v_x_572_, size_t v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_571_) == 0)
{
lean_object* v_es_576_; size_t v___x_577_; size_t v___x_578_; lean_object* v_j_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_es_576_ = lean_ctor_get(v_x_571_, 0);
v___x_577_ = ((size_t)31ULL);
v___x_578_ = lean_usize_land(v_x_572_, v___x_577_);
v_j_579_ = lean_usize_to_nat(v___x_578_);
v___x_580_ = lean_array_get_size(v_es_576_);
v___x_581_ = lean_nat_dec_lt(v_j_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec(v_j_579_);
lean_dec(v_x_575_);
lean_dec(v_x_574_);
return v_x_571_;
}
else
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_620_; 
lean_inc_ref(v_es_576_);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_571_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_x_571_, 0);
lean_dec(v_unused_621_);
v___x_583_ = v_x_571_;
v_isShared_584_ = v_isSharedCheck_620_;
goto v_resetjp_582_;
}
else
{
lean_dec(v_x_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_620_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_v_585_; lean_object* v___x_586_; lean_object* v_xs_x27_587_; lean_object* v___y_589_; 
v_v_585_ = lean_array_fget(v_es_576_, v_j_579_);
v___x_586_ = lean_box(0);
v_xs_x27_587_ = lean_array_fset(v_es_576_, v_j_579_, v___x_586_);
switch(lean_obj_tag(v_v_585_))
{
case 0:
{
lean_object* v_key_594_; lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_605_; 
v_key_594_ = lean_ctor_get(v_v_585_, 0);
v_val_595_ = lean_ctor_get(v_v_585_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_v_585_);
if (v_isSharedCheck_605_ == 0)
{
v___x_597_ = v_v_585_;
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_inc(v_key_594_);
lean_dec(v_v_585_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = lean_name_eq(v_x_574_, v_key_594_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_del_object(v___x_597_);
v___x_600_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_594_, v_val_595_, v_x_574_, v_x_575_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___y_589_ = v___x_601_;
goto v___jp_588_;
}
else
{
lean_object* v___x_603_; 
lean_dec(v_val_595_);
lean_dec(v_key_594_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v_x_575_);
lean_ctor_set(v___x_597_, 0, v_x_574_);
v___x_603_ = v___x_597_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_x_574_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_x_575_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
v___y_589_ = v___x_603_;
goto v___jp_588_;
}
}
}
}
case 1:
{
lean_object* v_node_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
v_node_606_ = lean_ctor_get(v_v_585_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_v_585_);
if (v_isSharedCheck_618_ == 0)
{
v___x_608_ = v_v_585_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_node_606_);
lean_dec(v_v_585_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_610_ = ((size_t)5ULL);
v___x_611_ = lean_usize_shift_right(v_x_572_, v___x_610_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_x_573_, v___x_612_);
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_606_, v___x_611_, v___x_613_, v_x_574_, v_x_575_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_614_);
v___x_616_ = v___x_608_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v___y_589_ = v___x_616_;
goto v___jp_588_;
}
}
}
default: 
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_x_574_);
lean_ctor_set(v___x_619_, 1, v_x_575_);
v___y_589_ = v___x_619_;
goto v___jp_588_;
}
}
v___jp_588_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_array_fset(v_xs_x27_587_, v_j_579_, v___y_589_);
lean_dec(v_j_579_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_590_);
v___x_592_ = v___x_583_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_641_; 
v_ks_622_ = lean_ctor_get(v_x_571_, 0);
v_vs_623_ = lean_ctor_get(v_x_571_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_571_);
if (v_isSharedCheck_641_ == 0)
{
v___x_625_ = v_x_571_;
v_isShared_626_ = v_isSharedCheck_641_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_vs_623_);
lean_inc(v_ks_622_);
lean_dec(v_x_571_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_641_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_ks_622_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_vs_623_);
v___x_628_ = v_reuseFailAlloc_640_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v_newNode_629_; size_t v___x_630_; uint8_t v___x_631_; 
v_newNode_629_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_628_, v_x_574_, v_x_575_);
v___x_630_ = ((size_t)7ULL);
v___x_631_ = lean_usize_dec_le(v___x_630_, v_x_573_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_629_);
v___x_633_ = lean_unsigned_to_nat(4u);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
if (v___x_634_ == 0)
{
lean_object* v_ks_635_; lean_object* v_vs_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_ks_635_ = lean_ctor_get(v_newNode_629_, 0);
lean_inc_ref(v_ks_635_);
v_vs_636_ = lean_ctor_get(v_newNode_629_, 1);
lean_inc_ref(v_vs_636_);
lean_dec_ref(v_newNode_629_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_573_, v_ks_635_, v_vs_636_, v___x_637_, v___x_638_);
lean_dec_ref(v_vs_636_);
lean_dec_ref(v_ks_635_);
return v___x_639_;
}
else
{
return v_newNode_629_;
}
}
else
{
return v_newNode_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_i_645_, lean_object* v_entries_646_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_keys_643_);
v___x_648_ = lean_nat_dec_lt(v_i_645_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec(v_i_645_);
return v_entries_646_;
}
else
{
lean_object* v_k_649_; lean_object* v_v_650_; uint64_t v___y_652_; 
v_k_649_ = lean_array_fget_borrowed(v_keys_643_, v_i_645_);
v_v_650_ = lean_array_fget_borrowed(v_vals_644_, v_i_645_);
if (lean_obj_tag(v_k_649_) == 0)
{
uint64_t v___x_663_; 
v___x_663_ = 1723ULL;
v___y_652_ = v___x_663_;
goto v___jp_651_;
}
else
{
uint64_t v_hash_664_; 
v_hash_664_ = lean_ctor_get_uint64(v_k_649_, sizeof(void*)*2);
v___y_652_ = v_hash_664_;
goto v___jp_651_;
}
v___jp_651_:
{
size_t v_h_653_; size_t v___x_654_; lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v_h_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_h_653_ = lean_uint64_to_usize(v___y_652_);
v___x_654_ = ((size_t)5ULL);
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_sub(v_depth_642_, v___x_656_);
v___x_658_ = lean_usize_mul(v___x_654_, v___x_657_);
v_h_659_ = lean_usize_shift_right(v_h_653_, v___x_658_);
v___x_660_ = lean_nat_add(v_i_645_, v___x_655_);
lean_dec(v_i_645_);
lean_inc(v_v_650_);
lean_inc(v_k_649_);
v___x_661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_646_, v_h_659_, v_depth_642_, v_k_649_, v_v_650_);
v_i_645_ = v___x_660_;
v_entries_646_ = v___x_661_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_i_668_, lean_object* v_entries_669_){
_start:
{
size_t v_depth_boxed_670_; lean_object* v_res_671_; 
v_depth_boxed_670_ = lean_unbox_usize(v_depth_665_);
lean_dec(v_depth_665_);
v_res_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_670_, v_keys_666_, v_vals_667_, v_i_668_, v_entries_669_);
lean_dec_ref(v_vals_667_);
lean_dec_ref(v_keys_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
size_t v_x_1435__boxed_677_; size_t v_x_1436__boxed_678_; lean_object* v_res_679_; 
v_x_1435__boxed_677_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_x_1436__boxed_678_ = lean_unbox_usize(v_x_674_);
lean_dec(v_x_674_);
v_res_679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_672_, v_x_1435__boxed_677_, v_x_1436__boxed_678_, v_x_675_, v_x_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
uint64_t v___y_684_; 
if (lean_obj_tag(v_x_681_) == 0)
{
uint64_t v___x_688_; 
v___x_688_ = 1723ULL;
v___y_684_ = v___x_688_;
goto v___jp_683_;
}
else
{
uint64_t v_hash_689_; 
v_hash_689_ = lean_ctor_get_uint64(v_x_681_, sizeof(void*)*2);
v___y_684_ = v_hash_689_;
goto v___jp_683_;
}
v___jp_683_:
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_uint64_to_usize(v___y_684_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_680_, v___x_685_, v___x_686_, v_x_681_, v_x_682_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_stage_u2081_693_; 
v_stage_u2081_693_ = lean_ctor_get_uint8(v_x_690_, sizeof(void*)*2);
if (v_stage_u2081_693_ == 0)
{
lean_object* v_map_u2081_694_; lean_object* v_map_u2082_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_map_u2081_694_ = lean_ctor_get(v_x_690_, 0);
v_map_u2082_695_ = lean_ctor_get(v_x_690_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v_x_690_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_map_u2082_695_);
lean_inc(v_map_u2081_694_);
lean_dec(v_x_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_695_, v_x_691_, v_x_692_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_map_u2081_694_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_702_, sizeof(void*)*2, v_stage_u2081_693_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_map_u2081_704_; lean_object* v_map_u2082_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
v_map_u2081_704_ = lean_ctor_get(v_x_690_, 0);
v_map_u2082_705_ = lean_ctor_get(v_x_690_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v_x_690_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_map_u2082_705_);
lean_inc(v_map_u2081_704_);
lean_dec(v_x_690_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_704_, v_x_691_, v_x_692_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_map_u2082_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*2, v_stage_u2081_693_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(32u);
v___x_715_ = lean_mk_empty_array_with_capacity(v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_717_ = ((size_t)5ULL);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_unsigned_to_nat(32u);
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_719_);
v___x_721_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_722_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
lean_ctor_set(v___x_722_, 2, v___x_718_);
lean_ctor_set(v___x_722_, 3, v___x_718_);
lean_ctor_set_usize(v___x_722_, 4, v___x_717_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_723_, lean_object* v_ns_724_, lean_object* v_b_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_723_, v_ns_724_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_728_ = l_Lean_PersistentArray_push___redArg(v___x_727_, v_b_725_);
v___x_729_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_723_, v_ns_724_, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_val_730_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_726_, 1);
v___x_731_ = l_Lean_PersistentArray_push___redArg(v_val_730_, v_b_725_);
v___x_732_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_723_, v_ns_724_, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_733_, lean_object* v_scopedEntries_734_, lean_object* v_ns_735_, lean_object* v_b_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_734_, v_ns_735_, v_b_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_742_, v_x_743_, v_x_744_);
lean_dec(v_x_744_);
lean_dec_ref(v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_747_, v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_755_, v_x_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec_ref(v_x_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_760_, v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_763_, lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_763_, v_m_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_m_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_768_, v_x_769_, v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_772_, lean_object* v_m_773_, lean_object* v_a_774_, lean_object* v_b_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_773_, v_a_774_, v_b_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, size_t v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_778_, v_x_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
size_t v_x_1736__boxed_786_; lean_object* v_res_787_; 
v_x_1736__boxed_786_ = lean_unbox_usize(v_x_784_);
lean_dec(v_x_784_);
v_res_787_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_782_, v_x_783_, v_x_1736__boxed_786_, v_x_785_);
lean_dec(v_x_785_);
lean_dec_ref(v_x_783_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_788_, lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_789_, v_x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_792_, lean_object* v_a_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_792_, v_a_793_, v_x_794_);
lean_dec(v_x_794_);
lean_dec(v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_1752__boxed_809_; size_t v_x_1753__boxed_810_; lean_object* v_res_811_; 
v_x_1752__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_x_1753__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_res_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_803_, v_x_804_, v_x_1752__boxed_809_, v_x_1753__boxed_810_, v_x_807_, v_x_808_);
return v_res_811_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_812_, lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_816_, v_a_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec(v_a_817_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_821_, lean_object* v_data_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_b_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_825_, v_b_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_heq_832_, lean_object* v_i_833_, lean_object* v_k_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_830_, v_vals_831_, v_i_833_, v_k_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_836_, lean_object* v_keys_837_, lean_object* v_vals_838_, lean_object* v_heq_839_, lean_object* v_i_840_, lean_object* v_k_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_836_, v_keys_837_, v_vals_838_, v_heq_839_, v_i_840_, v_k_841_);
lean_dec(v_k_841_);
lean_dec_ref(v_vals_838_);
lean_dec_ref(v_keys_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_843_, lean_object* v_n_844_, lean_object* v_k_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_844_, v_k_845_, v_v_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_848_, size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_heq_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_849_, v_keys_850_, v_vals_851_, v_i_853_, v_entries_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_856_, lean_object* v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_entries_862_){
_start:
{
size_t v_depth_boxed_863_; lean_object* v_res_864_; 
v_depth_boxed_863_ = lean_unbox_usize(v_depth_857_);
lean_dec(v_depth_857_);
v_res_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_856_, v_depth_boxed_863_, v_keys_858_, v_vals_859_, v_heq_860_, v_i_861_, v_entries_862_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_865_, lean_object* v_i_866_, lean_object* v_source_867_, lean_object* v_target_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_866_, v_source_867_, v_target_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_871_, v_x_872_, v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_880_, lean_object* v_as_881_, size_t v_sz_882_, size_t v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_a_888_; uint8_t v___x_892_; 
v___x_892_ = lean_usize_dec_lt(v_i_883_, v_sz_882_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec_ref(v_descr_880_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_b_884_);
return v___x_893_;
}
else
{
lean_object* v_fst_894_; lean_object* v_snd_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_934_; 
v_fst_894_ = lean_ctor_get(v_b_884_, 0);
v_snd_895_ = lean_ctor_get(v_b_884_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_b_884_);
if (v_isSharedCheck_934_ == 0)
{
v___x_897_ = v_b_884_;
v_isShared_898_ = v_isSharedCheck_934_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_snd_895_);
lean_inc(v_fst_894_);
lean_dec(v_b_884_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_934_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_a_899_; 
v_a_899_ = lean_array_uget_borrowed(v_as_881_, v_i_883_);
if (lean_obj_tag(v_a_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_ofOLeanEntry_901_; lean_object* v_addEntry_902_; lean_object* v___x_903_; 
v_a_900_ = lean_ctor_get(v_a_899_, 0);
v_ofOLeanEntry_901_ = lean_ctor_get(v_descr_880_, 2);
v_addEntry_902_ = lean_ctor_get(v_descr_880_, 4);
lean_inc_ref(v_ofOLeanEntry_901_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_900_);
lean_inc(v_fst_894_);
v___x_903_ = lean_apply_4(v_ofOLeanEntry_901_, v_fst_894_, v_a_900_, v___y_885_, lean_box(0));
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
lean_inc(v_addEntry_902_);
v___x_905_ = lean_apply_2(v_addEntry_902_, v_fst_894_, v_a_904_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_905_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_895_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
v_a_888_ = v___x_907_;
goto v___jp_887_;
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_897_);
lean_dec(v_snd_895_);
lean_dec(v_fst_894_);
lean_dec_ref(v_descr_880_);
v_a_909_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_903_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
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
else
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v_ofOLeanEntry_919_; lean_object* v___x_920_; 
v_a_917_ = lean_ctor_get(v_a_899_, 0);
v_a_918_ = lean_ctor_get(v_a_899_, 1);
v_ofOLeanEntry_919_ = lean_ctor_get(v_descr_880_, 2);
lean_inc_ref(v_ofOLeanEntry_919_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_918_);
lean_inc(v_fst_894_);
v___x_920_ = lean_apply_4(v_ofOLeanEntry_919_, v_fst_894_, v_a_918_, v___y_885_, lean_box(0));
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
lean_inc(v_a_917_);
v___x_922_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_895_, v_a_917_, v_a_921_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_922_);
v___x_924_ = v___x_897_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_fst_894_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v_a_888_ = v___x_924_;
goto v___jp_887_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_del_object(v___x_897_);
lean_dec(v_snd_895_);
lean_dec(v_fst_894_);
lean_dec_ref(v_descr_880_);
v_a_926_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_920_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_920_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
v___jp_887_:
{
size_t v___x_889_; size_t v___x_890_; 
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_add(v_i_883_, v___x_889_);
v_i_883_ = v___x_890_;
v_b_884_ = v_a_888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_935_, lean_object* v_as_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_943_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_935_, v_as_936_, v_sz_boxed_942_, v_i_boxed_943_, v_b_939_, v___y_940_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v_as_936_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_945_, lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_descr_945_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_949_);
return v___x_953_;
}
else
{
lean_object* v_fst_954_; lean_object* v_snd_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_979_; 
v_fst_954_ = lean_ctor_get(v_b_949_, 0);
v_snd_955_ = lean_ctor_get(v_b_949_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_b_949_);
if (v_isSharedCheck_979_ == 0)
{
v___x_957_ = v_b_949_;
v_isShared_958_ = v_isSharedCheck_979_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_955_);
lean_inc(v_fst_954_);
lean_dec(v_b_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_979_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_a_959_; lean_object* v___x_961_; 
v_a_959_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
if (v_isShared_958_ == 0)
{
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_fst_954_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_snd_955_);
v___x_961_ = v_reuseFailAlloc_978_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; 
v_sz_962_ = lean_array_size(v_a_959_);
v___x_963_ = ((size_t)0ULL);
lean_inc_ref(v_descr_945_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_945_, v_a_959_, v_sz_962_, v___x_963_, v___x_961_, v___y_950_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_977_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v_fst_966_ = lean_ctor_get(v_a_965_, 0);
v_snd_967_ = lean_ctor_get(v_a_965_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_977_ == 0)
{
v___x_969_ = v_a_965_;
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_a_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fst_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_snd_967_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
size_t v___x_973_; size_t v___x_974_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_948_, v___x_973_);
v_i_948_ = v___x_974_;
v_b_949_ = v___x_972_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_945_);
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_980_, lean_object* v_as_981_, lean_object* v_sz_982_, lean_object* v_i_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_sz_boxed_987_ = lean_unbox_usize(v_sz_982_);
lean_dec(v_sz_982_);
v_i_boxed_988_ = lean_unbox_usize(v_i_983_);
lean_dec(v_i_983_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_980_, v_as_981_, v_sz_boxed_987_, v_i_boxed_988_, v_b_984_, v___y_985_);
lean_dec_ref(v___y_985_);
lean_dec_ref(v_as_981_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_990_, lean_object* v_as_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_mkInitial_994_; lean_object* v_finalizeImport_995_; lean_object* v___x_996_; 
v_mkInitial_994_ = lean_ctor_get(v_descr_990_, 1);
v_finalizeImport_995_ = lean_ctor_get(v_descr_990_, 5);
lean_inc(v_finalizeImport_995_);
lean_inc_ref(v_mkInitial_994_);
v___x_996_ = lean_apply_1(v_mkInitial_994_, lean_box(0));
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = 1;
v___x_999_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_a_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v_sz_1001_ = lean_array_size(v_as_991_);
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_990_, v_as_991_, v_sz_1001_, v___x_1002_, v___x_1000_, v_a_992_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1026_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1026_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1026_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1025_; 
v_fst_1008_ = lean_ctor_get(v_a_1004_, 0);
v_snd_1009_ = lean_ctor_get(v_a_1004_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_1004_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1011_ = v_a_1004_;
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_inc(v_fst_1008_);
lean_dec(v_a_1004_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1013_ = lean_apply_1(v_finalizeImport_995_, v_fst_1008_);
v___x_1014_ = l_Lean_NameSet_empty;
v___x_1015_ = 0;
v___x_1016_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*2, v___x_998_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*2 + 1, v___x_1015_);
v___x_1017_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 1);
lean_ctor_set(v___x_1011_, 1, v___x_1017_);
lean_ctor_set(v___x_1011_, 0, v___x_1016_);
v___x_1019_ = v___x_1011_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_snd_1009_);
lean_ctor_set(v___x_1020_, 2, v___x_1017_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1020_);
v___x_1022_ = v___x_1006_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_finalizeImport_995_);
v_a_1027_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1003_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1003_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_finalizeImport_995_);
lean_dec_ref(v_descr_990_);
v_a_1035_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_996_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_996_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1043_, lean_object* v_as_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1043_, v_as_1044_, v_a_1045_);
lean_dec_ref(v_a_1045_);
lean_dec_ref(v_as_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_00_u03c3_1050_, lean_object* v_descr_1051_, lean_object* v_as_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1051_, v_as_1052_, v_a_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_00_u03c3_1058_, lean_object* v_descr_1059_, lean_object* v_as_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1056_, v_00_u03b2_1057_, v_00_u03c3_1058_, v_descr_1059_, v_as_1060_, v_a_1061_);
lean_dec_ref(v_a_1061_);
lean_dec_ref(v_as_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03c3_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_descr_1067_, lean_object* v_as_1068_, size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1067_, v_as_1068_, v_sz_1069_, v_i_1070_, v_b_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03c3_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_descr_1078_, lean_object* v_as_1079_, lean_object* v_sz_1080_, lean_object* v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
size_t v_sz_boxed_1085_; size_t v_i_boxed_1086_; lean_object* v_res_1087_; 
v_sz_boxed_1085_ = lean_unbox_usize(v_sz_1080_);
lean_dec(v_sz_1080_);
v_i_boxed_1086_ = lean_unbox_usize(v_i_1081_);
lean_dec(v_i_1081_);
v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1075_, v_00_u03c3_1076_, v_00_u03b2_1077_, v_descr_1078_, v_as_1079_, v_sz_boxed_1085_, v_i_boxed_1086_, v_b_1082_, v___y_1083_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_as_1079_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1088_, lean_object* v_00_u03c3_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_descr_1091_, lean_object* v_as_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1091_, v_as_1092_, v_sz_1093_, v_i_1094_, v_b_1095_, v___y_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03c3_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_descr_1102_, lean_object* v_as_1103_, lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
size_t v_sz_boxed_1109_; size_t v_i_boxed_1110_; lean_object* v_res_1111_; 
v_sz_boxed_1109_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1110_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1099_, v_00_u03c3_1100_, v_00_u03b2_1101_, v_descr_1102_, v_as_1103_, v_sz_boxed_1109_, v_i_boxed_1110_, v_b_1106_, v___y_1107_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_as_1103_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1112_, lean_object* v_descr_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
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
lean_object* v_head_1118_; lean_object* v_tail_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1146_; 
v_head_1118_ = lean_ctor_get(v_a_1115_, 0);
v_tail_1119_ = lean_ctor_get(v_a_1115_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_a_1115_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1121_ = v_a_1115_;
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_tail_1119_);
lean_inc(v_head_1118_);
lean_dec(v_a_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1146_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___y_1124_; lean_object* v_state_1129_; lean_object* v_activeScopes_1130_; uint8_t v_delimitsLocal_1131_; uint8_t v_scopeChanged_1132_; uint8_t v___x_1133_; 
v_state_1129_ = lean_ctor_get(v_head_1118_, 0);
v_activeScopes_1130_ = lean_ctor_get(v_head_1118_, 1);
v_delimitsLocal_1131_ = lean_ctor_get_uint8(v_head_1118_, sizeof(void*)*2);
v_scopeChanged_1132_ = lean_ctor_get_uint8(v_head_1118_, sizeof(void*)*2 + 1);
v___x_1133_ = l_Lean_NameSet_contains(v_activeScopes_1130_, v_a_1112_);
if (v___x_1133_ == 0)
{
v___y_1124_ = v_head_1118_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1143_; 
lean_inc(v_activeScopes_1130_);
lean_inc(v_state_1129_);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_head_1118_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1144_ = lean_ctor_get(v_head_1118_, 1);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_head_1118_, 0);
lean_dec(v_unused_1145_);
v___x_1135_ = v_head_1118_;
v_isShared_1136_ = v_isSharedCheck_1143_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v_head_1118_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1143_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_addEntry_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v_addEntry_1137_ = lean_ctor_get(v_descr_1113_, 4);
lean_inc(v_addEntry_1137_);
lean_inc(v_a_1114_);
v___x_1138_ = lean_apply_2(v_addEntry_1137_, v_state_1129_, v_a_1114_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1138_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_activeScopes_1130_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*2, v_delimitsLocal_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*2 + 1, v_scopeChanged_1132_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1113_, v___x_1140_);
v___y_1124_ = v___x_1141_;
goto v___jp_1123_;
}
}
}
v___jp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_a_1116_);
lean_ctor_set(v___x_1121_, 0, v___y_1124_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___y_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1116_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v_a_1115_ = v_tail_1119_;
v_a_1116_ = v___x_1126_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1147_, lean_object* v_descr_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1147_, v_descr_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1147_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
if (lean_obj_tag(v_a_1155_) == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_a_1154_);
lean_dec_ref(v_descr_1153_);
v___x_1157_ = l_List_reverse___redArg(v_a_1156_);
return v___x_1157_;
}
else
{
lean_object* v_head_1158_; lean_object* v_tail_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1180_; 
v_head_1158_ = lean_ctor_get(v_a_1155_, 0);
v_tail_1159_ = lean_ctor_get(v_a_1155_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_1155_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1161_ = v_a_1155_;
v_isShared_1162_ = v_isSharedCheck_1180_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_tail_1159_);
lean_inc(v_head_1158_);
lean_dec(v_a_1155_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1180_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_addEntry_1163_; lean_object* v_state_1164_; lean_object* v_activeScopes_1165_; uint8_t v_delimitsLocal_1166_; uint8_t v_scopeChanged_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1179_; 
v_addEntry_1163_ = lean_ctor_get(v_descr_1153_, 4);
v_state_1164_ = lean_ctor_get(v_head_1158_, 0);
v_activeScopes_1165_ = lean_ctor_get(v_head_1158_, 1);
v_delimitsLocal_1166_ = lean_ctor_get_uint8(v_head_1158_, sizeof(void*)*2);
v_scopeChanged_1167_ = lean_ctor_get_uint8(v_head_1158_, sizeof(void*)*2 + 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_head_1158_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1169_ = v_head_1158_;
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_activeScopes_1165_);
lean_inc(v_state_1164_);
lean_dec(v_head_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc(v_addEntry_1163_);
lean_inc(v_a_1154_);
v___x_1171_ = lean_apply_2(v_addEntry_1163_, v_state_1164_, v_a_1154_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_activeScopes_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1178_, sizeof(void*)*2, v_delimitsLocal_1166_);
lean_ctor_set_uint8(v_reuseFailAlloc_1178_, sizeof(void*)*2 + 1, v_scopeChanged_1167_);
v___x_1173_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v_a_1156_);
lean_ctor_set(v___x_1161_, 0, v___x_1173_);
v___x_1175_ = v___x_1161_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_a_1156_);
v___x_1175_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
v_a_1155_ = v_tail_1159_;
v_a_1156_ = v___x_1175_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1181_, lean_object* v_s_1182_, lean_object* v_e_1183_){
_start:
{
if (lean_obj_tag(v_e_1183_) == 0)
{
lean_object* v_stateStack_1184_; lean_object* v_scopedEntries_1185_; lean_object* v_newEntries_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1206_; 
v_stateStack_1184_ = lean_ctor_get(v_s_1182_, 0);
v_scopedEntries_1185_ = lean_ctor_get(v_s_1182_, 1);
v_newEntries_1186_ = lean_ctor_get(v_s_1182_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_s_1182_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1188_ = v_s_1182_;
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_newEntries_1186_);
lean_inc(v_scopedEntries_1185_);
lean_inc(v_stateStack_1184_);
lean_dec(v_s_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1205_; 
v_a_1190_ = lean_ctor_get(v_e_1183_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_e_1183_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1192_ = v_e_1183_;
v_isShared_1193_ = v_isSharedCheck_1205_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v_e_1183_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1205_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_toOLeanEntry_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_toOLeanEntry_1194_ = lean_ctor_get(v_descr_1181_, 3);
lean_inc(v_toOLeanEntry_1194_);
v___x_1195_ = lean_box(0);
lean_inc(v_a_1190_);
v___x_1196_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1181_, v_a_1190_, v_stateStack_1184_, v___x_1195_);
v___x_1197_ = lean_apply_1(v_toOLeanEntry_1194_, v_a_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1197_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_newEntries_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 2, v___x_1200_);
lean_ctor_set(v___x_1188_, 0, v___x_1196_);
v___x_1202_ = v___x_1188_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_scopedEntries_1185_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1207_; lean_object* v_scopedEntries_1208_; lean_object* v_newEntries_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1231_; 
v_stateStack_1207_ = lean_ctor_get(v_s_1182_, 0);
v_scopedEntries_1208_ = lean_ctor_get(v_s_1182_, 1);
v_newEntries_1209_ = lean_ctor_get(v_s_1182_, 2);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_s_1182_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1211_ = v_s_1182_;
v_isShared_1212_ = v_isSharedCheck_1231_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_newEntries_1209_);
lean_inc(v_scopedEntries_1208_);
lean_inc(v_stateStack_1207_);
lean_dec(v_s_1182_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1231_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
v_a_1213_ = lean_ctor_get(v_e_1183_, 0);
v_a_1214_ = lean_ctor_get(v_e_1183_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_e_1183_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1216_ = v_e_1183_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v_e_1183_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_toOLeanEntry_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v_toOLeanEntry_1218_ = lean_ctor_get(v_descr_1181_, 3);
lean_inc(v_toOLeanEntry_1218_);
v___x_1219_ = lean_box(0);
lean_inc_n(v_a_1214_, 2);
v___x_1220_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1213_, v_descr_1181_, v_a_1214_, v_stateStack_1207_, v___x_1219_);
lean_inc(v_a_1213_);
v___x_1221_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1208_, v_a_1213_, v_a_1214_);
v___x_1222_ = lean_apply_1(v_toOLeanEntry_1218_, v_a_1214_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1222_);
v___x_1224_ = v___x_1216_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1213_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_newEntries_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 2, v___x_1225_);
lean_ctor_set(v___x_1211_, 1, v___x_1221_);
lean_ctor_set(v___x_1211_, 0, v___x_1220_);
v___x_1227_ = v___x_1211_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1232_, lean_object* v_00_u03b2_1233_, lean_object* v_00_u03c3_1234_, lean_object* v_descr_1235_, lean_object* v_s_1236_, lean_object* v_e_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1235_, v_s_1236_, v_e_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1239_, lean_object* v_00_u03b2_1240_, lean_object* v_00_u03b1_1241_, lean_object* v_descr_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1247_, lean_object* v_a_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_00_u03b1_1250_, lean_object* v_descr_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1248_, v_descr_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1256_, lean_object* v_a_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_00_u03b1_1259_, lean_object* v_descr_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1256_, v_a_1257_, v_00_u03b2_1258_, v_00_u03b1_1259_, v_descr_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1265_, lean_object* v_env_1266_, lean_object* v_as_1267_, size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_b_1270_){
_start:
{
lean_object* v_a_1272_; uint8_t v___x_1276_; 
v___x_1276_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_env_1266_);
lean_dec_ref(v_descr_1265_);
return v_b_1270_;
}
else
{
lean_object* v_snd_1277_; lean_object* v_fst_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1378_; 
v_snd_1277_ = lean_ctor_get(v_b_1270_, 1);
v_fst_1278_ = lean_ctor_get(v_b_1270_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_b_1270_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1280_ = v_b_1270_;
v_isShared_1281_ = v_isSharedCheck_1378_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1278_);
lean_dec(v_b_1270_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1378_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1377_; 
v_fst_1282_ = lean_ctor_get(v_snd_1277_, 0);
v_snd_1283_ = lean_ctor_get(v_snd_1277_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_snd_1277_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1285_ = v_snd_1277_;
v_isShared_1286_ = v_isSharedCheck_1377_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v_snd_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1377_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_array_uget(v_as_1267_, v_i_1269_);
if (lean_obj_tag(v_a_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1337_; 
v_a_1288_ = lean_ctor_get(v_a_1287_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1290_ = v_a_1287_;
v_isShared_1291_ = v_isSharedCheck_1337_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v_a_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1337_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_exportEntry_x3f_1292_; lean_object* v___x_1293_; lean_object* v_exported_1294_; lean_object* v_server_1295_; lean_object* v_private_1296_; lean_object* v___y_1298_; lean_object* v_server_1299_; lean_object* v_exported_1318_; 
v_exportEntry_x3f_1292_ = lean_ctor_get(v_descr_1265_, 6);
lean_inc_ref(v_exportEntry_x3f_1292_);
lean_inc_ref(v_env_1266_);
v___x_1293_ = lean_apply_2(v_exportEntry_x3f_1292_, v_env_1266_, v_a_1288_);
v_exported_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_exported_1294_);
v_server_1295_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_server_1295_);
v_private_1296_ = lean_ctor_get(v___x_1293_, 2);
lean_inc(v_private_1296_);
lean_dec_ref(v___x_1293_);
if (lean_obj_tag(v_exported_1294_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1336_; 
v_val_1328_ = lean_ctor_get(v_exported_1294_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_exported_1294_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1330_ = v_exported_1294_;
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v_exported_1294_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 0);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_val_1328_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_array_push(v_fst_1278_, v___x_1333_);
v_exported_1318_ = v___x_1334_;
goto v___jp_1317_;
}
}
}
else
{
lean_dec(v_exported_1294_);
v_exported_1318_ = v_fst_1278_;
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
lean_ctor_set(v___x_1290_, 0, v_val_1300_);
v___x_1302_ = v___x_1290_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_val_1300_);
v___x_1302_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_array_push(v_snd_1283_, v___x_1302_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1303_);
lean_ctor_set(v___x_1285_, 0, v_server_1299_);
v___x_1305_ = v___x_1285_;
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
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1305_);
lean_ctor_set(v___x_1280_, 0, v___y_1298_);
v___x_1307_ = v___x_1280_;
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
v_a_1272_ = v___x_1307_;
goto v___jp_1271_;
}
}
}
}
else
{
lean_object* v___x_1312_; 
lean_dec(v_private_1296_);
lean_del_object(v___x_1290_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_server_1299_);
v___x_1312_ = v___x_1285_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_server_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1283_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1312_);
lean_ctor_set(v___x_1280_, 0, v___y_1298_);
v___x_1314_ = v___x_1280_;
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
v_a_1272_ = v___x_1314_;
goto v___jp_1271_;
}
}
}
}
v___jp_1317_:
{
if (lean_obj_tag(v_server_1295_) == 1)
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_val_1319_ = lean_ctor_get(v_server_1295_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_server_1295_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v_server_1295_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v_server_1295_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_val_1319_);
v___x_1324_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_array_push(v_fst_1282_, v___x_1324_);
v___y_1298_ = v_exported_1318_;
v_server_1299_ = v___x_1325_;
goto v___jp_1297_;
}
}
}
else
{
lean_dec(v_server_1295_);
v___y_1298_ = v_exported_1318_;
v_server_1299_ = v_fst_1282_;
goto v___jp_1297_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1376_; 
v_a_1338_ = lean_ctor_get(v_a_1287_, 0);
v_a_1339_ = lean_ctor_get(v_a_1287_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1341_ = v_a_1287_;
v_isShared_1342_ = v_isSharedCheck_1376_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_inc(v_a_1338_);
lean_dec(v_a_1287_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1376_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_exportEntry_x3f_1343_; lean_object* v___x_1344_; lean_object* v_exported_1345_; lean_object* v_server_1346_; lean_object* v_private_1347_; lean_object* v___y_1349_; lean_object* v_server_1350_; lean_object* v_exported_1369_; 
v_exportEntry_x3f_1343_ = lean_ctor_get(v_descr_1265_, 6);
lean_inc_ref(v_exportEntry_x3f_1343_);
lean_inc_ref(v_env_1266_);
v___x_1344_ = lean_apply_2(v_exportEntry_x3f_1343_, v_env_1266_, v_a_1339_);
v_exported_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_exported_1345_);
v_server_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_server_1346_);
v_private_1347_ = lean_ctor_get(v___x_1344_, 2);
lean_inc(v_private_1347_);
lean_dec_ref(v___x_1344_);
if (lean_obj_tag(v_exported_1345_) == 1)
{
lean_object* v_val_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_val_1373_ = lean_ctor_get(v_exported_1345_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v_exported_1345_, 1);
lean_inc(v_a_1338_);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1338_);
lean_ctor_set(v___x_1374_, 1, v_val_1373_);
v___x_1375_ = lean_array_push(v_fst_1278_, v___x_1374_);
v_exported_1369_ = v___x_1375_;
goto v___jp_1368_;
}
else
{
lean_dec(v_exported_1345_);
v_exported_1369_ = v_fst_1278_;
goto v___jp_1368_;
}
v___jp_1348_:
{
if (lean_obj_tag(v_private_1347_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1353_; 
v_val_1351_ = lean_ctor_get(v_private_1347_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_private_1347_, 1);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_val_1351_);
v___x_1353_ = v___x_1341_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1338_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_val_1351_);
v___x_1353_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_array_push(v_snd_1283_, v___x_1353_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1354_);
lean_ctor_set(v___x_1285_, 0, v_server_1350_);
v___x_1356_ = v___x_1285_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_server_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1356_);
lean_ctor_set(v___x_1280_, 0, v___y_1349_);
v___x_1358_ = v___x_1280_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___y_1349_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v_a_1272_ = v___x_1358_;
goto v___jp_1271_;
}
}
}
}
else
{
lean_object* v___x_1363_; 
lean_dec(v_private_1347_);
lean_del_object(v___x_1341_);
lean_dec(v_a_1338_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_server_1350_);
v___x_1363_ = v___x_1285_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_server_1350_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1283_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1363_);
lean_ctor_set(v___x_1280_, 0, v___y_1349_);
v___x_1365_ = v___x_1280_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___y_1349_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_a_1272_ = v___x_1365_;
goto v___jp_1271_;
}
}
}
}
v___jp_1368_:
{
if (lean_obj_tag(v_server_1346_) == 1)
{
lean_object* v_val_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_val_1370_ = lean_ctor_get(v_server_1346_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v_server_1346_, 1);
lean_inc(v_a_1338_);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1338_);
lean_ctor_set(v___x_1371_, 1, v_val_1370_);
v___x_1372_ = lean_array_push(v_fst_1282_, v___x_1371_);
v___y_1349_ = v_exported_1369_;
v_server_1350_ = v___x_1372_;
goto v___jp_1348_;
}
else
{
lean_dec(v_server_1346_);
v___y_1349_ = v_exported_1369_;
v_server_1350_ = v_fst_1282_;
goto v___jp_1348_;
}
}
}
}
}
}
}
v___jp_1271_:
{
size_t v___x_1273_; size_t v___x_1274_; 
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1269_, v___x_1273_);
v_i_1269_ = v___x_1274_;
v_b_1270_ = v_a_1272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1379_, lean_object* v_env_1380_, lean_object* v_as_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_b_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1379_, v_env_1380_, v_as_1381_, v_sz_boxed_1385_, v_i_boxed_1386_, v_b_1384_);
lean_dec_ref(v_as_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1395_, lean_object* v_env_1396_, lean_object* v_s_1397_){
_start:
{
lean_object* v_newEntries_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1415_; 
v_newEntries_1398_ = lean_ctor_get(v_s_1397_, 2);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_s_1397_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; lean_object* v_unused_1417_; 
v_unused_1416_ = lean_ctor_get(v_s_1397_, 1);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_s_1397_, 0);
lean_dec(v_unused_1417_);
v___x_1400_ = v_s_1397_;
v_isShared_1401_ = v_isSharedCheck_1415_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_newEntries_1398_);
lean_dec(v_s_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1415_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; size_t v_sz_1405_; size_t v___x_1406_; lean_object* v___x_1407_; lean_object* v_snd_1408_; lean_object* v_fst_1409_; lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1413_; 
v___x_1402_ = lean_array_mk(v_newEntries_1398_);
v___x_1403_ = l_Array_reverse___redArg(v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1405_ = lean_array_size(v___x_1403_);
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1395_, v_env_1396_, v___x_1403_, v_sz_1405_, v___x_1406_, v___x_1404_);
lean_dec_ref(v___x_1403_);
v_snd_1408_ = lean_ctor_get(v___x_1407_, 1);
lean_inc(v_snd_1408_);
v_fst_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_fst_1409_);
lean_dec_ref(v___x_1407_);
v_fst_1410_ = lean_ctor_get(v_snd_1408_, 0);
lean_inc(v_fst_1410_);
v_snd_1411_ = lean_ctor_get(v_snd_1408_, 1);
lean_inc(v_snd_1411_);
lean_dec(v_snd_1408_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v_snd_1411_);
lean_ctor_set(v___x_1400_, 1, v_fst_1410_);
lean_ctor_set(v___x_1400_, 0, v_fst_1409_);
v___x_1413_ = v___x_1400_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_fst_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_fst_1410_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_snd_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1418_, lean_object* v_00_u03b2_1419_, lean_object* v_00_u03c3_1420_, lean_object* v_descr_1421_, lean_object* v_env_1422_, lean_object* v_s_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1421_, v_env_1422_, v_s_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_00_u03c3_1427_, lean_object* v_descr_1428_, lean_object* v_env_1429_, lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1428_, v_env_1429_, v_as_1430_, v_sz_1431_, v_i_1432_, v_b_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_00_u03c3_1437_, lean_object* v_descr_1438_, lean_object* v_env_1439_, lean_object* v_as_1440_, lean_object* v_sz_1441_, lean_object* v_i_1442_, lean_object* v_b_1443_){
_start:
{
size_t v_sz_boxed_1444_; size_t v_i_boxed_1445_; lean_object* v_res_1446_; 
v_sz_boxed_1444_ = lean_unbox_usize(v_sz_1441_);
lean_dec(v_sz_1441_);
v_i_boxed_1445_ = lean_unbox_usize(v_i_1442_);
lean_dec(v_i_1442_);
v_res_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1435_, v_00_u03b2_1436_, v_00_u03c3_1437_, v_descr_1438_, v_env_1439_, v_as_1440_, v_sz_boxed_1444_, v_i_boxed_1445_, v_b_1443_);
lean_dec_ref(v_as_1440_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1452_, v___y_1453_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_x_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1456_, lean_object* v_x_1457_){
_start:
{
lean_inc_ref(v_s_1456_);
return v_s_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1458_, v_x_1459_);
lean_dec_ref(v_x_1459_);
lean_dec_ref(v_s_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1466_, v_x_1467_);
lean_dec_ref(v_x_1467_);
lean_dec_ref(v_x_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_box(0);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1471_);
lean_dec_ref(v_x_1471_);
return v_res_1472_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___f_1478_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1479_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1480_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1481_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v___f_1481_);
lean_ctor_set(v___x_1484_, 3, v___f_1480_);
lean_ctor_set(v___x_1484_, 4, v___f_1479_);
lean_ctor_set(v___x_1484_, 5, v___f_1478_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1485_){
_start:
{
lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___f_1486_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1487_, 0, v_inst_1485_);
v___f_1488_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1489_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1492_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1493_ = 0;
v___x_1494_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v___x_1491_);
lean_ctor_set(v___x_1494_, 2, v___f_1486_);
lean_ctor_set(v___x_1494_, 3, v___f_1487_);
lean_ctor_set(v___x_1494_, 4, v___f_1488_);
lean_ctor_set(v___x_1494_, 5, v___x_1492_);
lean_ctor_set(v___x_1494_, 6, v___f_1489_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*7, v___x_1493_);
v___x_1495_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_00_u03c3_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1504_, lean_object* v_inst_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1513_ = lean_st_mk_ref(v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1520_){
_start:
{
lean_object* v_newEntries_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_newEntries_1521_ = lean_ctor_get(v_s_1520_, 2);
v___x_1522_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1523_ = l_List_lengthTR___redArg(v_newEntries_1521_);
v___x_1524_ = l_Nat_reprFast(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1522_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1527_);
lean_dec_ref(v_s_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1531_);
lean_dec_ref(v_x_1531_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1535_){
_start:
{
lean_object* v_name_1537_; uint8_t v_trackGen_1538_; lean_object* v___f_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_name_1537_ = lean_ctor_get(v_descr_1535_, 0);
v_trackGen_1538_ = lean_ctor_get_uint8(v_descr_1535_, sizeof(void*)*7);
v___f_1539_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1540_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1535_, 4);
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1541_, 0, lean_box(0));
lean_closure_set(v___x_1541_, 1, lean_box(0));
lean_closure_set(v___x_1541_, 2, lean_box(0));
lean_closure_set(v___x_1541_, 3, v_descr_1535_);
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1542_, 0, lean_box(0));
lean_closure_set(v___x_1542_, 1, lean_box(0));
lean_closure_set(v___x_1542_, 2, lean_box(0));
lean_closure_set(v___x_1542_, 3, v_descr_1535_);
v___x_1543_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1543_, 0, lean_box(0));
lean_closure_set(v___x_1543_, 1, lean_box(0));
lean_closure_set(v___x_1543_, 2, lean_box(0));
lean_closure_set(v___x_1543_, 3, v_descr_1535_);
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, lean_box(0));
lean_closure_set(v___x_1544_, 2, lean_box(0));
lean_closure_set(v___x_1544_, 3, v_descr_1535_);
v___x_1545_ = lean_box(2);
v___x_1546_ = lean_box(0);
lean_inc(v_name_1537_);
v___x_1547_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1547_, 0, v_name_1537_);
lean_ctor_set(v___x_1547_, 1, v___x_1541_);
lean_ctor_set(v___x_1547_, 2, v___x_1542_);
lean_ctor_set(v___x_1547_, 3, v___x_1543_);
lean_ctor_set(v___x_1547_, 4, v___x_1544_);
lean_ctor_set(v___x_1547_, 5, v___f_1539_);
lean_ctor_set(v___x_1547_, 6, v___x_1545_);
lean_ctor_set(v___x_1547_, 7, v___x_1546_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*8, v_trackGen_1538_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___f_1540_);
v___x_1549_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1562_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1562_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1562_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_descr_1535_);
lean_ctor_set(v___x_1554_, 1, v_a_1550_);
v___x_1555_ = l_Lean_scopedEnvExtensionsRef;
v___x_1556_ = lean_st_ref_take(v___x_1555_);
lean_inc_ref(v___x_1554_);
v___x_1557_ = lean_array_push(v___x_1556_, v___x_1554_);
v___x_1558_ = lean_st_ref_put(v___x_1555_, v___x_1557_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1554_);
v___x_1560_ = v___x_1552_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1554_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_descr_1535_);
v_a_1563_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1549_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1549_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_00_u03c3_1576_, lean_object* v_descr_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_00_u03c3_1582_, lean_object* v_descr_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1580_, v_00_u03b2_1581_, v_00_u03c3_1582_, v_descr_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1586_){
_start:
{
lean_object* v_stateStack_1587_; 
v_stateStack_1587_ = lean_ctor_get(v_s_1586_, 0);
if (lean_obj_tag(v_stateStack_1587_) == 0)
{
return v_s_1586_;
}
else
{
lean_object* v_head_1588_; lean_object* v_scopedEntries_1589_; lean_object* v_newEntries_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1609_; 
lean_inc_ref(v_stateStack_1587_);
v_head_1588_ = lean_ctor_get(v_stateStack_1587_, 0);
lean_inc(v_head_1588_);
v_scopedEntries_1589_ = lean_ctor_get(v_s_1586_, 1);
v_newEntries_1590_ = lean_ctor_get(v_s_1586_, 2);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_s_1586_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_s_1586_, 0);
lean_dec(v_unused_1610_);
v___x_1592_ = v_s_1586_;
v_isShared_1593_ = v_isSharedCheck_1609_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_newEntries_1590_);
lean_inc(v_scopedEntries_1589_);
lean_dec(v_s_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1609_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_state_1594_; lean_object* v_activeScopes_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1608_; 
v_state_1594_ = lean_ctor_get(v_head_1588_, 0);
v_activeScopes_1595_ = lean_ctor_get(v_head_1588_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_head_1588_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1597_ = v_head_1588_;
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_activeScopes_1595_);
lean_inc(v_state_1594_);
lean_dec(v_head_1588_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
uint8_t v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = 1;
v___x_1600_ = 0;
if (v_isShared_1598_ == 0)
{
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_state_1594_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_activeScopes_1595_);
v___x_1602_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2, v___x_1599_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2 + 1, v___x_1600_);
v___x_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_stateStack_1587_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1603_);
v___x_1605_ = v___x_1592_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_scopedEntries_1589_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_newEntries_1590_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1612_, lean_object* v_env_1613_){
_start:
{
lean_object* v_ext_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v_ext_1614_ = lean_ctor_get(v_ext_1612_, 1);
lean_inc_ref(v_ext_1614_);
lean_dec_ref(v_ext_1612_);
v___f_1615_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1616_ = lean_box(1);
v___x_1617_ = lean_box(0);
v___x_1618_ = 0;
v___x_1619_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1614_, v_env_1613_, v___f_1615_, v___x_1616_, v___x_1617_, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_00_u03c3_1622_, lean_object* v_ext_1623_, lean_object* v_env_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1623_, v_env_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_tail_1626_, lean_object* v_s_1627_){
_start:
{
lean_object* v_scopedEntries_1628_; lean_object* v_newEntries_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_scopedEntries_1628_ = lean_ctor_get(v_s_1627_, 1);
v_newEntries_1629_ = lean_ctor_get(v_s_1627_, 2);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_s_1627_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; 
v_unused_1637_ = lean_ctor_get(v_s_1627_, 0);
lean_dec(v_unused_1637_);
v___x_1631_ = v_s_1627_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_newEntries_1629_);
lean_inc(v_scopedEntries_1628_);
lean_dec(v_s_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_tail_1626_);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_tail_1626_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_scopedEntries_1628_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_newEntries_1629_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1638_, lean_object* v_env_1639_){
_start:
{
lean_object* v_ext_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_stateStack_1645_; 
v_ext_1640_ = lean_ctor_get(v_ext_1638_, 1);
lean_inc_ref(v_ext_1640_);
lean_dec_ref(v_ext_1638_);
v___x_1641_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1642_ = lean_box(1);
v___x_1643_ = lean_box(0);
lean_inc_ref(v_env_1639_);
v___x_1644_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1641_, v_ext_1640_, v_env_1639_, v___x_1642_, v___x_1643_);
v_stateStack_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_stateStack_1645_);
lean_dec(v___x_1644_);
if (lean_obj_tag(v_stateStack_1645_) == 1)
{
lean_object* v_tail_1646_; 
v_tail_1646_ = lean_ctor_get(v_stateStack_1645_, 1);
lean_inc(v_tail_1646_);
if (lean_obj_tag(v_tail_1646_) == 1)
{
lean_object* v_head_1647_; uint8_t v_scopeChanged_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; 
v_head_1647_ = lean_ctor_get(v_stateStack_1645_, 0);
lean_inc(v_head_1647_);
lean_dec_ref_known(v_stateStack_1645_, 2);
v_scopeChanged_1648_ = lean_ctor_get_uint8(v_head_1647_, sizeof(void*)*2 + 1);
lean_dec(v_head_1647_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1649_, 0, v_tail_1646_);
v___x_1650_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1640_, v_env_1639_, v___f_1649_, v___x_1642_, v___x_1643_, v_scopeChanged_1648_);
return v___x_1650_;
}
else
{
lean_dec_ref_known(v_stateStack_1645_, 2);
lean_dec(v_tail_1646_);
lean_dec_ref(v_ext_1640_);
return v_env_1639_;
}
}
else
{
lean_dec(v_stateStack_1645_);
lean_dec_ref(v_ext_1640_);
return v_env_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1651_, lean_object* v_00_u03b2_1652_, lean_object* v_00_u03c3_1653_, lean_object* v_ext_1654_, lean_object* v_env_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1654_, v_env_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_zero_1659_; uint8_t v_isZero_1660_; 
v_zero_1659_ = lean_unsigned_to_nat(0u);
v_isZero_1660_ = lean_nat_dec_eq(v_a_1657_, v_zero_1659_);
if (v_isZero_1660_ == 1)
{
return v_a_1658_;
}
else
{
if (lean_obj_tag(v_a_1658_) == 0)
{
return v_a_1658_;
}
else
{
lean_object* v_head_1661_; lean_object* v_tail_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1682_; 
v_head_1661_ = lean_ctor_get(v_a_1658_, 0);
v_tail_1662_ = lean_ctor_get(v_a_1658_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1664_ = v_a_1658_;
v_isShared_1665_ = v_isSharedCheck_1682_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_tail_1662_);
lean_inc(v_head_1661_);
lean_dec(v_a_1658_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1682_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_state_1666_; lean_object* v_activeScopes_1667_; uint8_t v_scopeChanged_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1681_; 
v_state_1666_ = lean_ctor_get(v_head_1661_, 0);
v_activeScopes_1667_ = lean_ctor_get(v_head_1661_, 1);
v_scopeChanged_1668_ = lean_ctor_get_uint8(v_head_1661_, sizeof(void*)*2 + 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_head_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1670_ = v_head_1661_;
v_isShared_1671_ = v_isSharedCheck_1681_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_activeScopes_1667_);
lean_inc(v_state_1666_);
lean_dec(v_head_1661_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1681_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_one_1672_; lean_object* v_n_1673_; lean_object* v___x_1675_; 
v_one_1672_ = lean_unsigned_to_nat(1u);
v_n_1673_ = lean_nat_sub(v_a_1657_, v_one_1672_);
if (v_isShared_1671_ == 0)
{
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_state_1666_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_activeScopes_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1680_, sizeof(void*)*2 + 1, v_scopeChanged_1668_);
v___x_1675_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*2, v_isZero_1660_);
v___x_1676_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1673_, v_tail_1662_);
lean_dec(v_n_1673_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1676_);
lean_ctor_set(v___x_1664_, 0, v___x_1675_);
v___x_1678_ = v___x_1664_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1683_, v_a_1684_);
lean_dec(v_a_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1687_, v_a_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1694_, lean_object* v_s_1695_){
_start:
{
lean_object* v_stateStack_1696_; lean_object* v_scopedEntries_1697_; lean_object* v_newEntries_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_stateStack_1696_ = lean_ctor_get(v_s_1695_, 0);
v_scopedEntries_1697_ = lean_ctor_get(v_s_1695_, 1);
v_newEntries_1698_ = lean_ctor_get(v_s_1695_, 2);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_s_1695_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v_s_1695_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_newEntries_1698_);
lean_inc(v_scopedEntries_1697_);
lean_inc(v_stateStack_1696_);
lean_dec(v_s_1695_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1694_, v_stateStack_1696_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_scopedEntries_1697_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_newEntries_1698_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1707_, lean_object* v_s_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1707_, v_s_1708_);
lean_dec(v_depth_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1710_, lean_object* v_env_1711_, lean_object* v_depth_1712_){
_start:
{
lean_object* v_ext_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v_ext_1713_ = lean_ctor_get(v_ext_1710_, 1);
lean_inc_ref(v_ext_1713_);
lean_dec_ref(v_ext_1710_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1714_, 0, v_depth_1712_);
v___x_1715_ = lean_box(1);
v___x_1716_ = lean_box(0);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1713_, v_env_1711_, v___f_1714_, v___x_1715_, v___x_1716_, v___x_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_00_u03c3_1721_, lean_object* v_ext_1722_, lean_object* v_env_1723_, lean_object* v_depth_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1722_, v_env_1723_, v_depth_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1726_, lean_object* v_env_1727_, lean_object* v_b_1728_){
_start:
{
lean_object* v_ext_1729_; lean_object* v_toEnvExtension_1730_; lean_object* v_asyncMode_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_ext_1729_ = lean_ctor_get(v_ext_1726_, 1);
lean_inc_ref(v_ext_1729_);
lean_dec_ref(v_ext_1726_);
v_toEnvExtension_1730_ = lean_ctor_get(v_ext_1729_, 0);
v_asyncMode_1731_ = lean_ctor_get(v_toEnvExtension_1730_, 2);
lean_inc(v_asyncMode_1731_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_b_1728_);
v___x_1733_ = lean_box(0);
v___x_1734_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1729_, v_env_1727_, v___x_1732_, v_asyncMode_1731_, v___x_1733_);
lean_dec(v_asyncMode_1731_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_00_u03c3_1737_, lean_object* v_ext_1738_, lean_object* v_env_1739_, lean_object* v_b_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1738_, v_env_1739_, v_b_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1742_, lean_object* v_env_1743_, lean_object* v_namespaceName_1744_, lean_object* v_b_1745_){
_start:
{
lean_object* v_ext_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1757_; 
v_ext_1746_ = lean_ctor_get(v_ext_1742_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_ext_1742_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_ext_1742_, 0);
lean_dec(v_unused_1758_);
v___x_1748_ = v_ext_1742_;
v_isShared_1749_ = v_isSharedCheck_1757_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_ext_1746_);
lean_dec(v_ext_1742_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1757_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_toEnvExtension_1750_; lean_object* v_asyncMode_1751_; lean_object* v___x_1753_; 
v_toEnvExtension_1750_ = lean_ctor_get(v_ext_1746_, 0);
v_asyncMode_1751_ = lean_ctor_get(v_toEnvExtension_1750_, 2);
lean_inc(v_asyncMode_1751_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 1);
lean_ctor_set(v___x_1748_, 1, v_b_1745_);
lean_ctor_set(v___x_1748_, 0, v_namespaceName_1744_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_namespaceName_1744_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_b_1745_);
v___x_1753_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1746_, v_env_1743_, v___x_1753_, v_asyncMode_1751_, v___x_1754_);
lean_dec(v_asyncMode_1751_);
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_00_u03c3_1761_, lean_object* v_ext_1762_, lean_object* v_env_1763_, lean_object* v_namespaceName_1764_, lean_object* v_b_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1762_, v_env_1763_, v_namespaceName_1764_, v_b_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1767_, lean_object* v_states_1768_, lean_object* v_b_1769_){
_start:
{
if (lean_obj_tag(v_states_1768_) == 0)
{
lean_dec(v_b_1769_);
lean_dec_ref(v_ext_1767_);
return v_states_1768_;
}
else
{
lean_object* v_descr_1770_; lean_object* v_head_1771_; lean_object* v_tail_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1798_; 
v_descr_1770_ = lean_ctor_get(v_ext_1767_, 0);
v_head_1771_ = lean_ctor_get(v_states_1768_, 0);
v_tail_1772_ = lean_ctor_get(v_states_1768_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_states_1768_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1774_ = v_states_1768_;
v_isShared_1775_ = v_isSharedCheck_1798_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_tail_1772_);
lean_inc(v_head_1771_);
lean_dec(v_states_1768_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1798_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_addEntry_1776_; lean_object* v_state_1777_; lean_object* v_activeScopes_1778_; uint8_t v_delimitsLocal_1779_; uint8_t v_scopeChanged_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1797_; 
v_addEntry_1776_ = lean_ctor_get(v_descr_1770_, 4);
v_state_1777_ = lean_ctor_get(v_head_1771_, 0);
v_activeScopes_1778_ = lean_ctor_get(v_head_1771_, 1);
v_delimitsLocal_1779_ = lean_ctor_get_uint8(v_head_1771_, sizeof(void*)*2);
v_scopeChanged_1780_ = lean_ctor_get_uint8(v_head_1771_, sizeof(void*)*2 + 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_head_1771_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1782_ = v_head_1771_;
v_isShared_1783_ = v_isSharedCheck_1797_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_activeScopes_1778_);
lean_inc(v_state_1777_);
lean_dec(v_head_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1797_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_inc(v_addEntry_1776_);
lean_inc(v_b_1769_);
v___x_1784_ = lean_apply_2(v_addEntry_1776_, v_state_1777_, v_b_1769_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_activeScopes_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, sizeof(void*)*2, v_delimitsLocal_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, sizeof(void*)*2 + 1, v_scopeChanged_1780_);
v___x_1786_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v_top_1787_; uint8_t v_delimitsLocal_1788_; 
v_top_1787_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1770_, v___x_1786_);
v_delimitsLocal_1788_ = lean_ctor_get_uint8(v_top_1787_, sizeof(void*)*2);
if (v_delimitsLocal_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = l_Lean_stateStackModify___redArg(v_ext_1767_, v_tail_1772_, v_b_1769_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v___x_1789_);
lean_ctor_set(v___x_1774_, 0, v_top_1787_);
v___x_1791_ = v___x_1774_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_top_1787_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_b_1769_);
lean_dec_ref(v_ext_1767_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v_top_1787_);
v___x_1794_ = v___x_1774_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_top_1787_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_tail_1772_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1799_, lean_object* v_00_u03b2_1800_, lean_object* v_00_u03c3_1801_, lean_object* v_ext_1802_, lean_object* v_states_1803_, lean_object* v_b_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_stateStackModify___redArg(v_ext_1802_, v_states_1803_, v_b_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1806_, lean_object* v_b_1807_, lean_object* v_s_1808_){
_start:
{
lean_object* v_stateStack_1809_; lean_object* v_scopedEntries_1810_; lean_object* v_newEntries_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_stateStack_1809_ = lean_ctor_get(v_s_1808_, 0);
v_scopedEntries_1810_ = lean_ctor_get(v_s_1808_, 1);
v_newEntries_1811_ = lean_ctor_get(v_s_1808_, 2);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_s_1808_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_s_1808_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_newEntries_1811_);
lean_inc(v_scopedEntries_1810_);
lean_inc(v_stateStack_1809_);
lean_dec(v_s_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = l_Lean_stateStackModify___redArg(v_ext_1806_, v_stateStack_1809_, v_b_1807_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_scopedEntries_1810_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_newEntries_1811_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1820_, lean_object* v_env_1821_, lean_object* v_b_1822_){
_start:
{
lean_object* v_ext_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
v_ext_1823_ = lean_ctor_get(v_ext_1820_, 1);
lean_inc_ref(v_ext_1823_);
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1824_, 0, v_ext_1820_);
lean_closure_set(v___f_1824_, 1, v_b_1822_);
v___x_1825_ = lean_box(1);
v___x_1826_ = lean_box(0);
v___x_1827_ = 1;
v___x_1828_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1823_, v_env_1821_, v___f_1824_, v___x_1825_, v___x_1826_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_00_u03c3_1831_, lean_object* v_ext_1832_, lean_object* v_env_1833_, lean_object* v_b_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1832_, v_env_1833_, v_b_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1836_, lean_object* v_ext_1837_, lean_object* v_b_1838_, uint8_t v_kind_1839_, lean_object* v_namespaceName_1840_){
_start:
{
switch(v_kind_1839_)
{
case 0:
{
lean_object* v___x_1841_; 
lean_dec(v_namespaceName_1840_);
v___x_1841_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1837_, v_env_1836_, v_b_1838_);
return v___x_1841_;
}
case 1:
{
lean_object* v___x_1842_; 
lean_dec(v_namespaceName_1840_);
v___x_1842_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1837_, v_env_1836_, v_b_1838_);
return v___x_1842_;
}
default: 
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1837_, v_env_1836_, v_namespaceName_1840_, v_b_1838_);
return v___x_1843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1844_, lean_object* v_ext_1845_, lean_object* v_b_1846_, lean_object* v_kind_1847_, lean_object* v_namespaceName_1848_){
_start:
{
uint8_t v_kind_boxed_1849_; lean_object* v_res_1850_; 
v_kind_boxed_1849_ = lean_unbox(v_kind_1847_);
v_res_1850_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1844_, v_ext_1845_, v_b_1846_, v_kind_boxed_1849_, v_namespaceName_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_00_u03c3_1853_, lean_object* v_env_1854_, lean_object* v_ext_1855_, lean_object* v_b_1856_, uint8_t v_kind_1857_, lean_object* v_namespaceName_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1854_, v_ext_1855_, v_b_1856_, v_kind_1857_, v_namespaceName_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_00_u03c3_1862_, lean_object* v_env_1863_, lean_object* v_ext_1864_, lean_object* v_b_1865_, lean_object* v_kind_1866_, lean_object* v_namespaceName_1867_){
_start:
{
uint8_t v_kind_boxed_1868_; lean_object* v_res_1869_; 
v_kind_boxed_1868_ = lean_unbox(v_kind_1866_);
v_res_1869_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1860_, v_00_u03b2_1861_, v_00_u03c3_1862_, v_env_1863_, v_ext_1864_, v_b_1865_, v_kind_boxed_1868_, v_namespaceName_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1870_, lean_object* v_b_1871_, uint8_t v_kind_1872_, lean_object* v_ns_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1874_, v_ext_1870_, v_b_1871_, v_kind_1872_, v_ns_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1876_, lean_object* v_b_1877_, lean_object* v_kind_1878_, lean_object* v_ns_1879_, lean_object* v_x_1880_){
_start:
{
uint8_t v_kind_boxed_1881_; lean_object* v_res_1882_; 
v_kind_boxed_1881_ = lean_unbox(v_kind_1878_);
v_res_1882_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1876_, v_b_1877_, v_kind_boxed_1881_, v_ns_1879_, v_x_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1883_, lean_object* v_ext_1884_, lean_object* v_b_1885_, uint8_t v_kind_1886_, lean_object* v_ns_1887_){
_start:
{
lean_object* v_modifyEnv_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
v_modifyEnv_1888_ = lean_ctor_get(v_inst_1883_, 1);
lean_inc(v_modifyEnv_1888_);
lean_dec_ref(v_inst_1883_);
v___x_1889_ = lean_box(v_kind_1886_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1890_, 0, v_ext_1884_);
lean_closure_set(v___f_1890_, 1, v_b_1885_);
lean_closure_set(v___f_1890_, 2, v___x_1889_);
lean_closure_set(v___f_1890_, 3, v_ns_1887_);
v___x_1891_ = lean_apply_1(v_modifyEnv_1888_, v___f_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1892_, lean_object* v_ext_1893_, lean_object* v_b_1894_, lean_object* v_kind_1895_, lean_object* v_ns_1896_){
_start:
{
uint8_t v_kind_boxed_1897_; lean_object* v_res_1898_; 
v_kind_boxed_1897_ = lean_unbox(v_kind_1895_);
v_res_1898_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1892_, v_ext_1893_, v_b_1894_, v_kind_boxed_1897_, v_ns_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_ext_1902_, lean_object* v_b_1903_, uint8_t v_kind_1904_){
_start:
{
lean_object* v_toBind_1905_; lean_object* v_getCurrNamespace_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; 
v_toBind_1905_ = lean_ctor_get(v_inst_1899_, 1);
lean_inc(v_toBind_1905_);
lean_dec_ref(v_inst_1899_);
v_getCurrNamespace_1906_ = lean_ctor_get(v_inst_1900_, 0);
lean_inc(v_getCurrNamespace_1906_);
lean_dec_ref(v_inst_1900_);
v___x_1907_ = lean_box(v_kind_1904_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1908_, 0, v_inst_1901_);
lean_closure_set(v___f_1908_, 1, v_ext_1902_);
lean_closure_set(v___f_1908_, 2, v_b_1903_);
lean_closure_set(v___f_1908_, 3, v___x_1907_);
v___x_1909_ = lean_apply_4(v_toBind_1905_, lean_box(0), lean_box(0), v_getCurrNamespace_1906_, v___f_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_ext_1913_, lean_object* v_b_1914_, lean_object* v_kind_1915_){
_start:
{
uint8_t v_kind_boxed_1916_; lean_object* v_res_1917_; 
v_kind_boxed_1916_ = lean_unbox(v_kind_1915_);
v_res_1917_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1910_, v_inst_1911_, v_inst_1912_, v_ext_1913_, v_b_1914_, v_kind_boxed_1916_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1918_, lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_ext_1925_, lean_object* v_b_1926_, uint8_t v_kind_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1922_, v_inst_1923_, v_inst_1924_, v_ext_1925_, v_b_1926_, v_kind_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1929_, lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_00_u03c3_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_ext_1936_, lean_object* v_b_1937_, lean_object* v_kind_1938_){
_start:
{
uint8_t v_kind_boxed_1939_; lean_object* v_res_1940_; 
v_kind_boxed_1939_ = lean_unbox(v_kind_1938_);
v_res_1940_ = l_Lean_ScopedEnvExtension_add(v_m_1929_, v_00_u03b1_1930_, v_00_u03b2_1931_, v_00_u03c3_1932_, v_inst_1933_, v_inst_1934_, v_inst_1935_, v_ext_1936_, v_b_1937_, v_kind_boxed_1939_);
return v_res_1940_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1944_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1945_ = lean_unsigned_to_nat(16u);
v___x_1946_ = lean_unsigned_to_nat(227u);
v___x_1947_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1948_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1949_ = l_mkPanicMessageWithDecl(v___x_1948_, v___x_1947_, v___x_1946_, v___x_1945_, v___x_1944_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1950_, lean_object* v_ext_1951_, lean_object* v_env_1952_, lean_object* v_asyncMode_1953_){
_start:
{
lean_object* v_ext_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_stateStack_1958_; 
v_ext_1954_ = lean_ctor_get(v_ext_1951_, 1);
v___x_1955_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1956_ = lean_box(0);
v___x_1957_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1955_, v_ext_1954_, v_env_1952_, v_asyncMode_1953_, v___x_1956_);
v_stateStack_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_stateStack_1958_);
lean_dec(v___x_1957_);
if (lean_obj_tag(v_stateStack_1958_) == 1)
{
lean_object* v_head_1959_; lean_object* v_state_1960_; 
v_head_1959_ = lean_ctor_get(v_stateStack_1958_, 0);
lean_inc(v_head_1959_);
lean_dec_ref_known(v_stateStack_1958_, 2);
v_state_1960_ = lean_ctor_get(v_head_1959_, 0);
lean_inc(v_state_1960_);
lean_dec(v_head_1959_);
return v_state_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_stateStack_1958_);
v___x_1961_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1962_ = l_panic___redArg(v_inst_1950_, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1963_, lean_object* v_ext_1964_, lean_object* v_env_1965_, lean_object* v_asyncMode_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1963_, v_ext_1964_, v_env_1965_, v_asyncMode_1966_);
lean_dec(v_asyncMode_1966_);
lean_dec_ref(v_ext_1964_);
lean_dec(v_inst_1963_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1968_, lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_inst_1971_, lean_object* v_ext_1972_, lean_object* v_env_1973_, lean_object* v_asyncMode_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1971_, v_ext_1972_, v_env_1973_, v_asyncMode_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1976_, lean_object* v_00_u03b1_1977_, lean_object* v_00_u03b2_1978_, lean_object* v_inst_1979_, lean_object* v_ext_1980_, lean_object* v_env_1981_, lean_object* v_asyncMode_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1976_, v_00_u03b1_1977_, v_00_u03b2_1978_, v_inst_1979_, v_ext_1980_, v_env_1981_, v_asyncMode_1982_);
lean_dec(v_asyncMode_1982_);
lean_dec_ref(v_ext_1980_);
lean_dec(v_inst_1979_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v___y_1984_, lean_object* v_tail_1985_, lean_object* v_s_1986_){
_start:
{
lean_object* v_scopedEntries_1987_; lean_object* v_newEntries_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_scopedEntries_1987_ = lean_ctor_get(v_s_1986_, 1);
v_newEntries_1988_ = lean_ctor_get(v_s_1986_, 2);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_s_1986_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v_s_1986_, 0);
lean_dec(v_unused_1997_);
v___x_1990_ = v_s_1986_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_newEntries_1988_);
lean_inc(v_scopedEntries_1987_);
lean_dec(v_s_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1984_);
lean_ctor_set(v___x_1992_, 1, v_tail_1985_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_scopedEntries_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_newEntries_1988_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v___x_1998_, lean_object* v_as_1999_, size_t v_i_2000_, size_t v_stop_2001_, lean_object* v_b_2002_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_eq(v_i_2000_, v_stop_2001_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; size_t v___x_2006_; size_t v___x_2007_; 
v___x_2004_ = lean_array_uget_borrowed(v_as_1999_, v_i_2000_);
lean_inc(v___x_1998_);
lean_inc(v___x_2004_);
v___x_2005_ = lean_apply_2(v___x_1998_, v_b_2002_, v___x_2004_);
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_add(v_i_2000_, v___x_2006_);
v_i_2000_ = v___x_2007_;
v_b_2002_ = v___x_2005_;
goto _start;
}
else
{
lean_dec(v___x_1998_);
return v_b_2002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v___x_2009_, lean_object* v_as_2010_, lean_object* v_i_2011_, lean_object* v_stop_2012_, lean_object* v_b_2013_){
_start:
{
size_t v_i_boxed_2014_; size_t v_stop_boxed_2015_; lean_object* v_res_2016_; 
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_stop_boxed_2015_ = lean_unbox_usize(v_stop_2012_);
lean_dec(v_stop_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2009_, v_as_2010_, v_i_boxed_2014_, v_stop_boxed_2015_, v_b_2013_);
lean_dec_ref(v_as_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object* v___x_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_){
_start:
{
if (lean_obj_tag(v_x_2018_) == 0)
{
lean_object* v_cs_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_cs_2020_ = lean_ctor_get(v_x_2018_, 0);
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_array_get_size(v_cs_2020_);
v___x_2023_ = lean_nat_dec_lt(v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_dec(v___x_2017_);
return v_x_2019_;
}
else
{
size_t v___x_2024_; size_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = lean_usize_of_nat(v___x_2022_);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v___x_2017_, v_cs_2020_, v___x_2024_, v___x_2025_, v_x_2019_);
return v___x_2026_;
}
}
else
{
lean_object* v_vs_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_vs_2027_ = lean_ctor_get(v_x_2018_, 0);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_array_get_size(v_vs_2027_);
v___x_2030_ = lean_nat_dec_lt(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_dec(v___x_2017_);
return v_x_2019_;
}
else
{
size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = ((size_t)0ULL);
v___x_2032_ = lean_usize_of_nat(v___x_2029_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2017_, v_vs_2027_, v___x_2031_, v___x_2032_, v_x_2019_);
return v___x_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2034_, lean_object* v_as_2035_, size_t v_i_2036_, size_t v_stop_2037_, lean_object* v_b_2038_){
_start:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_usize_dec_eq(v_i_2036_, v_stop_2037_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; 
v___x_2040_ = lean_array_uget_borrowed(v_as_2035_, v_i_2036_);
lean_inc(v___x_2034_);
v___x_2041_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v___x_2034_, v___x_2040_, v_b_2038_);
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_add(v_i_2036_, v___x_2042_);
v_i_2036_ = v___x_2043_;
v_b_2038_ = v___x_2041_;
goto _start;
}
else
{
lean_dec(v___x_2034_);
return v_b_2038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2045_, lean_object* v_as_2046_, lean_object* v_i_2047_, lean_object* v_stop_2048_, lean_object* v_b_2049_){
_start:
{
size_t v_i_boxed_2050_; size_t v_stop_boxed_2051_; lean_object* v_res_2052_; 
v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_stop_boxed_2051_ = lean_unbox_usize(v_stop_2048_);
lean_dec(v_stop_2048_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v___x_2045_, v_as_2046_, v_i_boxed_2050_, v_stop_boxed_2051_, v_b_2049_);
lean_dec_ref(v_as_2046_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object* v___x_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v___x_2053_, v_x_2054_, v_x_2055_);
lean_dec_ref(v_x_2054_);
return v_res_2056_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v___x_2058_, lean_object* v_x_2059_, size_t v_x_2060_, size_t v_x_2061_, lean_object* v_x_2062_){
_start:
{
if (lean_obj_tag(v_x_2059_) == 0)
{
lean_object* v_cs_2063_; lean_object* v___x_2064_; size_t v___x_2065_; lean_object* v_j_2066_; lean_object* v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_cs_2063_ = lean_ctor_get(v_x_2059_, 0);
v___x_2064_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___closed__0);
v___x_2065_ = lean_usize_shift_right(v_x_2060_, v_x_2061_);
v_j_2066_ = lean_usize_to_nat(v___x_2065_);
v___x_2067_ = lean_array_get_borrowed(v___x_2064_, v_cs_2063_, v_j_2066_);
v___x_2068_ = ((size_t)1ULL);
v___x_2069_ = lean_usize_shift_left(v___x_2068_, v_x_2061_);
v___x_2070_ = lean_usize_sub(v___x_2069_, v___x_2068_);
v___x_2071_ = lean_usize_land(v_x_2060_, v___x_2070_);
v___x_2072_ = ((size_t)5ULL);
v___x_2073_ = lean_usize_sub(v_x_2061_, v___x_2072_);
lean_inc(v___x_2058_);
v___x_2074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v___x_2058_, v___x_2067_, v___x_2071_, v___x_2073_, v_x_2062_);
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_nat_add(v_j_2066_, v___x_2075_);
lean_dec(v_j_2066_);
v___x_2077_ = lean_array_get_size(v_cs_2063_);
v___x_2078_ = lean_nat_dec_lt(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec(v___x_2076_);
lean_dec(v___x_2058_);
return v___x_2074_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_usize_of_nat(v___x_2076_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_usize_of_nat(v___x_2077_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v___x_2058_, v_cs_2063_, v___x_2079_, v___x_2080_, v___x_2074_);
return v___x_2081_;
}
}
else
{
lean_object* v_vs_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_vs_2082_ = lean_ctor_get(v_x_2059_, 0);
v___x_2083_ = lean_usize_to_nat(v_x_2060_);
v___x_2084_ = lean_array_get_size(v_vs_2082_);
v___x_2085_ = lean_nat_dec_lt(v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v___x_2083_);
lean_dec(v___x_2058_);
return v_x_2062_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_usize_of_nat(v___x_2083_);
lean_dec(v___x_2083_);
v___x_2087_ = lean_usize_of_nat(v___x_2084_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2058_, v_vs_2082_, v___x_2086_, v___x_2087_, v_x_2062_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v___x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
size_t v_x_1392__boxed_2094_; size_t v_x_1393__boxed_2095_; lean_object* v_res_2096_; 
v_x_1392__boxed_2094_ = lean_unbox_usize(v_x_2091_);
lean_dec(v_x_2091_);
v_x_1393__boxed_2095_ = lean_unbox_usize(v_x_2092_);
lean_dec(v_x_2092_);
v_res_2096_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v___x_2089_, v_x_2090_, v_x_1392__boxed_2094_, v_x_1393__boxed_2095_, v_x_2093_);
lean_dec_ref(v_x_2090_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v___x_2097_, lean_object* v_t_2098_, lean_object* v_init_2099_, lean_object* v_start_2100_){
_start:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_nat_dec_eq(v_start_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v_root_2103_; lean_object* v_tail_2104_; size_t v_shift_2105_; lean_object* v_tailOff_2106_; uint8_t v___x_2107_; 
v_root_2103_ = lean_ctor_get(v_t_2098_, 0);
v_tail_2104_ = lean_ctor_get(v_t_2098_, 1);
v_shift_2105_ = lean_ctor_get_usize(v_t_2098_, 4);
v_tailOff_2106_ = lean_ctor_get(v_t_2098_, 3);
v___x_2107_ = lean_nat_dec_le(v_tailOff_2106_, v_start_2100_);
if (v___x_2107_ == 0)
{
size_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2108_ = lean_usize_of_nat(v_start_2100_);
lean_inc(v___x_2097_);
v___x_2109_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v___x_2097_, v_root_2103_, v___x_2108_, v_shift_2105_, v_init_2099_);
v___x_2110_ = lean_array_get_size(v_tail_2104_);
v___x_2111_ = lean_nat_dec_lt(v___x_2101_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v___x_2097_);
return v___x_2109_;
}
else
{
size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = lean_usize_of_nat(v___x_2110_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2097_, v_tail_2104_, v___x_2112_, v___x_2113_, v___x_2109_);
return v___x_2114_;
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2115_ = lean_nat_sub(v_start_2100_, v_tailOff_2106_);
v___x_2116_ = lean_array_get_size(v_tail_2104_);
v___x_2117_ = lean_nat_dec_lt(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_dec(v___x_2115_);
lean_dec(v___x_2097_);
return v_init_2099_;
}
else
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_usize_of_nat(v___x_2115_);
lean_dec(v___x_2115_);
v___x_2119_ = lean_usize_of_nat(v___x_2116_);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2097_, v_tail_2104_, v___x_2118_, v___x_2119_, v_init_2099_);
return v___x_2120_;
}
}
}
else
{
lean_object* v_root_2121_; lean_object* v_tail_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_root_2121_ = lean_ctor_get(v_t_2098_, 0);
v_tail_2122_ = lean_ctor_get(v_t_2098_, 1);
lean_inc(v___x_2097_);
v___x_2123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v___x_2097_, v_root_2121_, v_init_2099_);
v___x_2124_ = lean_array_get_size(v_tail_2122_);
v___x_2125_ = lean_nat_dec_lt(v___x_2101_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec(v___x_2097_);
return v___x_2123_;
}
else
{
size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = lean_usize_of_nat(v___x_2124_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2097_, v_tail_2122_, v___x_2126_, v___x_2127_, v___x_2123_);
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v___x_2129_, lean_object* v_t_2130_, lean_object* v_init_2131_, lean_object* v_start_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v___x_2129_, v_t_2130_, v_init_2131_, v_start_2132_);
lean_dec(v_start_2132_);
lean_dec_ref(v_t_2130_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2134_, lean_object* v_env_2135_, lean_object* v_namespaceName_2136_){
_start:
{
lean_object* v_descr_2137_; lean_object* v_ext_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_s_2142_; lean_object* v_stateStack_2143_; 
v_descr_2137_ = lean_ctor_get(v_ext_2134_, 0);
lean_inc_ref(v_descr_2137_);
v_ext_2138_ = lean_ctor_get(v_ext_2134_, 1);
lean_inc_ref(v_ext_2138_);
lean_dec_ref(v_ext_2134_);
v___x_2139_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2140_ = lean_box(1);
v___x_2141_ = lean_box(0);
lean_inc_ref(v_env_2135_);
v_s_2142_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2139_, v_ext_2138_, v_env_2135_, v___x_2140_, v___x_2141_);
v_stateStack_2143_ = lean_ctor_get(v_s_2142_, 0);
lean_inc(v_stateStack_2143_);
if (lean_obj_tag(v_stateStack_2143_) == 1)
{
lean_object* v_head_2144_; lean_object* v_scopedEntries_2145_; lean_object* v_tail_2146_; lean_object* v_state_2147_; lean_object* v_activeScopes_2148_; uint8_t v_delimitsLocal_2149_; uint8_t v_scopeChanged_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2175_; 
v_head_2144_ = lean_ctor_get(v_stateStack_2143_, 0);
lean_inc(v_head_2144_);
v_scopedEntries_2145_ = lean_ctor_get(v_s_2142_, 1);
lean_inc_ref(v_scopedEntries_2145_);
lean_dec(v_s_2142_);
v_tail_2146_ = lean_ctor_get(v_stateStack_2143_, 1);
lean_inc(v_tail_2146_);
lean_dec_ref_known(v_stateStack_2143_, 2);
v_state_2147_ = lean_ctor_get(v_head_2144_, 0);
v_activeScopes_2148_ = lean_ctor_get(v_head_2144_, 1);
v_delimitsLocal_2149_ = lean_ctor_get_uint8(v_head_2144_, sizeof(void*)*2);
v_scopeChanged_2150_ = lean_ctor_get_uint8(v_head_2144_, sizeof(void*)*2 + 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_head_2144_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2152_ = v_head_2144_;
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_activeScopes_2148_);
lean_inc(v_state_2147_);
lean_dec(v_head_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
uint8_t v___x_2154_; 
v___x_2154_ = l_Lean_NameSet_contains(v_activeScopes_2148_, v_namespaceName_2136_);
if (v___x_2154_ == 0)
{
lean_object* v_activeScopes_2155_; lean_object* v_bs_x3f_2156_; lean_object* v___y_2158_; 
lean_inc(v_namespaceName_2136_);
v_activeScopes_2155_ = l_Lean_NameSet_insert(v_activeScopes_2148_, v_namespaceName_2136_);
v_bs_x3f_2156_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2145_, v_namespaceName_2136_);
lean_dec(v_namespaceName_2136_);
lean_dec_ref(v_scopedEntries_2145_);
if (lean_obj_tag(v_bs_x3f_2156_) == 1)
{
lean_object* v_val_2163_; lean_object* v_addEntry_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_val_2163_ = lean_ctor_get(v_bs_x3f_2156_, 0);
v_addEntry_2164_ = lean_ctor_get(v_descr_2137_, 4);
v___x_2165_ = 1;
v___x_2166_ = lean_unsigned_to_nat(0u);
lean_inc(v_addEntry_2164_);
v___x_2167_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_addEntry_2164_, v_val_2163_, v_state_2147_, v___x_2166_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_activeScopes_2155_);
lean_ctor_set(v___x_2152_, 0, v___x_2167_);
v___x_2169_ = v___x_2152_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_activeScopes_2155_);
v___x_2169_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; 
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*2, v___x_2165_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*2 + 1, v___x_2154_);
v___x_2170_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2137_, v___x_2169_);
lean_dec_ref(v_descr_2137_);
v___y_2158_ = v___x_2170_;
goto v___jp_2157_;
}
}
else
{
lean_object* v___x_2173_; 
lean_dec_ref(v_descr_2137_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_activeScopes_2155_);
v___x_2173_ = v___x_2152_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_state_2147_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_activeScopes_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*2, v_delimitsLocal_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*2 + 1, v_scopeChanged_2150_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
v___y_2158_ = v___x_2173_;
goto v___jp_2157_;
}
}
v___jp_2157_:
{
lean_object* v___f_2159_; 
v___f_2159_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2159_, 0, v___y_2158_);
lean_closure_set(v___f_2159_, 1, v_tail_2146_);
if (lean_obj_tag(v_bs_x3f_2156_) == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2138_, v_env_2135_, v___f_2159_, v___x_2140_, v___x_2141_, v___x_2154_);
return v___x_2160_;
}
else
{
uint8_t v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref_known(v_bs_x3f_2156_, 1);
v___x_2161_ = 1;
v___x_2162_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2138_, v_env_2135_, v___f_2159_, v___x_2140_, v___x_2141_, v___x_2161_);
return v___x_2162_;
}
}
}
else
{
lean_del_object(v___x_2152_);
lean_dec(v_activeScopes_2148_);
lean_dec(v_state_2147_);
lean_dec(v_tail_2146_);
lean_dec_ref(v_scopedEntries_2145_);
lean_dec_ref(v_ext_2138_);
lean_dec_ref(v_descr_2137_);
lean_dec(v_namespaceName_2136_);
return v_env_2135_;
}
}
}
else
{
lean_dec(v_stateStack_2143_);
lean_dec(v_s_2142_);
lean_dec_ref(v_ext_2138_);
lean_dec_ref(v_descr_2137_);
lean_dec(v_namespaceName_2136_);
return v_env_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2176_, lean_object* v_00_u03b2_2177_, lean_object* v_00_u03c3_2178_, lean_object* v_ext_2179_, lean_object* v_env_2180_, lean_object* v_namespaceName_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2179_, v_env_2180_, v_namespaceName_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2183_, lean_object* v_00_u03c3_2184_, lean_object* v___x_2185_, lean_object* v_t_2186_, lean_object* v_init_2187_, lean_object* v_start_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v___x_2185_, v_t_2186_, v_init_2187_, v_start_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_00_u03c3_2191_, lean_object* v___x_2192_, lean_object* v_t_2193_, lean_object* v_init_2194_, lean_object* v_start_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2190_, v_00_u03c3_2191_, v___x_2192_, v_t_2193_, v_init_2194_, v_start_2195_);
lean_dec(v_start_2195_);
lean_dec_ref(v_t_2193_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2197_, lean_object* v_00_u03c3_2198_, lean_object* v___x_2199_, lean_object* v_x_2200_, size_t v_x_2201_, size_t v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v___x_2199_, v_x_2200_, v_x_2201_, v_x_2202_, v_x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_00_u03c3_2206_, lean_object* v___x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
size_t v_x_1568__boxed_2212_; size_t v_x_1569__boxed_2213_; lean_object* v_res_2214_; 
v_x_1568__boxed_2212_ = lean_unbox_usize(v_x_2209_);
lean_dec(v_x_2209_);
v_x_1569__boxed_2213_ = lean_unbox_usize(v_x_2210_);
lean_dec(v_x_2210_);
v_res_2214_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2205_, v_00_u03c3_2206_, v___x_2207_, v_x_2208_, v_x_1568__boxed_2212_, v_x_1569__boxed_2213_, v_x_2211_);
lean_dec_ref(v_x_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2215_, lean_object* v_00_u03c3_2216_, lean_object* v___x_2217_, lean_object* v_as_2218_, size_t v_i_2219_, size_t v_stop_2220_, lean_object* v_b_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v___x_2217_, v_as_2218_, v_i_2219_, v_stop_2220_, v_b_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2223_, lean_object* v_00_u03c3_2224_, lean_object* v___x_2225_, lean_object* v_as_2226_, lean_object* v_i_2227_, lean_object* v_stop_2228_, lean_object* v_b_2229_){
_start:
{
size_t v_i_boxed_2230_; size_t v_stop_boxed_2231_; lean_object* v_res_2232_; 
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_stop_boxed_2231_ = lean_unbox_usize(v_stop_2228_);
lean_dec(v_stop_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2223_, v_00_u03c3_2224_, v___x_2225_, v_as_2226_, v_i_boxed_2230_, v_stop_boxed_2231_, v_b_2229_);
lean_dec_ref(v_as_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object* v_00_u03b2_2233_, lean_object* v_00_u03c3_2234_, lean_object* v___x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v___x_2235_, v_x_2236_, v_x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2239_, lean_object* v_00_u03c3_2240_, lean_object* v___x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(v_00_u03b2_2239_, v_00_u03c3_2240_, v___x_2241_, v_x_2242_, v_x_2243_);
lean_dec_ref(v_x_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2245_, lean_object* v_00_u03c3_2246_, lean_object* v___x_2247_, lean_object* v_as_2248_, size_t v_i_2249_, size_t v_stop_2250_, lean_object* v_b_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v___x_2247_, v_as_2248_, v_i_2249_, v_stop_2250_, v_b_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2253_, lean_object* v_00_u03c3_2254_, lean_object* v___x_2255_, lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_stop_2258_, lean_object* v_b_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2258_);
lean_dec(v_stop_2258_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2253_, v_00_u03c3_2254_, v___x_2255_, v_as_2256_, v_i_boxed_2260_, v_stop_boxed_2261_, v_b_2259_);
lean_dec_ref(v_as_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2263_, lean_object* v_descr_2264_, lean_object* v_s_2265_){
_start:
{
lean_object* v_stateStack_2266_; 
v_stateStack_2266_ = lean_ctor_get(v_s_2265_, 0);
lean_inc(v_stateStack_2266_);
if (lean_obj_tag(v_stateStack_2266_) == 1)
{
lean_object* v_head_2267_; lean_object* v_scopedEntries_2268_; lean_object* v_newEntries_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2298_; 
v_head_2267_ = lean_ctor_get(v_stateStack_2266_, 0);
lean_inc(v_head_2267_);
v_scopedEntries_2268_ = lean_ctor_get(v_s_2265_, 1);
v_newEntries_2269_ = lean_ctor_get(v_s_2265_, 2);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_s_2265_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v_s_2265_, 0);
lean_dec(v_unused_2299_);
v___x_2271_ = v_s_2265_;
v_isShared_2272_ = v_isSharedCheck_2298_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_newEntries_2269_);
lean_inc(v_scopedEntries_2268_);
lean_dec(v_s_2265_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2298_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_tail_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2296_; 
v_tail_2273_ = lean_ctor_get(v_stateStack_2266_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_stateStack_2266_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v_stateStack_2266_, 0);
lean_dec(v_unused_2297_);
v___x_2275_ = v_stateStack_2266_;
v_isShared_2276_ = v_isSharedCheck_2296_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_tail_2273_);
lean_dec(v_stateStack_2266_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2296_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v_state_2277_; lean_object* v_activeScopes_2278_; uint8_t v_delimitsLocal_2279_; uint8_t v_scopeChanged_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2295_; 
v_state_2277_ = lean_ctor_get(v_head_2267_, 0);
v_activeScopes_2278_ = lean_ctor_get(v_head_2267_, 1);
v_delimitsLocal_2279_ = lean_ctor_get_uint8(v_head_2267_, sizeof(void*)*2);
v_scopeChanged_2280_ = lean_ctor_get_uint8(v_head_2267_, sizeof(void*)*2 + 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_head_2267_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2282_ = v_head_2267_;
v_isShared_2283_ = v_isSharedCheck_2295_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_activeScopes_2278_);
lean_inc(v_state_2277_);
lean_dec(v_head_2267_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2295_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_apply_1(v_f_2263_, v_state_2277_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_activeScopes_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2294_, sizeof(void*)*2, v_delimitsLocal_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2294_, sizeof(void*)*2 + 1, v_scopeChanged_2280_);
v___x_2286_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2264_, v___x_2286_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2287_);
v___x_2289_ = v___x_2275_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_tail_2273_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2289_);
v___x_2291_ = v___x_2271_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_scopedEntries_2268_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_newEntries_2269_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2266_);
lean_dec(v_f_2263_);
return v_s_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object* v_f_2300_, lean_object* v_descr_2301_, lean_object* v_s_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(v_f_2300_, v_descr_2301_, v_s_2302_);
lean_dec_ref(v_descr_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2304_, lean_object* v_env_2305_, lean_object* v_f_2306_){
_start:
{
lean_object* v_ext_2307_; lean_object* v_toEnvExtension_2308_; lean_object* v_descr_2309_; lean_object* v_asyncMode_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; 
v_ext_2307_ = lean_ctor_get(v_ext_2304_, 1);
lean_inc_ref(v_ext_2307_);
v_toEnvExtension_2308_ = lean_ctor_get(v_ext_2307_, 0);
v_descr_2309_ = lean_ctor_get(v_ext_2304_, 0);
lean_inc_ref(v_descr_2309_);
lean_dec_ref(v_ext_2304_);
v_asyncMode_2310_ = lean_ctor_get(v_toEnvExtension_2308_, 2);
lean_inc(v_asyncMode_2310_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2311_, 0, v_f_2306_);
lean_closure_set(v___f_2311_, 1, v_descr_2309_);
v___x_2312_ = lean_box(0);
v___x_2313_ = 1;
v___x_2314_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2307_, v_env_2305_, v___f_2311_, v_asyncMode_2310_, v___x_2312_, v___x_2313_);
lean_dec(v_asyncMode_2310_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_00_u03c3_2317_, lean_object* v_ext_2318_, lean_object* v_env_2319_, lean_object* v_f_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2318_, v_env_2319_, v_f_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2322_, lean_object* v_____s_2323_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_apply_2(v_toPure_2322_, lean_box(0), v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2326_, lean_object* v_toPure_2327_, lean_object* v_r_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2326_);
v___x_2330_ = lean_apply_2(v_toPure_2327_, lean_box(0), v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2331_, lean_object* v_toBind_2332_, lean_object* v___f_2333_, lean_object* v_a_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_modifyEnv_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_modifyEnv_2337_ = lean_ctor_get(v_inst_2331_, 1);
lean_inc(v_modifyEnv_2337_);
lean_dec_ref(v_inst_2331_);
v___x_2338_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2338_, 0, lean_box(0));
lean_closure_set(v___x_2338_, 1, lean_box(0));
lean_closure_set(v___x_2338_, 2, lean_box(0));
lean_closure_set(v___x_2338_, 3, v_a_2334_);
v___x_2339_ = lean_apply_1(v_modifyEnv_2337_, v___x_2338_);
v___x_2340_ = lean_apply_4(v_toBind_2332_, lean_box(0), lean_box(0), v___x_2339_, v___f_2333_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2341_, lean_object* v_inst_2342_, lean_object* v_toBind_2343_, lean_object* v_inst_2344_, lean_object* v___f_2345_, lean_object* v_____do__lift_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; size_t v_sz_2350_; size_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2347_ = lean_box(0);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2348_, 0, v___x_2347_);
lean_closure_set(v___f_2348_, 1, v_toPure_2341_);
lean_inc(v_toBind_2343_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2349_, 0, v_inst_2342_);
lean_closure_set(v___f_2349_, 1, v_toBind_2343_);
lean_closure_set(v___f_2349_, 2, v___f_2348_);
v_sz_2350_ = lean_array_size(v_____do__lift_2346_);
v___x_2351_ = ((size_t)0ULL);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2344_, v_____do__lift_2346_, v___f_2349_, v_sz_2350_, v___x_2351_, v___x_2347_);
v___x_2353_ = lean_apply_4(v_toBind_2343_, lean_box(0), lean_box(0), v___x_2352_, v___f_2345_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = l_Lean_scopedEnvExtensionsRef;
v___x_2355_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2355_, 0, lean_box(0));
lean_closure_set(v___x_2355_, 1, lean_box(0));
lean_closure_set(v___x_2355_, 2, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_){
_start:
{
lean_object* v_toApplicative_2359_; lean_object* v_toBind_2360_; lean_object* v_toPure_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; 
v_toApplicative_2359_ = lean_ctor_get(v_inst_2356_, 0);
v_toBind_2360_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc_n(v_toBind_2360_, 2);
v_toPure_2361_ = lean_ctor_get(v_toApplicative_2359_, 1);
lean_inc_n(v_toPure_2361_, 2);
v___x_2362_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2363_ = lean_apply_2(v_inst_2358_, lean_box(0), v___x_2362_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2364_, 0, v_toPure_2361_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2365_, 0, v_toPure_2361_);
lean_closure_set(v___f_2365_, 1, v_inst_2357_);
lean_closure_set(v___f_2365_, 2, v_toBind_2360_);
lean_closure_set(v___f_2365_, 3, v_inst_2356_);
lean_closure_set(v___f_2365_, 4, v___f_2364_);
v___x_2366_ = lean_apply_4(v_toBind_2360_, lean_box(0), lean_box(0), v___x_2363_, v___f_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_pushScope___redArg(v_inst_2368_, v_inst_2369_, v_inst_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2372_, lean_object* v_toBind_2373_, lean_object* v___f_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_modifyEnv_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_modifyEnv_2378_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc(v_modifyEnv_2378_);
lean_dec_ref(v_inst_2372_);
v___x_2379_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2379_, 0, lean_box(0));
lean_closure_set(v___x_2379_, 1, lean_box(0));
lean_closure_set(v___x_2379_, 2, lean_box(0));
lean_closure_set(v___x_2379_, 3, v_a_2375_);
v___x_2380_ = lean_apply_1(v_modifyEnv_2378_, v___x_2379_);
v___x_2381_ = lean_apply_4(v_toBind_2373_, lean_box(0), lean_box(0), v___x_2380_, v___f_2374_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2382_, lean_object* v_inst_2383_, lean_object* v_toBind_2384_, lean_object* v_inst_2385_, lean_object* v___f_2386_, lean_object* v_____do__lift_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2388_ = lean_box(0);
v___f_2389_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2389_, 0, v___x_2388_);
lean_closure_set(v___f_2389_, 1, v_toPure_2382_);
lean_inc(v_toBind_2384_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
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
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_){
_start:
{
lean_object* v_toApplicative_2398_; lean_object* v_toBind_2399_; lean_object* v_toPure_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; 
v_toApplicative_2398_ = lean_ctor_get(v_inst_2395_, 0);
v_toBind_2399_ = lean_ctor_get(v_inst_2395_, 1);
lean_inc_n(v_toBind_2399_, 2);
v_toPure_2400_ = lean_ctor_get(v_toApplicative_2398_, 1);
lean_inc_n(v_toPure_2400_, 2);
v___x_2401_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2402_ = lean_apply_2(v_inst_2397_, lean_box(0), v___x_2401_);
v___f_2403_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2403_, 0, v_toPure_2400_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2404_, 0, v_toPure_2400_);
lean_closure_set(v___f_2404_, 1, v_inst_2396_);
lean_closure_set(v___f_2404_, 2, v_toBind_2399_);
lean_closure_set(v___f_2404_, 3, v_inst_2395_);
lean_closure_set(v___f_2404_, 4, v___f_2403_);
v___x_2405_ = lean_apply_4(v_toBind_2399_, lean_box(0), lean_box(0), v___x_2402_, v___f_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_popScope___redArg(v_inst_2407_, v_inst_2408_, v_inst_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2411_, lean_object* v_depth_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2411_, v_x_2413_, v_depth_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2415_, lean_object* v_depth_2416_, lean_object* v_toBind_2417_, lean_object* v___f_2418_, lean_object* v_a_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_modifyEnv_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_modifyEnv_2422_ = lean_ctor_get(v_inst_2415_, 1);
lean_inc(v_modifyEnv_2422_);
lean_dec_ref(v_inst_2415_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2423_, 0, v_a_2419_);
lean_closure_set(v___f_2423_, 1, v_depth_2416_);
v___x_2424_ = lean_apply_1(v_modifyEnv_2422_, v___f_2423_);
v___x_2425_ = lean_apply_4(v_toBind_2417_, lean_box(0), lean_box(0), v___x_2424_, v___f_2418_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2426_, lean_object* v_inst_2427_, lean_object* v_depth_2428_, lean_object* v_toBind_2429_, lean_object* v_inst_2430_, lean_object* v___f_2431_, lean_object* v_____do__lift_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___f_2435_; size_t v_sz_2436_; size_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2433_ = lean_box(0);
v___f_2434_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2434_, 0, v___x_2433_);
lean_closure_set(v___f_2434_, 1, v_toPure_2426_);
lean_inc(v_toBind_2429_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2435_, 0, v_inst_2427_);
lean_closure_set(v___f_2435_, 1, v_depth_2428_);
lean_closure_set(v___f_2435_, 2, v_toBind_2429_);
lean_closure_set(v___f_2435_, 3, v___f_2434_);
v_sz_2436_ = lean_array_size(v_____do__lift_2432_);
v___x_2437_ = ((size_t)0ULL);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2430_, v_____do__lift_2432_, v___f_2435_, v_sz_2436_, v___x_2437_, v___x_2433_);
v___x_2439_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2438_, v___f_2431_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_depth_2443_){
_start:
{
lean_object* v_toApplicative_2444_; lean_object* v_toBind_2445_; lean_object* v_toPure_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v_toApplicative_2444_ = lean_ctor_get(v_inst_2440_, 0);
v_toBind_2445_ = lean_ctor_get(v_inst_2440_, 1);
lean_inc_n(v_toBind_2445_, 2);
v_toPure_2446_ = lean_ctor_get(v_toApplicative_2444_, 1);
lean_inc_n(v_toPure_2446_, 2);
v___x_2447_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2448_ = lean_apply_2(v_inst_2442_, lean_box(0), v___x_2447_);
v___f_2449_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2449_, 0, v_toPure_2446_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2450_, 0, v_toPure_2446_);
lean_closure_set(v___f_2450_, 1, v_inst_2441_);
lean_closure_set(v___f_2450_, 2, v_depth_2443_);
lean_closure_set(v___f_2450_, 3, v_toBind_2445_);
lean_closure_set(v___f_2450_, 4, v_inst_2440_);
lean_closure_set(v___f_2450_, 5, v___f_2449_);
v___x_2451_ = lean_apply_4(v_toBind_2445_, lean_box(0), lean_box(0), v___x_2448_, v___f_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_depth_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_setDelimitsLocal___redArg(v_inst_2453_, v_inst_2454_, v_inst_2455_, v_depth_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2458_, lean_object* v_namespaceName_2459_, lean_object* v_x_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2458_, v_x_2460_, v_namespaceName_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2462_, lean_object* v_namespaceName_2463_, lean_object* v_toBind_2464_, lean_object* v___f_2465_, lean_object* v_a_2466_, lean_object* v_x_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_modifyEnv_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_modifyEnv_2469_ = lean_ctor_get(v_inst_2462_, 1);
lean_inc(v_modifyEnv_2469_);
lean_dec_ref(v_inst_2462_);
v___f_2470_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2470_, 0, v_a_2466_);
lean_closure_set(v___f_2470_, 1, v_namespaceName_2463_);
v___x_2471_ = lean_apply_1(v_modifyEnv_2469_, v___f_2470_);
v___x_2472_ = lean_apply_4(v_toBind_2464_, lean_box(0), lean_box(0), v___x_2471_, v___f_2465_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2473_, lean_object* v_inst_2474_, lean_object* v_namespaceName_2475_, lean_object* v_toBind_2476_, lean_object* v_inst_2477_, lean_object* v___f_2478_, lean_object* v_____do__lift_2479_){
_start:
{
lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___f_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2480_ = lean_box(0);
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2481_, 0, v___x_2480_);
lean_closure_set(v___f_2481_, 1, v_toPure_2473_);
lean_inc(v_toBind_2476_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2482_, 0, v_inst_2474_);
lean_closure_set(v___f_2482_, 1, v_namespaceName_2475_);
lean_closure_set(v___f_2482_, 2, v_toBind_2476_);
lean_closure_set(v___f_2482_, 3, v___f_2481_);
v_sz_2483_ = lean_array_size(v_____do__lift_2479_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2477_, v_____do__lift_2479_, v___f_2482_, v_sz_2483_, v___x_2484_, v___x_2480_);
v___x_2486_ = lean_apply_4(v_toBind_2476_, lean_box(0), lean_box(0), v___x_2485_, v___f_2478_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_namespaceName_2490_){
_start:
{
lean_object* v_toApplicative_2491_; lean_object* v_toBind_2492_; lean_object* v_toPure_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___f_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; 
v_toApplicative_2491_ = lean_ctor_get(v_inst_2487_, 0);
v_toBind_2492_ = lean_ctor_get(v_inst_2487_, 1);
lean_inc_n(v_toBind_2492_, 2);
v_toPure_2493_ = lean_ctor_get(v_toApplicative_2491_, 1);
lean_inc_n(v_toPure_2493_, 2);
v___x_2494_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2495_ = lean_apply_2(v_inst_2489_, lean_box(0), v___x_2494_);
v___f_2496_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2496_, 0, v_toPure_2493_);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2497_, 0, v_toPure_2493_);
lean_closure_set(v___f_2497_, 1, v_inst_2488_);
lean_closure_set(v___f_2497_, 2, v_namespaceName_2490_);
lean_closure_set(v___f_2497_, 3, v_toBind_2492_);
lean_closure_set(v___f_2497_, 4, v_inst_2487_);
lean_closure_set(v___f_2497_, 5, v___f_2496_);
v___x_2498_ = lean_apply_4(v_toBind_2492_, lean_box(0), lean_box(0), v___x_2495_, v___f_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_namespaceName_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_activateScoped___redArg(v_inst_2500_, v_inst_2501_, v_inst_2502_, v_namespaceName_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2506_){
_start:
{
lean_inc(v___y_2506_);
return v___y_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2507_);
lean_dec(v___y_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2509_, lean_object* v_a_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2510_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2514_, lean_object* v_a_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2514_, v_a_2515_, v___y_2516_);
lean_dec_ref(v___y_2516_);
lean_dec(v_x_2514_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_initial_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2527_){
_start:
{
lean_object* v_name_2529_; lean_object* v_addEntry_2530_; lean_object* v_initial_2531_; lean_object* v_finalizeImport_2532_; lean_object* v_exportEntry_x3f_2533_; uint8_t v_trackGen_2534_; lean_object* v___f_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_name_2529_ = lean_ctor_get(v_descr_2527_, 0);
lean_inc(v_name_2529_);
v_addEntry_2530_ = lean_ctor_get(v_descr_2527_, 1);
lean_inc(v_addEntry_2530_);
v_initial_2531_ = lean_ctor_get(v_descr_2527_, 2);
lean_inc(v_initial_2531_);
v_finalizeImport_2532_ = lean_ctor_get(v_descr_2527_, 3);
lean_inc(v_finalizeImport_2532_);
v_exportEntry_x3f_2533_ = lean_ctor_get(v_descr_2527_, 4);
lean_inc_ref(v_exportEntry_x3f_2533_);
v_trackGen_2534_ = lean_ctor_get_uint8(v_descr_2527_, sizeof(void*)*5);
lean_dec_ref(v_descr_2527_);
v___f_2535_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2536_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2537_, 0, v_initial_2531_);
v___x_2538_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2538_, 0, v_name_2529_);
lean_ctor_set(v___x_2538_, 1, v___f_2537_);
lean_ctor_set(v___x_2538_, 2, v___f_2536_);
lean_ctor_set(v___x_2538_, 3, v___f_2535_);
lean_ctor_set(v___x_2538_, 4, v_addEntry_2530_);
lean_ctor_set(v___x_2538_, 5, v_finalizeImport_2532_);
lean_ctor_set(v___x_2538_, 6, v_exportEntry_x3f_2533_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*7, v_trackGen_2534_);
v___x_2539_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2543_, lean_object* v_00_u03c3_2544_, lean_object* v_descr_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2548_, lean_object* v_00_u03c3_2549_, lean_object* v_descr_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2548_, v_00_u03c3_2549_, v_descr_2550_);
return v_res_2552_;
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
