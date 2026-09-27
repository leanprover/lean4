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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_183_, v___y_184_, v___y_185_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec(v_x_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_188_, lean_object* v_x_189_){
_start:
{
lean_inc(v_inst_188_);
return v_inst_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec(v_inst_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_193_, lean_object* v_x_194_){
_start:
{
lean_inc(v_s_193_);
return v_s_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_195_, v_x_196_);
lean_dec(v_x_196_);
lean_dec(v_s_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_a_199_);
lean_inc_ref_n(v___x_200_, 2);
v___x_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_202_, v_a_203_);
lean_dec_ref(v_x_202_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = l_instInhabitedError;
v___x_209_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, lean_box(0));
lean_closure_set(v___x_209_, 2, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_211_){
_start:
{
lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___f_212_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_213_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_213_, 0, v_inst_211_);
v___f_214_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_215_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_216_ = lean_box(0);
v___x_217_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_218_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_219_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_219_, 0, v___x_216_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___f_212_);
lean_ctor_set(v___x_219_, 3, v___f_213_);
lean_ctor_set(v___x_219_, 4, v___f_214_);
lean_ctor_set(v___x_219_, 5, v___x_218_);
lean_ctor_set(v___x_219_, 6, v___f_215_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_00_u03c3_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_225_){
_start:
{
lean_object* v_mkInitial_227_; lean_object* v___x_228_; 
v_mkInitial_227_ = lean_ctor_get(v_descr_225_, 1);
lean_inc_ref(v_mkInitial_227_);
lean_dec_ref(v_descr_225_);
v___x_228_ = lean_apply_1(v_mkInitial_227_, lean_box(0));
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_233_ = l_Lean_NameSet_empty;
v___x_234_ = 1;
v___x_235_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_235_, 0, v_a_229_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*2, v___x_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_239_);
v___x_241_ = v___x_231_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_228_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_228_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_255_, lean_object* v_00_u03b2_256_, lean_object* v_00_u03c3_257_, lean_object* v_descr_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_00_u03c3_263_, lean_object* v_descr_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_261_, v_00_u03b2_262_, v_00_u03c3_263_, v_descr_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
return v___x_269_;
}
else
{
lean_object* v_key_270_; lean_object* v_value_271_; lean_object* v_tail_272_; uint8_t v___x_273_; 
v_key_270_ = lean_ctor_get(v_x_268_, 0);
v_value_271_ = lean_ctor_get(v_x_268_, 1);
v_tail_272_ = lean_ctor_get(v_x_268_, 2);
v___x_273_ = lean_name_eq(v_key_270_, v_a_267_);
if (v___x_273_ == 0)
{
v_x_268_ = v_tail_272_;
goto _start;
}
else
{
lean_object* v___x_275_; 
lean_inc(v_value_271_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_value_271_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_276_, v_x_277_);
lean_dec(v_x_277_);
lean_dec(v_a_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_buckets_281_; lean_object* v___x_282_; uint64_t v___y_284_; 
v_buckets_281_ = lean_ctor_get(v_m_279_, 1);
v___x_282_ = lean_array_get_size(v_buckets_281_);
if (lean_obj_tag(v_a_280_) == 0)
{
uint64_t v___x_298_; 
v___x_298_ = 1723ULL;
v___y_284_ = v___x_298_;
goto v___jp_283_;
}
else
{
uint64_t v_hash_299_; 
v_hash_299_ = lean_ctor_get_uint64(v_a_280_, sizeof(void*)*2);
v___y_284_ = v_hash_299_;
goto v___jp_283_;
}
v___jp_283_:
{
uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v_fold_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_285_ = 32ULL;
v___x_286_ = lean_uint64_shift_right(v___y_284_, v___x_285_);
v_fold_287_ = lean_uint64_xor(v___y_284_, v___x_286_);
v___x_288_ = 16ULL;
v___x_289_ = lean_uint64_shift_right(v_fold_287_, v___x_288_);
v___x_290_ = lean_uint64_xor(v_fold_287_, v___x_289_);
v___x_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = lean_usize_of_nat(v___x_282_);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_sub(v___x_292_, v___x_293_);
v___x_295_ = lean_usize_land(v___x_291_, v___x_294_);
v___x_296_ = lean_array_uget_borrowed(v_buckets_281_, v___x_295_);
v___x_297_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_280_, v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_m_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_303_, lean_object* v_vals_304_, lean_object* v_i_305_, lean_object* v_k_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_keys_303_);
v___x_308_ = lean_nat_dec_lt(v_i_305_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v_i_305_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v_k_x27_310_; uint8_t v___x_311_; 
v_k_x27_310_ = lean_array_fget_borrowed(v_keys_303_, v_i_305_);
v___x_311_ = lean_name_eq(v_k_306_, v_k_x27_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_i_305_, v___x_312_);
lean_dec(v_i_305_);
v_i_305_ = v___x_313_;
goto _start;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_array_fget_borrowed(v_vals_304_, v_i_305_);
lean_dec(v_i_305_);
lean_inc(v___x_315_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_317_, lean_object* v_vals_318_, lean_object* v_i_319_, lean_object* v_k_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_317_, v_vals_318_, v_i_319_, v_k_320_);
lean_dec(v_k_320_);
lean_dec_ref(v_vals_318_);
lean_dec_ref(v_keys_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_322_, size_t v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_es_325_; lean_object* v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v_j_329_; lean_object* v___x_330_; 
v_es_325_ = lean_ctor_get(v_x_322_, 0);
v___x_326_ = lean_box(2);
v___x_327_ = ((size_t)31ULL);
v___x_328_ = lean_usize_land(v_x_323_, v___x_327_);
v_j_329_ = lean_usize_to_nat(v___x_328_);
v___x_330_ = lean_array_get_borrowed(v___x_326_, v_es_325_, v_j_329_);
lean_dec(v_j_329_);
switch(lean_obj_tag(v___x_330_))
{
case 0:
{
lean_object* v_key_331_; lean_object* v_val_332_; uint8_t v___x_333_; 
v_key_331_ = lean_ctor_get(v___x_330_, 0);
v_val_332_ = lean_ctor_get(v___x_330_, 1);
v___x_333_ = lean_name_eq(v_x_324_, v_key_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
lean_inc(v_val_332_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_val_332_);
return v___x_335_;
}
}
case 1:
{
lean_object* v_node_336_; size_t v___x_337_; size_t v___x_338_; 
v_node_336_ = lean_ctor_get(v___x_330_, 0);
v___x_337_ = ((size_t)5ULL);
v___x_338_ = lean_usize_shift_right(v_x_323_, v___x_337_);
v_x_322_ = v_node_336_;
v_x_323_ = v___x_338_;
goto _start;
}
default: 
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
}
}
else
{
lean_object* v_ks_341_; lean_object* v_vs_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_ks_341_ = lean_ctor_get(v_x_322_, 0);
v_vs_342_ = lean_ctor_get(v_x_322_, 1);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_341_, v_vs_342_, v___x_343_, v_x_324_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
size_t v_x_1059__boxed_348_; lean_object* v_res_349_; 
v_x_1059__boxed_348_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_res_349_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_345_, v_x_1059__boxed_348_, v_x_347_);
lean_dec(v_x_347_);
lean_dec_ref(v_x_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint64_t v___y_353_; 
if (lean_obj_tag(v_x_351_) == 0)
{
uint64_t v___x_356_; 
v___x_356_ = 1723ULL;
v___y_353_ = v___x_356_;
goto v___jp_352_;
}
else
{
uint64_t v_hash_357_; 
v_hash_357_ = lean_ctor_get_uint64(v_x_351_, sizeof(void*)*2);
v___y_353_ = v_hash_357_;
goto v___jp_352_;
}
v___jp_352_:
{
size_t v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_uint64_to_usize(v___y_353_);
v___x_355_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_350_, v___x_354_, v_x_351_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec_ref(v_x_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_stage_u2081_363_; 
v_stage_u2081_363_ = lean_ctor_get_uint8(v_x_361_, sizeof(void*)*2);
if (v_stage_u2081_363_ == 0)
{
lean_object* v_map_u2081_364_; lean_object* v_map_u2082_365_; lean_object* v___x_366_; 
v_map_u2081_364_ = lean_ctor_get(v_x_361_, 0);
v_map_u2082_365_ = lean_ctor_get(v_x_361_, 1);
v___x_366_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_365_, v_x_362_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_364_, v_x_362_);
return v___x_367_;
}
else
{
return v___x_366_;
}
}
else
{
lean_object* v_map_u2081_368_; lean_object* v___x_369_; 
v_map_u2081_368_ = lean_ctor_get(v_x_361_, 0);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_368_, v_x_362_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec_ref(v_x_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_373_, lean_object* v_b_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_dec(v_b_374_);
lean_dec(v_a_373_);
return v_x_375_;
}
else
{
lean_object* v_key_376_; lean_object* v_value_377_; lean_object* v_tail_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v_key_376_ = lean_ctor_get(v_x_375_, 0);
v_value_377_ = lean_ctor_get(v_x_375_, 1);
v_tail_378_ = lean_ctor_get(v_x_375_, 2);
v_isSharedCheck_390_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_390_ == 0)
{
v___x_380_ = v_x_375_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_tail_378_);
lean_inc(v_value_377_);
lean_inc(v_key_376_);
lean_dec(v_x_375_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_name_eq(v_key_376_, v_a_373_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_373_, v_b_374_, v_tail_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 2, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_key_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_value_377_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v___x_388_; 
lean_dec(v_value_377_);
lean_dec(v_key_376_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_b_374_);
lean_ctor_set(v___x_380_, 0, v_a_373_);
v___x_388_ = v___x_380_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_b_374_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_tail_378_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
return v_x_391_;
}
else
{
lean_object* v_key_393_; lean_object* v_value_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_421_; 
v_key_393_ = lean_ctor_get(v_x_392_, 0);
v_value_394_ = lean_ctor_get(v_x_392_, 1);
v_tail_395_ = lean_ctor_get(v_x_392_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_421_ == 0)
{
v___x_397_ = v_x_392_;
v_isShared_398_ = v_isSharedCheck_421_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_value_394_);
lean_inc(v_key_393_);
lean_dec(v_x_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_421_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint64_t v___y_401_; 
v___x_399_ = lean_array_get_size(v_x_391_);
if (lean_obj_tag(v_key_393_) == 0)
{
uint64_t v___x_419_; 
v___x_419_ = 1723ULL;
v___y_401_ = v___x_419_;
goto v___jp_400_;
}
else
{
uint64_t v_hash_420_; 
v_hash_420_ = lean_ctor_get_uint64(v_key_393_, sizeof(void*)*2);
v___y_401_ = v_hash_420_;
goto v___jp_400_;
}
v___jp_400_:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v_fold_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_402_ = 32ULL;
v___x_403_ = lean_uint64_shift_right(v___y_401_, v___x_402_);
v_fold_404_ = lean_uint64_xor(v___y_401_, v___x_403_);
v___x_405_ = 16ULL;
v___x_406_ = lean_uint64_shift_right(v_fold_404_, v___x_405_);
v___x_407_ = lean_uint64_xor(v_fold_404_, v___x_406_);
v___x_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = lean_usize_of_nat(v___x_399_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_sub(v___x_409_, v___x_410_);
v___x_412_ = lean_usize_land(v___x_408_, v___x_411_);
v___x_413_ = lean_array_uget_borrowed(v_x_391_, v___x_412_);
lean_inc(v___x_413_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_413_);
v___x_415_ = v___x_397_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_key_393_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_value_394_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v___x_413_);
v___x_415_ = v_reuseFailAlloc_418_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_array_uset(v_x_391_, v___x_412_, v___x_415_);
v_x_391_ = v___x_416_;
v_x_392_ = v_tail_395_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_422_, lean_object* v_source_423_, lean_object* v_target_424_){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_array_get_size(v_source_423_);
v___x_426_ = lean_nat_dec_lt(v_i_422_, v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v_source_423_);
lean_dec(v_i_422_);
return v_target_424_;
}
else
{
lean_object* v_es_427_; lean_object* v___x_428_; lean_object* v_source_429_; lean_object* v_target_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_es_427_ = lean_array_fget(v_source_423_, v_i_422_);
v___x_428_ = lean_box(0);
v_source_429_ = lean_array_fset(v_source_423_, v_i_422_, v___x_428_);
v_target_430_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_424_, v_es_427_);
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v_i_422_, v___x_431_);
lean_dec(v_i_422_);
v_i_422_ = v___x_432_;
v_source_423_ = v_source_429_;
v_target_424_ = v_target_430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_nbuckets_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_435_ = lean_array_get_size(v_data_434_);
v___x_436_ = lean_unsigned_to_nat(2u);
v_nbuckets_437_ = lean_nat_mul(v___x_435_, v___x_436_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_box(0);
v___x_440_ = lean_mk_array(v_nbuckets_437_, v___x_439_);
v___x_441_ = lean_array_propagate_mark(v_data_434_, v___x_440_);
v___x_442_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_438_, v_data_434_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
lean_object* v_key_446_; lean_object* v_tail_447_; uint8_t v___x_448_; 
v_key_446_ = lean_ctor_get(v_x_444_, 0);
v_tail_447_ = lean_ctor_get(v_x_444_, 2);
v___x_448_ = lean_name_eq(v_key_446_, v_a_443_);
if (v___x_448_ == 0)
{
v_x_444_ = v_tail_447_;
goto _start;
}
else
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_450_, v_x_451_);
lean_dec(v_x_451_);
lean_dec(v_a_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_454_, lean_object* v_a_455_, lean_object* v_b_456_){
_start:
{
lean_object* v_size_457_; lean_object* v_buckets_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_504_; 
v_size_457_ = lean_ctor_get(v_m_454_, 0);
v_buckets_458_ = lean_ctor_get(v_m_454_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_m_454_);
if (v_isSharedCheck_504_ == 0)
{
v___x_460_ = v_m_454_;
v_isShared_461_ = v_isSharedCheck_504_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_buckets_458_);
lean_inc(v_size_457_);
lean_dec(v_m_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_504_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; uint64_t v___y_464_; 
v___x_462_ = lean_array_get_size(v_buckets_458_);
if (lean_obj_tag(v_a_455_) == 0)
{
uint64_t v___x_502_; 
v___x_502_ = 1723ULL;
v___y_464_ = v___x_502_;
goto v___jp_463_;
}
else
{
uint64_t v_hash_503_; 
v_hash_503_ = lean_ctor_get_uint64(v_a_455_, sizeof(void*)*2);
v___y_464_ = v_hash_503_;
goto v___jp_463_;
}
v___jp_463_:
{
uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v_fold_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v_bkt_476_; uint8_t v___x_477_; 
v___x_465_ = 32ULL;
v___x_466_ = lean_uint64_shift_right(v___y_464_, v___x_465_);
v_fold_467_ = lean_uint64_xor(v___y_464_, v___x_466_);
v___x_468_ = 16ULL;
v___x_469_ = lean_uint64_shift_right(v_fold_467_, v___x_468_);
v___x_470_ = lean_uint64_xor(v_fold_467_, v___x_469_);
v___x_471_ = lean_uint64_to_usize(v___x_470_);
v___x_472_ = lean_usize_of_nat(v___x_462_);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_sub(v___x_472_, v___x_473_);
v___x_475_ = lean_usize_land(v___x_471_, v___x_474_);
v_bkt_476_ = lean_array_uget_borrowed(v_buckets_458_, v___x_475_);
v___x_477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_455_, v_bkt_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_size_x27_479_; lean_object* v___x_480_; lean_object* v_buckets_x27_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v_size_x27_479_ = lean_nat_add(v_size_457_, v___x_478_);
lean_dec(v_size_457_);
lean_inc(v_bkt_476_);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v_a_455_);
lean_ctor_set(v___x_480_, 1, v_b_456_);
lean_ctor_set(v___x_480_, 2, v_bkt_476_);
v_buckets_x27_481_ = lean_array_uset(v_buckets_458_, v___x_475_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(4u);
v___x_483_ = lean_nat_mul(v_size_x27_479_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_div(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_array_get_size(v_buckets_x27_481_);
v___x_487_ = lean_nat_dec_le(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v_val_488_; lean_object* v___x_490_; 
v_val_488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_481_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_val_488_);
lean_ctor_set(v___x_460_, 0, v_size_x27_479_);
v___x_490_ = v___x_460_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_val_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_buckets_x27_481_);
lean_ctor_set(v___x_460_, 0, v_size_x27_479_);
v___x_493_ = v___x_460_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_buckets_x27_481_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v___x_495_; lean_object* v_buckets_x27_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc(v_bkt_476_);
v___x_495_ = lean_box(0);
v_buckets_x27_496_ = lean_array_uset(v_buckets_458_, v___x_475_, v___x_495_);
v___x_497_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_455_, v_b_456_, v_bkt_476_);
v___x_498_ = lean_array_uset(v_buckets_x27_496_, v___x_475_, v___x_497_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_498_);
v___x_500_ = v___x_460_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_size_457_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v_ks_509_; lean_object* v_vs_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_534_; 
v_ks_509_ = lean_ctor_get(v_x_505_, 0);
v_vs_510_ = lean_ctor_get(v_x_505_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_534_ == 0)
{
v___x_512_ = v_x_505_;
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_vs_510_);
lean_inc(v_ks_509_);
lean_dec(v_x_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_array_get_size(v_ks_509_);
v___x_515_ = lean_nat_dec_lt(v_x_506_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec(v_x_506_);
v___x_516_ = lean_array_push(v_ks_509_, v_x_507_);
v___x_517_ = lean_array_push(v_vs_510_, v_x_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_517_);
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v_k_x27_521_; uint8_t v___x_522_; 
v_k_x27_521_ = lean_array_fget_borrowed(v_ks_509_, v_x_506_);
v___x_522_ = lean_name_eq(v_x_507_, v_k_x27_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_524_; 
if (v_isShared_513_ == 0)
{
v___x_524_ = v___x_512_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_ks_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_vs_510_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_x_506_, v___x_525_);
lean_dec(v_x_506_);
v_x_505_ = v___x_524_;
v_x_506_ = v___x_526_;
goto _start;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_array_fset(v_ks_509_, v_x_506_, v_x_507_);
v___x_530_ = lean_array_fset(v_vs_510_, v_x_506_, v_x_508_);
lean_dec(v_x_506_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_530_);
lean_ctor_set(v___x_512_, 0, v___x_529_);
v___x_532_ = v___x_512_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_535_, lean_object* v_k_536_, lean_object* v_v_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_535_, v___x_538_, v_k_536_, v_v_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_541_, size_t v_x_542_, size_t v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_es_546_; size_t v___x_547_; size_t v___x_548_; lean_object* v_j_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_es_546_ = lean_ctor_get(v_x_541_, 0);
v___x_547_ = ((size_t)31ULL);
v___x_548_ = lean_usize_land(v_x_542_, v___x_547_);
v_j_549_ = lean_usize_to_nat(v___x_548_);
v___x_550_ = lean_array_get_size(v_es_546_);
v___x_551_ = lean_nat_dec_lt(v_j_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_j_549_);
lean_dec(v_x_545_);
lean_dec(v_x_544_);
return v_x_541_;
}
else
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_590_; 
lean_inc_ref(v_es_546_);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_x_541_, 0);
lean_dec(v_unused_591_);
v___x_553_ = v_x_541_;
v_isShared_554_ = v_isSharedCheck_590_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_x_541_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_590_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_v_555_; lean_object* v___x_556_; lean_object* v_xs_x27_557_; lean_object* v___y_559_; 
v_v_555_ = lean_array_fget(v_es_546_, v_j_549_);
v___x_556_ = lean_box(0);
v_xs_x27_557_ = lean_array_fset(v_es_546_, v_j_549_, v___x_556_);
switch(lean_obj_tag(v_v_555_))
{
case 0:
{
lean_object* v_key_564_; lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
v_key_564_ = lean_ctor_get(v_v_555_, 0);
v_val_565_ = lean_ctor_get(v_v_555_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_575_ == 0)
{
v___x_567_ = v_v_555_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_inc(v_key_564_);
lean_dec(v_v_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint8_t v___x_569_; 
v___x_569_ = lean_name_eq(v_x_544_, v_key_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_del_object(v___x_567_);
v___x_570_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_564_, v_val_565_, v_x_544_, v_x_545_);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___y_559_ = v___x_571_;
goto v___jp_558_;
}
else
{
lean_object* v___x_573_; 
lean_dec(v_val_565_);
lean_dec(v_key_564_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_x_545_);
lean_ctor_set(v___x_567_, 0, v_x_544_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_x_544_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_x_545_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_559_ = v___x_573_;
goto v___jp_558_;
}
}
}
}
case 1:
{
lean_object* v_node_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_588_; 
v_node_576_ = lean_ctor_get(v_v_555_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_588_ == 0)
{
v___x_578_ = v_v_555_;
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_node_576_);
lean_dec(v_v_555_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_580_ = ((size_t)5ULL);
v___x_581_ = lean_usize_shift_right(v_x_542_, v___x_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_x_543_, v___x_582_);
v___x_584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_576_, v___x_581_, v___x_583_, v_x_544_, v_x_545_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_559_ = v___x_586_;
goto v___jp_558_;
}
}
}
default: 
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_x_544_);
lean_ctor_set(v___x_589_, 1, v_x_545_);
v___y_559_ = v___x_589_;
goto v___jp_558_;
}
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_array_fset(v_xs_x27_557_, v_j_549_, v___y_559_);
lean_dec(v_j_549_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_560_);
v___x_562_ = v___x_553_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
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
else
{
lean_object* v_ks_592_; lean_object* v_vs_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_611_; 
v_ks_592_ = lean_ctor_get(v_x_541_, 0);
v_vs_593_ = lean_ctor_get(v_x_541_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_611_ == 0)
{
v___x_595_ = v_x_541_;
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_vs_593_);
lean_inc(v_ks_592_);
lean_dec(v_x_541_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_ks_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_vs_593_);
v___x_598_ = v_reuseFailAlloc_610_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v_newNode_599_; size_t v___x_600_; uint8_t v___x_601_; 
v_newNode_599_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_598_, v_x_544_, v_x_545_);
v___x_600_ = ((size_t)7ULL);
v___x_601_ = lean_usize_dec_le(v___x_600_, v_x_543_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_599_);
v___x_603_ = lean_unsigned_to_nat(4u);
v___x_604_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
lean_dec(v___x_602_);
if (v___x_604_ == 0)
{
lean_object* v_ks_605_; lean_object* v_vs_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_ks_605_ = lean_ctor_get(v_newNode_599_, 0);
lean_inc_ref(v_ks_605_);
v_vs_606_ = lean_ctor_get(v_newNode_599_, 1);
lean_inc_ref(v_vs_606_);
lean_dec_ref(v_newNode_599_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_543_, v_ks_605_, v_vs_606_, v___x_607_, v___x_608_);
lean_dec_ref(v_vs_606_);
lean_dec_ref(v_ks_605_);
return v___x_609_;
}
else
{
return v_newNode_599_;
}
}
else
{
return v_newNode_599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_612_, lean_object* v_keys_613_, lean_object* v_vals_614_, lean_object* v_i_615_, lean_object* v_entries_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_array_get_size(v_keys_613_);
v___x_618_ = lean_nat_dec_lt(v_i_615_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_i_615_);
return v_entries_616_;
}
else
{
lean_object* v_k_619_; lean_object* v_v_620_; uint64_t v___y_622_; 
v_k_619_ = lean_array_fget_borrowed(v_keys_613_, v_i_615_);
v_v_620_ = lean_array_fget_borrowed(v_vals_614_, v_i_615_);
if (lean_obj_tag(v_k_619_) == 0)
{
uint64_t v___x_633_; 
v___x_633_ = 1723ULL;
v___y_622_ = v___x_633_;
goto v___jp_621_;
}
else
{
uint64_t v_hash_634_; 
v_hash_634_ = lean_ctor_get_uint64(v_k_619_, sizeof(void*)*2);
v___y_622_ = v_hash_634_;
goto v___jp_621_;
}
v___jp_621_:
{
size_t v_h_623_; size_t v___x_624_; lean_object* v___x_625_; size_t v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v_h_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_h_623_ = lean_uint64_to_usize(v___y_622_);
v___x_624_ = ((size_t)5ULL);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_sub(v_depth_612_, v___x_626_);
v___x_628_ = lean_usize_mul(v___x_624_, v___x_627_);
v_h_629_ = lean_usize_shift_right(v_h_623_, v___x_628_);
v___x_630_ = lean_nat_add(v_i_615_, v___x_625_);
lean_dec(v_i_615_);
lean_inc(v_v_620_);
lean_inc(v_k_619_);
v___x_631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_616_, v_h_629_, v_depth_612_, v_k_619_, v_v_620_);
v_i_615_ = v___x_630_;
v_entries_616_ = v___x_631_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_635_, lean_object* v_keys_636_, lean_object* v_vals_637_, lean_object* v_i_638_, lean_object* v_entries_639_){
_start:
{
size_t v_depth_boxed_640_; lean_object* v_res_641_; 
v_depth_boxed_640_ = lean_unbox_usize(v_depth_635_);
lean_dec(v_depth_635_);
v_res_641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_640_, v_keys_636_, v_vals_637_, v_i_638_, v_entries_639_);
lean_dec_ref(v_vals_637_);
lean_dec_ref(v_keys_636_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
size_t v_x_1435__boxed_647_; size_t v_x_1436__boxed_648_; lean_object* v_res_649_; 
v_x_1435__boxed_647_ = lean_unbox_usize(v_x_643_);
lean_dec(v_x_643_);
v_x_1436__boxed_648_ = lean_unbox_usize(v_x_644_);
lean_dec(v_x_644_);
v_res_649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_642_, v_x_1435__boxed_647_, v_x_1436__boxed_648_, v_x_645_, v_x_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
uint64_t v___y_654_; 
if (lean_obj_tag(v_x_651_) == 0)
{
uint64_t v___x_658_; 
v___x_658_ = 1723ULL;
v___y_654_ = v___x_658_;
goto v___jp_653_;
}
else
{
uint64_t v_hash_659_; 
v_hash_659_ = lean_ctor_get_uint64(v_x_651_, sizeof(void*)*2);
v___y_654_ = v_hash_659_;
goto v___jp_653_;
}
v___jp_653_:
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_uint64_to_usize(v___y_654_);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_650_, v___x_655_, v___x_656_, v_x_651_, v_x_652_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_stage_u2081_663_; 
v_stage_u2081_663_ = lean_ctor_get_uint8(v_x_660_, sizeof(void*)*2);
if (v_stage_u2081_663_ == 0)
{
lean_object* v_map_u2081_664_; lean_object* v_map_u2082_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_map_u2081_664_ = lean_ctor_get(v_x_660_, 0);
v_map_u2082_665_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_673_ == 0)
{
v___x_667_ = v_x_660_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_map_u2082_665_);
lean_inc(v_map_u2081_664_);
lean_dec(v_x_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_665_, v_x_661_, v_x_662_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_map_u2081_664_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*2, v_stage_u2081_663_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_map_u2081_674_; lean_object* v_map_u2082_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_map_u2081_674_ = lean_ctor_get(v_x_660_, 0);
v_map_u2082_675_ = lean_ctor_get(v_x_660_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_660_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v_x_660_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_map_u2082_675_);
lean_inc(v_map_u2081_674_);
lean_dec(v_x_660_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_674_, v_x_661_, v_x_662_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_map_u2082_675_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*2, v_stage_u2081_663_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_unsigned_to_nat(32u);
v___x_685_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = ((size_t)5ULL);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_unsigned_to_nat(32u);
v___x_690_ = lean_mk_empty_array_with_capacity(v___x_689_);
v___x_691_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_692_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_688_);
lean_ctor_set(v___x_692_, 3, v___x_688_);
lean_ctor_set_usize(v___x_692_, 4, v___x_687_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_693_, lean_object* v_ns_694_, lean_object* v_b_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_693_, v_ns_694_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_698_ = l_Lean_PersistentArray_push___redArg(v___x_697_, v_b_695_);
v___x_699_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_693_, v_ns_694_, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v_val_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_val_700_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_696_, 1);
v___x_701_ = l_Lean_PersistentArray_push___redArg(v_val_700_, v_b_695_);
v___x_702_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_693_, v_ns_694_, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_703_, lean_object* v_scopedEntries_704_, lean_object* v_ns_705_, lean_object* v_b_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_704_, v_ns_705_, v_b_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_712_, v_x_713_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_717_, v_x_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_725_, v_x_726_, v_x_727_);
lean_dec(v_x_727_);
lean_dec_ref(v_x_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_730_, v_a_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_733_, lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_733_, v_m_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_m_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_737_, lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_738_, v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_743_, v_a_744_, v_b_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, size_t v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_748_, v_x_749_, v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
size_t v_x_1736__boxed_756_; lean_object* v_res_757_; 
v_x_1736__boxed_756_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_res_757_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_752_, v_x_753_, v_x_1736__boxed_756_, v_x_755_);
lean_dec(v_x_755_);
lean_dec_ref(v_x_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_758_, lean_object* v_a_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_762_, lean_object* v_a_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_762_, v_a_763_, v_x_764_);
lean_dec(v_x_764_);
lean_dec(v_a_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, size_t v_x_768_, size_t v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_767_, v_x_768_, v_x_769_, v_x_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
size_t v_x_1752__boxed_779_; size_t v_x_1753__boxed_780_; lean_object* v_res_781_; 
v_x_1752__boxed_779_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_x_1753__boxed_780_ = lean_unbox_usize(v_x_776_);
lean_dec(v_x_776_);
v_res_781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_773_, v_x_774_, v_x_1752__boxed_779_, v_x_1753__boxed_780_, v_x_777_, v_x_778_);
return v_res_781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_782_, lean_object* v_a_783_, lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_786_, v_a_787_, v_x_788_);
lean_dec(v_x_788_);
lean_dec(v_a_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_791_, lean_object* v_data_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_794_, lean_object* v_a_795_, lean_object* v_b_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_795_, v_b_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_799_, lean_object* v_keys_800_, lean_object* v_vals_801_, lean_object* v_heq_802_, lean_object* v_i_803_, lean_object* v_k_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_800_, v_vals_801_, v_i_803_, v_k_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_806_, lean_object* v_keys_807_, lean_object* v_vals_808_, lean_object* v_heq_809_, lean_object* v_i_810_, lean_object* v_k_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_806_, v_keys_807_, v_vals_808_, v_heq_809_, v_i_810_, v_k_811_);
lean_dec(v_k_811_);
lean_dec_ref(v_vals_808_);
lean_dec_ref(v_keys_807_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_k_815_, lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_814_, v_k_815_, v_v_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_818_, size_t v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_819_, v_keys_820_, v_vals_821_, v_i_823_, v_entries_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_826_, lean_object* v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_827_);
lean_dec(v_depth_827_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_826_, v_depth_boxed_833_, v_keys_828_, v_vals_829_, v_heq_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_829_);
lean_dec_ref(v_keys_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_835_, lean_object* v_i_836_, lean_object* v_source_837_, lean_object* v_target_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_836_, v_source_837_, v_target_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_b_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_a_858_; uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_descr_850_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_b_854_);
return v___x_863_;
}
else
{
lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_904_; 
v_fst_864_ = lean_ctor_get(v_b_854_, 0);
v_snd_865_ = lean_ctor_get(v_b_854_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_904_ == 0)
{
v___x_867_ = v_b_854_;
v_isShared_868_ = v_isSharedCheck_904_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_b_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_904_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_a_869_; 
v_a_869_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
if (lean_obj_tag(v_a_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_ofOLeanEntry_871_; lean_object* v_addEntry_872_; lean_object* v___x_873_; 
v_a_870_ = lean_ctor_get(v_a_869_, 0);
v_ofOLeanEntry_871_ = lean_ctor_get(v_descr_850_, 2);
v_addEntry_872_ = lean_ctor_get(v_descr_850_, 4);
lean_inc_ref(v_ofOLeanEntry_871_);
lean_inc_ref(v___y_855_);
lean_inc(v_a_870_);
lean_inc(v_fst_864_);
v___x_873_ = lean_apply_4(v_ofOLeanEntry_871_, v_fst_864_, v_a_870_, v___y_855_, lean_box(0));
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
lean_inc(v_addEntry_872_);
v___x_875_ = lean_apply_2(v_addEntry_872_, v_fst_864_, v_a_874_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_875_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_snd_865_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_858_ = v___x_877_;
goto v___jp_857_;
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec_ref(v_descr_850_);
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
else
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v_ofOLeanEntry_889_; lean_object* v___x_890_; 
v_a_887_ = lean_ctor_get(v_a_869_, 0);
v_a_888_ = lean_ctor_get(v_a_869_, 1);
v_ofOLeanEntry_889_ = lean_ctor_get(v_descr_850_, 2);
lean_inc_ref(v_ofOLeanEntry_889_);
lean_inc_ref(v___y_855_);
lean_inc(v_a_888_);
lean_inc(v_fst_864_);
v___x_890_ = lean_apply_4(v_ofOLeanEntry_889_, v_fst_864_, v_a_888_, v___y_855_, lean_box(0));
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
lean_inc(v_a_887_);
v___x_892_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_865_, v_a_887_, v_a_891_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_892_);
v___x_894_ = v___x_867_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_fst_864_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
v_a_858_ = v___x_894_;
goto v___jp_857_;
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_del_object(v___x_867_);
lean_dec(v_snd_865_);
lean_dec(v_fst_864_);
lean_dec_ref(v_descr_850_);
v_a_896_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_890_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_890_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
v___jp_857_:
{
size_t v___x_859_; size_t v___x_860_; 
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_add(v_i_853_, v___x_859_);
v_i_853_ = v___x_860_;
v_b_854_ = v_a_858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_905_, lean_object* v_as_906_, lean_object* v_sz_907_, lean_object* v_i_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_907_);
lean_dec(v_sz_907_);
v_i_boxed_913_ = lean_unbox_usize(v_i_908_);
lean_dec(v_i_908_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_905_, v_as_906_, v_sz_boxed_912_, v_i_boxed_913_, v_b_909_, v___y_910_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v_as_906_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_915_, lean_object* v_as_916_, size_t v_sz_917_, size_t v_i_918_, lean_object* v_b_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_lt(v_i_918_, v_sz_917_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v_descr_915_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v_b_919_);
return v___x_923_;
}
else
{
lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_949_; 
v_fst_924_ = lean_ctor_get(v_b_919_, 0);
v_snd_925_ = lean_ctor_get(v_b_919_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_b_919_);
if (v_isSharedCheck_949_ == 0)
{
v___x_927_ = v_b_919_;
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v_b_919_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_a_929_; lean_object* v___x_931_; 
v_a_929_ = lean_array_uget_borrowed(v_as_916_, v_i_918_);
if (v_isShared_928_ == 0)
{
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_fst_924_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_snd_925_);
v___x_931_ = v_reuseFailAlloc_948_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; 
v_sz_932_ = lean_array_size(v_a_929_);
v___x_933_ = ((size_t)0ULL);
lean_inc_ref(v_descr_915_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_915_, v_a_929_, v_sz_932_, v___x_933_, v___x_931_, v___y_920_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v_fst_936_ = lean_ctor_get(v_a_935_, 0);
v_snd_937_ = lean_ctor_get(v_a_935_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v_a_935_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v_a_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_snd_937_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
size_t v___x_943_; size_t v___x_944_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_918_, v___x_943_);
v_i_918_ = v___x_944_;
v_b_919_ = v___x_942_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_915_);
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_958_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_950_, v_as_951_, v_sz_boxed_957_, v_i_boxed_958_, v_b_954_, v___y_955_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_960_, lean_object* v_as_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_mkInitial_964_; lean_object* v_finalizeImport_965_; lean_object* v___x_966_; 
v_mkInitial_964_ = lean_ctor_get(v_descr_960_, 1);
v_finalizeImport_965_ = lean_ctor_get(v_descr_960_, 5);
lean_inc(v_finalizeImport_965_);
lean_inc_ref(v_mkInitial_964_);
v___x_966_ = lean_apply_1(v_mkInitial_964_, lean_box(0));
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; size_t v_sz_971_; size_t v___x_972_; lean_object* v___x_973_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = 1;
v___x_969_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_a_967_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v_sz_971_ = lean_array_size(v_as_961_);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_960_, v_as_961_, v_sz_971_, v___x_972_, v___x_970_, v_a_962_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_995_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_995_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_994_; 
v_fst_978_ = lean_ctor_get(v_a_974_, 0);
v_snd_979_ = lean_ctor_get(v_a_974_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_981_ = v_a_974_;
v_isShared_982_ = v_isSharedCheck_994_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snd_979_);
lean_inc(v_fst_978_);
lean_dec(v_a_974_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_994_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_983_ = lean_apply_1(v_finalizeImport_965_, v_fst_978_);
v___x_984_ = l_Lean_NameSet_empty;
v___x_985_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*2, v___x_968_);
v___x_986_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 1);
lean_ctor_set(v___x_981_, 1, v___x_986_);
lean_ctor_set(v___x_981_, 0, v___x_985_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_986_);
v___x_988_ = v_reuseFailAlloc_993_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v_snd_979_);
lean_ctor_set(v___x_989_, 2, v___x_986_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_989_);
v___x_991_ = v___x_976_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_finalizeImport_965_);
v_a_996_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_973_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_973_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_finalizeImport_965_);
lean_dec_ref(v_descr_960_);
v_a_1004_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_966_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_966_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1012_, lean_object* v_as_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1012_, v_as_1013_, v_a_1014_);
lean_dec_ref(v_a_1014_);
lean_dec_ref(v_as_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_00_u03c3_1019_, lean_object* v_descr_1020_, lean_object* v_as_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1020_, v_as_1021_, v_a_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_00_u03c3_1027_, lean_object* v_descr_1028_, lean_object* v_as_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1025_, v_00_u03b2_1026_, v_00_u03c3_1027_, v_descr_1028_, v_as_1029_, v_a_1030_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v_as_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03c3_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_descr_1036_, lean_object* v_as_1037_, size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1036_, v_as_1037_, v_sz_1038_, v_i_1039_, v_b_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03c3_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_descr_1047_, lean_object* v_as_1048_, lean_object* v_sz_1049_, lean_object* v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_sz_boxed_1054_; size_t v_i_boxed_1055_; lean_object* v_res_1056_; 
v_sz_boxed_1054_ = lean_unbox_usize(v_sz_1049_);
lean_dec(v_sz_1049_);
v_i_boxed_1055_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1044_, v_00_u03c3_1045_, v_00_u03b2_1046_, v_descr_1047_, v_as_1048_, v_sz_boxed_1054_, v_i_boxed_1055_, v_b_1051_, v___y_1052_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v_as_1048_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03c3_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_descr_1060_, lean_object* v_as_1061_, size_t v_sz_1062_, size_t v_i_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1060_, v_as_1061_, v_sz_1062_, v_i_1063_, v_b_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03c3_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_descr_1071_, lean_object* v_as_1072_, lean_object* v_sz_1073_, lean_object* v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
size_t v_sz_boxed_1078_; size_t v_i_boxed_1079_; lean_object* v_res_1080_; 
v_sz_boxed_1078_ = lean_unbox_usize(v_sz_1073_);
lean_dec(v_sz_1073_);
v_i_boxed_1079_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1068_, v_00_u03c3_1069_, v_00_u03b2_1070_, v_descr_1071_, v_as_1072_, v_sz_boxed_1078_, v_i_boxed_1079_, v_b_1075_, v___y_1076_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_as_1072_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1081_, lean_object* v_descr_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
if (lean_obj_tag(v_a_1084_) == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_descr_1082_);
v___x_1086_ = l_List_reverse___redArg(v_a_1085_);
return v___x_1086_;
}
else
{
lean_object* v_head_1087_; lean_object* v_tail_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1113_; 
v_head_1087_ = lean_ctor_get(v_a_1084_, 0);
v_tail_1088_ = lean_ctor_get(v_a_1084_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_1084_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1090_ = v_a_1084_;
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_tail_1088_);
lean_inc(v_head_1087_);
lean_dec(v_a_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___y_1093_; lean_object* v_state_1098_; lean_object* v_activeScopes_1099_; uint8_t v_delimitsLocal_1100_; uint8_t v___x_1101_; 
v_state_1098_ = lean_ctor_get(v_head_1087_, 0);
v_activeScopes_1099_ = lean_ctor_get(v_head_1087_, 1);
v_delimitsLocal_1100_ = lean_ctor_get_uint8(v_head_1087_, sizeof(void*)*2);
v___x_1101_ = l_Lean_NameSet_contains(v_activeScopes_1099_, v_a_1081_);
if (v___x_1101_ == 0)
{
v___y_1093_ = v_head_1087_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
lean_inc(v_activeScopes_1099_);
lean_inc(v_state_1098_);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_head_1087_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; 
v_unused_1111_ = lean_ctor_get(v_head_1087_, 1);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_head_1087_, 0);
lean_dec(v_unused_1112_);
v___x_1103_ = v_head_1087_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_head_1087_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_addEntry_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_addEntry_1105_ = lean_ctor_get(v_descr_1082_, 4);
lean_inc(v_addEntry_1105_);
lean_inc(v_a_1083_);
v___x_1106_ = lean_apply_2(v_addEntry_1105_, v_state_1098_, v_a_1083_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_activeScopes_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*2, v_delimitsLocal_1100_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v___y_1093_ = v___x_1108_;
goto v___jp_1092_;
}
}
}
v___jp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_a_1085_);
lean_ctor_set(v___x_1090_, 0, v___y_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___y_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1085_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v_a_1084_ = v_tail_1088_;
v_a_1085_ = v___x_1095_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1114_, lean_object* v_descr_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1114_, v_descr_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_a_1121_);
lean_dec_ref(v_descr_1120_);
v___x_1124_ = l_List_reverse___redArg(v_a_1123_);
return v___x_1124_;
}
else
{
lean_object* v_head_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1146_; 
v_head_1125_ = lean_ctor_get(v_a_1122_, 0);
v_tail_1126_ = lean_ctor_get(v_a_1122_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1128_ = v_a_1122_;
v_isShared_1129_ = v_isSharedCheck_1146_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_head_1125_);
lean_dec(v_a_1122_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1146_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_addEntry_1130_; lean_object* v_state_1131_; lean_object* v_activeScopes_1132_; uint8_t v_delimitsLocal_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1145_; 
v_addEntry_1130_ = lean_ctor_get(v_descr_1120_, 4);
v_state_1131_ = lean_ctor_get(v_head_1125_, 0);
v_activeScopes_1132_ = lean_ctor_get(v_head_1125_, 1);
v_delimitsLocal_1133_ = lean_ctor_get_uint8(v_head_1125_, sizeof(void*)*2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_head_1125_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1135_ = v_head_1125_;
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_activeScopes_1132_);
lean_inc(v_state_1131_);
lean_dec(v_head_1125_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_inc(v_addEntry_1130_);
lean_inc(v_a_1121_);
v___x_1137_ = lean_apply_2(v_addEntry_1130_, v_state_1131_, v_a_1121_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_activeScopes_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1144_, sizeof(void*)*2, v_delimitsLocal_1133_);
v___x_1139_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v_a_1123_);
lean_ctor_set(v___x_1128_, 0, v___x_1139_);
v___x_1141_ = v___x_1128_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_a_1123_);
v___x_1141_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
v_a_1122_ = v_tail_1126_;
v_a_1123_ = v___x_1141_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1147_, lean_object* v_s_1148_, lean_object* v_e_1149_){
_start:
{
if (lean_obj_tag(v_e_1149_) == 0)
{
lean_object* v_stateStack_1150_; lean_object* v_scopedEntries_1151_; lean_object* v_newEntries_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1172_; 
v_stateStack_1150_ = lean_ctor_get(v_s_1148_, 0);
v_scopedEntries_1151_ = lean_ctor_get(v_s_1148_, 1);
v_newEntries_1152_ = lean_ctor_get(v_s_1148_, 2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_s_1148_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1154_ = v_s_1148_;
v_isShared_1155_ = v_isSharedCheck_1172_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_newEntries_1152_);
lean_inc(v_scopedEntries_1151_);
lean_inc(v_stateStack_1150_);
lean_dec(v_s_1148_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1172_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1171_; 
v_a_1156_ = lean_ctor_get(v_e_1149_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_e_1149_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1158_ = v_e_1149_;
v_isShared_1159_ = v_isSharedCheck_1171_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v_e_1149_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1171_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_toOLeanEntry_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v_toOLeanEntry_1160_ = lean_ctor_get(v_descr_1147_, 3);
lean_inc(v_toOLeanEntry_1160_);
v___x_1161_ = lean_box(0);
lean_inc(v_a_1156_);
v___x_1162_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1147_, v_a_1156_, v_stateStack_1150_, v___x_1161_);
v___x_1163_ = lean_apply_1(v_toOLeanEntry_1160_, v_a_1156_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1163_);
v___x_1165_ = v___x_1158_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_newEntries_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v___x_1166_);
lean_ctor_set(v___x_1154_, 0, v___x_1162_);
v___x_1168_ = v___x_1154_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_scopedEntries_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1173_; lean_object* v_scopedEntries_1174_; lean_object* v_newEntries_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1197_; 
v_stateStack_1173_ = lean_ctor_get(v_s_1148_, 0);
v_scopedEntries_1174_ = lean_ctor_get(v_s_1148_, 1);
v_newEntries_1175_ = lean_ctor_get(v_s_1148_, 2);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_s_1148_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1177_ = v_s_1148_;
v_isShared_1178_ = v_isSharedCheck_1197_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_newEntries_1175_);
lean_inc(v_scopedEntries_1174_);
lean_inc(v_stateStack_1173_);
lean_dec(v_s_1148_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1197_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_a_1179_; lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1196_; 
v_a_1179_ = lean_ctor_get(v_e_1149_, 0);
v_a_1180_ = lean_ctor_get(v_e_1149_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_e_1149_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1182_ = v_e_1149_;
v_isShared_1183_ = v_isSharedCheck_1196_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_inc(v_a_1179_);
lean_dec(v_e_1149_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1196_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_toOLeanEntry_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_toOLeanEntry_1184_ = lean_ctor_get(v_descr_1147_, 3);
lean_inc(v_toOLeanEntry_1184_);
v___x_1185_ = lean_box(0);
lean_inc_n(v_a_1180_, 2);
v___x_1186_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1179_, v_descr_1147_, v_a_1180_, v_stateStack_1173_, v___x_1185_);
lean_inc(v_a_1179_);
v___x_1187_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1174_, v_a_1179_, v_a_1180_);
v___x_1188_ = lean_apply_1(v_toOLeanEntry_1184_, v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1188_);
v___x_1190_ = v___x_1182_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1179_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v_newEntries_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 2, v___x_1191_);
lean_ctor_set(v___x_1177_, 1, v___x_1187_);
lean_ctor_set(v___x_1177_, 0, v___x_1186_);
v___x_1193_ = v___x_1177_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_00_u03c3_1200_, lean_object* v_descr_1201_, lean_object* v_s_1202_, lean_object* v_e_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1201_, v_s_1202_, v_e_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_00_u03b1_1207_, lean_object* v_descr_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1213_, lean_object* v_a_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_00_u03b1_1216_, lean_object* v_descr_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1214_, v_descr_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1222_, lean_object* v_a_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_00_u03b1_1225_, lean_object* v_descr_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1222_, v_a_1223_, v_00_u03b2_1224_, v_00_u03b1_1225_, v_descr_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1231_, lean_object* v_env_1232_, lean_object* v_as_1233_, size_t v_sz_1234_, size_t v_i_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v_a_1238_; uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_env_1232_);
lean_dec_ref(v_descr_1231_);
return v_b_1236_;
}
else
{
lean_object* v_snd_1243_; lean_object* v_fst_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1344_; 
v_snd_1243_ = lean_ctor_get(v_b_1236_, 1);
v_fst_1244_ = lean_ctor_get(v_b_1236_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_b_1236_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1246_ = v_b_1236_;
v_isShared_1247_ = v_isSharedCheck_1344_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1244_);
lean_dec(v_b_1236_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1344_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1343_; 
v_fst_1248_ = lean_ctor_get(v_snd_1243_, 0);
v_snd_1249_ = lean_ctor_get(v_snd_1243_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_snd_1243_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1251_ = v_snd_1243_;
v_isShared_1252_ = v_isSharedCheck_1343_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_snd_1243_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1343_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_a_1253_; 
v_a_1253_ = lean_array_uget(v_as_1233_, v_i_1235_);
if (lean_obj_tag(v_a_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1303_; 
v_a_1254_ = lean_ctor_get(v_a_1253_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1256_ = v_a_1253_;
v_isShared_1257_ = v_isSharedCheck_1303_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v_a_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1303_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_exportEntry_x3f_1258_; lean_object* v___x_1259_; lean_object* v_exported_1260_; lean_object* v_server_1261_; lean_object* v_private_1262_; lean_object* v___y_1264_; lean_object* v_server_1265_; lean_object* v_exported_1284_; 
v_exportEntry_x3f_1258_ = lean_ctor_get(v_descr_1231_, 6);
lean_inc_ref(v_exportEntry_x3f_1258_);
lean_inc_ref(v_env_1232_);
v___x_1259_ = lean_apply_2(v_exportEntry_x3f_1258_, v_env_1232_, v_a_1254_);
v_exported_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_exported_1260_);
v_server_1261_ = lean_ctor_get(v___x_1259_, 1);
lean_inc(v_server_1261_);
v_private_1262_ = lean_ctor_get(v___x_1259_, 2);
lean_inc(v_private_1262_);
lean_dec_ref(v___x_1259_);
if (lean_obj_tag(v_exported_1260_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_val_1294_ = lean_ctor_get(v_exported_1260_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_exported_1260_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v_exported_1260_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v_exported_1260_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 0);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1294_);
v___x_1299_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_array_push(v_fst_1244_, v___x_1299_);
v_exported_1284_ = v___x_1300_;
goto v___jp_1283_;
}
}
}
else
{
lean_dec(v_exported_1260_);
v_exported_1284_ = v_fst_1244_;
goto v___jp_1283_;
}
v___jp_1263_:
{
if (lean_obj_tag(v_private_1262_) == 1)
{
lean_object* v_val_1266_; lean_object* v___x_1268_; 
v_val_1266_ = lean_ctor_get(v_private_1262_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v_private_1262_, 1);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_val_1266_);
v___x_1268_ = v___x_1256_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_val_1266_);
v___x_1268_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_array_push(v_snd_1249_, v___x_1268_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1269_);
lean_ctor_set(v___x_1251_, 0, v_server_1265_);
v___x_1271_ = v___x_1251_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_server_1265_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1271_);
lean_ctor_set(v___x_1246_, 0, v___y_1264_);
v___x_1273_ = v___x_1246_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___y_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_a_1238_ = v___x_1273_;
goto v___jp_1237_;
}
}
}
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_private_1262_);
lean_del_object(v___x_1256_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_server_1265_);
v___x_1278_ = v___x_1251_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_server_1265_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_snd_1249_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1278_);
lean_ctor_set(v___x_1246_, 0, v___y_1264_);
v___x_1280_ = v___x_1246_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___y_1264_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v_a_1238_ = v___x_1280_;
goto v___jp_1237_;
}
}
}
}
v___jp_1283_:
{
if (lean_obj_tag(v_server_1261_) == 1)
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_val_1285_ = lean_ctor_get(v_server_1261_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_server_1261_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v_server_1261_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v_server_1261_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 0);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_val_1285_);
v___x_1290_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_array_push(v_fst_1248_, v___x_1290_);
v___y_1264_ = v_exported_1284_;
v_server_1265_ = v___x_1291_;
goto v___jp_1263_;
}
}
}
else
{
lean_dec(v_server_1261_);
v___y_1264_ = v_exported_1284_;
v_server_1265_ = v_fst_1248_;
goto v___jp_1263_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1342_; 
v_a_1304_ = lean_ctor_get(v_a_1253_, 0);
v_a_1305_ = lean_ctor_get(v_a_1253_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1307_ = v_a_1253_;
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_inc(v_a_1304_);
lean_dec(v_a_1253_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_exportEntry_x3f_1309_; lean_object* v___x_1310_; lean_object* v_exported_1311_; lean_object* v_server_1312_; lean_object* v_private_1313_; lean_object* v___y_1315_; lean_object* v_server_1316_; lean_object* v_exported_1335_; 
v_exportEntry_x3f_1309_ = lean_ctor_get(v_descr_1231_, 6);
lean_inc_ref(v_exportEntry_x3f_1309_);
lean_inc_ref(v_env_1232_);
v___x_1310_ = lean_apply_2(v_exportEntry_x3f_1309_, v_env_1232_, v_a_1305_);
v_exported_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_exported_1311_);
v_server_1312_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_server_1312_);
v_private_1313_ = lean_ctor_get(v___x_1310_, 2);
lean_inc(v_private_1313_);
lean_dec_ref(v___x_1310_);
if (lean_obj_tag(v_exported_1311_) == 1)
{
lean_object* v_val_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_val_1339_ = lean_ctor_get(v_exported_1311_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_exported_1311_, 1);
lean_inc(v_a_1304_);
v___x_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_a_1304_);
lean_ctor_set(v___x_1340_, 1, v_val_1339_);
v___x_1341_ = lean_array_push(v_fst_1244_, v___x_1340_);
v_exported_1335_ = v___x_1341_;
goto v___jp_1334_;
}
else
{
lean_dec(v_exported_1311_);
v_exported_1335_ = v_fst_1244_;
goto v___jp_1334_;
}
v___jp_1314_:
{
if (lean_obj_tag(v_private_1313_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1319_; 
v_val_1317_ = lean_ctor_get(v_private_1313_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v_private_1313_, 1);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_val_1317_);
v___x_1319_ = v___x_1307_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1304_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_val_1317_);
v___x_1319_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_array_push(v_snd_1249_, v___x_1319_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1320_);
lean_ctor_set(v___x_1251_, 0, v_server_1316_);
v___x_1322_ = v___x_1251_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_server_1316_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1322_);
lean_ctor_set(v___x_1246_, 0, v___y_1315_);
v___x_1324_ = v___x_1246_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___y_1315_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v_a_1238_ = v___x_1324_;
goto v___jp_1237_;
}
}
}
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_private_1313_);
lean_del_object(v___x_1307_);
lean_dec(v_a_1304_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_server_1316_);
v___x_1329_ = v___x_1251_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_server_1316_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_snd_1249_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1329_);
lean_ctor_set(v___x_1246_, 0, v___y_1315_);
v___x_1331_ = v___x_1246_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___y_1315_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
v_a_1238_ = v___x_1331_;
goto v___jp_1237_;
}
}
}
}
v___jp_1334_:
{
if (lean_obj_tag(v_server_1312_) == 1)
{
lean_object* v_val_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_val_1336_ = lean_ctor_get(v_server_1312_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_server_1312_, 1);
lean_inc(v_a_1304_);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1304_);
lean_ctor_set(v___x_1337_, 1, v_val_1336_);
v___x_1338_ = lean_array_push(v_fst_1248_, v___x_1337_);
v___y_1315_ = v_exported_1335_;
v_server_1316_ = v___x_1338_;
goto v___jp_1314_;
}
else
{
lean_dec(v_server_1312_);
v___y_1315_ = v_exported_1335_;
v_server_1316_ = v_fst_1248_;
goto v___jp_1314_;
}
}
}
}
}
}
}
v___jp_1237_:
{
size_t v___x_1239_; size_t v___x_1240_; 
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_add(v_i_1235_, v___x_1239_);
v_i_1235_ = v___x_1240_;
v_b_1236_ = v_a_1238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1345_, lean_object* v_env_1346_, lean_object* v_as_1347_, lean_object* v_sz_1348_, lean_object* v_i_1349_, lean_object* v_b_1350_){
_start:
{
size_t v_sz_boxed_1351_; size_t v_i_boxed_1352_; lean_object* v_res_1353_; 
v_sz_boxed_1351_ = lean_unbox_usize(v_sz_1348_);
lean_dec(v_sz_1348_);
v_i_boxed_1352_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1345_, v_env_1346_, v_as_1347_, v_sz_boxed_1351_, v_i_boxed_1352_, v_b_1350_);
lean_dec_ref(v_as_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1361_, lean_object* v_env_1362_, lean_object* v_s_1363_){
_start:
{
lean_object* v_newEntries_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1381_; 
v_newEntries_1364_ = lean_ctor_get(v_s_1363_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_s_1363_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1382_ = lean_ctor_get(v_s_1363_, 1);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_s_1363_, 0);
lean_dec(v_unused_1383_);
v___x_1366_ = v_s_1363_;
v_isShared_1367_ = v_isSharedCheck_1381_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_newEntries_1364_);
lean_dec(v_s_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1381_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; lean_object* v_snd_1374_; lean_object* v_fst_1375_; lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v___x_1379_; 
v___x_1368_ = lean_array_mk(v_newEntries_1364_);
v___x_1369_ = l_Array_reverse___redArg(v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1371_ = lean_array_size(v___x_1369_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1361_, v_env_1362_, v___x_1369_, v_sz_1371_, v___x_1372_, v___x_1370_);
lean_dec_ref(v___x_1369_);
v_snd_1374_ = lean_ctor_get(v___x_1373_, 1);
lean_inc(v_snd_1374_);
v_fst_1375_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_fst_1375_);
lean_dec_ref(v___x_1373_);
v_fst_1376_ = lean_ctor_get(v_snd_1374_, 0);
lean_inc(v_fst_1376_);
v_snd_1377_ = lean_ctor_get(v_snd_1374_, 1);
lean_inc(v_snd_1377_);
lean_dec(v_snd_1374_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 2, v_snd_1377_);
lean_ctor_set(v___x_1366_, 1, v_fst_1376_);
lean_ctor_set(v___x_1366_, 0, v_fst_1375_);
v___x_1379_ = v___x_1366_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_fst_1375_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_fst_1376_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_snd_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_00_u03c3_1386_, lean_object* v_descr_1387_, lean_object* v_env_1388_, lean_object* v_s_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1387_, v_env_1388_, v_s_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_00_u03c3_1393_, lean_object* v_descr_1394_, lean_object* v_env_1395_, lean_object* v_as_1396_, size_t v_sz_1397_, size_t v_i_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1394_, v_env_1395_, v_as_1396_, v_sz_1397_, v_i_1398_, v_b_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_00_u03c3_1403_, lean_object* v_descr_1404_, lean_object* v_env_1405_, lean_object* v_as_1406_, lean_object* v_sz_1407_, lean_object* v_i_1408_, lean_object* v_b_1409_){
_start:
{
size_t v_sz_boxed_1410_; size_t v_i_boxed_1411_; lean_object* v_res_1412_; 
v_sz_boxed_1410_ = lean_unbox_usize(v_sz_1407_);
lean_dec(v_sz_1407_);
v_i_boxed_1411_ = lean_unbox_usize(v_i_1408_);
lean_dec(v_i_1408_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1401_, v_00_u03b2_1402_, v_00_u03c3_1403_, v_descr_1404_, v_env_1405_, v_as_1406_, v_sz_boxed_1410_, v_i_boxed_1411_, v_b_1409_);
lean_dec_ref(v_as_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1418_, v___y_1419_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v_x_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1422_, lean_object* v_x_1423_){
_start:
{
lean_inc_ref(v_s_1422_);
return v_s_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1424_, v_x_1425_);
lean_dec_ref(v_x_1425_);
lean_dec_ref(v_s_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1432_, v_x_1433_);
lean_dec_ref(v_x_1433_);
lean_dec_ref(v_x_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1437_);
lean_dec_ref(v_x_1437_);
return v_res_1438_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___f_1444_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1445_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1446_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1447_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___f_1447_);
lean_ctor_set(v___x_1450_, 3, v___f_1446_);
lean_ctor_set(v___x_1450_, 4, v___f_1445_);
lean_ctor_set(v___x_1450_, 5, v___f_1444_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1451_){
_start:
{
lean_object* v___f_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___f_1452_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1453_, 0, v_inst_1451_);
v___f_1454_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1455_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1458_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1459_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1456_);
lean_ctor_set(v___x_1459_, 1, v___x_1457_);
lean_ctor_set(v___x_1459_, 2, v___f_1452_);
lean_ctor_set(v___x_1459_, 3, v___f_1453_);
lean_ctor_set(v___x_1459_, 4, v___f_1454_);
lean_ctor_set(v___x_1459_, 5, v___x_1458_);
lean_ctor_set(v___x_1459_, 6, v___f_1455_);
v___x_1460_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_00_u03c3_1464_, lean_object* v_inst_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1469_, lean_object* v_inst_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1478_ = lean_st_mk_ref(v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_s_1485_){
_start:
{
lean_object* v_newEntries_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_newEntries_1486_ = lean_ctor_get(v_s_1485_, 2);
v___x_1487_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1));
v___x_1488_ = l_List_lengthTR___redArg(v_newEntries_1486_);
v___x_1489_ = l_Nat_reprFast(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1487_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_s_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_1492_);
lean_dec_ref(v_s_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_x_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_x_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_1496_);
lean_dec_ref(v_x_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1500_){
_start:
{
lean_object* v_name_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_name_1502_ = lean_ctor_get(v_descr_1500_, 0);
v___f_1503_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1504_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
lean_inc_ref_n(v_descr_1500_, 4);
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1505_, 0, lean_box(0));
lean_closure_set(v___x_1505_, 1, lean_box(0));
lean_closure_set(v___x_1505_, 2, lean_box(0));
lean_closure_set(v___x_1505_, 3, v_descr_1500_);
v___x_1506_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1506_, 0, lean_box(0));
lean_closure_set(v___x_1506_, 1, lean_box(0));
lean_closure_set(v___x_1506_, 2, lean_box(0));
lean_closure_set(v___x_1506_, 3, v_descr_1500_);
v___x_1507_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1507_, 0, lean_box(0));
lean_closure_set(v___x_1507_, 1, lean_box(0));
lean_closure_set(v___x_1507_, 2, lean_box(0));
lean_closure_set(v___x_1507_, 3, v_descr_1500_);
v___x_1508_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1508_, 0, lean_box(0));
lean_closure_set(v___x_1508_, 1, lean_box(0));
lean_closure_set(v___x_1508_, 2, lean_box(0));
lean_closure_set(v___x_1508_, 3, v_descr_1500_);
v___x_1509_ = lean_box(2);
v___x_1510_ = lean_box(0);
v___x_1511_ = 0;
lean_inc(v_name_1502_);
v___x_1512_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1512_, 0, v_name_1502_);
lean_ctor_set(v___x_1512_, 1, v___x_1505_);
lean_ctor_set(v___x_1512_, 2, v___x_1506_);
lean_ctor_set(v___x_1512_, 3, v___x_1507_);
lean_ctor_set(v___x_1512_, 4, v___x_1508_);
lean_ctor_set(v___x_1512_, 5, v___f_1503_);
lean_ctor_set(v___x_1512_, 6, v___x_1509_);
lean_ctor_set(v___x_1512_, 7, v___x_1510_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*8, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v___f_1504_);
v___x_1514_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1513_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1527_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_descr_1500_);
lean_ctor_set(v___x_1519_, 1, v_a_1515_);
v___x_1520_ = l_Lean_scopedEnvExtensionsRef;
v___x_1521_ = lean_st_ref_take(v___x_1520_);
lean_inc_ref(v___x_1519_);
v___x_1522_ = lean_array_push(v___x_1521_, v___x_1519_);
v___x_1523_ = lean_st_ref_put(v___x_1520_, v___x_1522_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1519_);
v___x_1525_ = v___x_1517_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1519_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_descr_1500_);
v_a_1528_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1514_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1514_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_00_u03c3_1541_, lean_object* v_descr_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1545_, lean_object* v_00_u03b2_1546_, lean_object* v_00_u03c3_1547_, lean_object* v_descr_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1545_, v_00_u03b2_1546_, v_00_u03c3_1547_, v_descr_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(lean_object* v_s_1551_){
_start:
{
lean_object* v_stateStack_1552_; 
v_stateStack_1552_ = lean_ctor_get(v_s_1551_, 0);
if (lean_obj_tag(v_stateStack_1552_) == 0)
{
return v_s_1551_;
}
else
{
lean_object* v_head_1553_; lean_object* v_scopedEntries_1554_; lean_object* v_newEntries_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1573_; 
lean_inc_ref(v_stateStack_1552_);
v_head_1553_ = lean_ctor_get(v_stateStack_1552_, 0);
lean_inc(v_head_1553_);
v_scopedEntries_1554_ = lean_ctor_get(v_s_1551_, 1);
v_newEntries_1555_ = lean_ctor_get(v_s_1551_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_s_1551_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_s_1551_, 0);
lean_dec(v_unused_1574_);
v___x_1557_ = v_s_1551_;
v_isShared_1558_ = v_isSharedCheck_1573_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_newEntries_1555_);
lean_inc(v_scopedEntries_1554_);
lean_dec(v_s_1551_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1573_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_state_1559_; lean_object* v_activeScopes_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1572_; 
v_state_1559_ = lean_ctor_get(v_head_1553_, 0);
v_activeScopes_1560_ = lean_ctor_get(v_head_1553_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_head_1553_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1562_ = v_head_1553_;
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_activeScopes_1560_);
lean_inc(v_state_1559_);
lean_dec(v_head_1553_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
uint8_t v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = 1;
if (v_isShared_1563_ == 0)
{
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_state_1559_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_activeScopes_1560_);
v___x_1566_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*2, v___x_1564_);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_stateStack_1552_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1567_);
v___x_1569_ = v___x_1557_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_scopedEntries_1554_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_newEntries_1555_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1576_, lean_object* v_env_1577_){
_start:
{
lean_object* v_ext_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v_ext_1578_ = lean_ctor_get(v_ext_1576_, 1);
lean_inc_ref(v_ext_1578_);
lean_dec_ref(v_ext_1576_);
v___f_1579_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1580_ = lean_box(1);
v___x_1581_ = lean_box(0);
v___x_1582_ = 1;
v___x_1583_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1578_, v_env_1577_, v___f_1579_, v___x_1580_, v___x_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_00_u03c3_1586_, lean_object* v_ext_1587_, lean_object* v_env_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1587_, v_env_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_s_1590_){
_start:
{
lean_object* v_stateStack_1591_; 
v_stateStack_1591_ = lean_ctor_get(v_s_1590_, 0);
if (lean_obj_tag(v_stateStack_1591_) == 1)
{
lean_object* v_tail_1592_; 
v_tail_1592_ = lean_ctor_get(v_stateStack_1591_, 1);
if (lean_obj_tag(v_tail_1592_) == 1)
{
lean_object* v_scopedEntries_1593_; lean_object* v_newEntries_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_inc_ref(v_tail_1592_);
v_scopedEntries_1593_ = lean_ctor_get(v_s_1590_, 1);
v_newEntries_1594_ = lean_ctor_get(v_s_1590_, 2);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_s_1590_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v_s_1590_, 0);
lean_dec(v_unused_1602_);
v___x_1596_ = v_s_1590_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_newEntries_1594_);
lean_inc(v_scopedEntries_1593_);
lean_dec(v_s_1590_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_tail_1592_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_tail_1592_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_scopedEntries_1593_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_newEntries_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
else
{
return v_s_1590_;
}
}
else
{
return v_s_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1604_, lean_object* v_env_1605_){
_start:
{
lean_object* v_ext_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; 
v_ext_1606_ = lean_ctor_get(v_ext_1604_, 1);
lean_inc_ref(v_ext_1606_);
lean_dec_ref(v_ext_1604_);
v___f_1607_ = ((lean_object*)(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0));
v___x_1608_ = lean_box(1);
v___x_1609_ = lean_box(0);
v___x_1610_ = 1;
v___x_1611_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1606_, v_env_1605_, v___f_1607_, v___x_1608_, v___x_1609_, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_00_u03c3_1614_, lean_object* v_ext_1615_, lean_object* v_env_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1615_, v_env_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_zero_1620_; uint8_t v_isZero_1621_; 
v_zero_1620_ = lean_unsigned_to_nat(0u);
v_isZero_1621_ = lean_nat_dec_eq(v_a_1618_, v_zero_1620_);
if (v_isZero_1621_ == 1)
{
return v_a_1619_;
}
else
{
if (lean_obj_tag(v_a_1619_) == 0)
{
return v_a_1619_;
}
else
{
lean_object* v_head_1622_; lean_object* v_tail_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1642_; 
v_head_1622_ = lean_ctor_get(v_a_1619_, 0);
v_tail_1623_ = lean_ctor_get(v_a_1619_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1625_ = v_a_1619_;
v_isShared_1626_ = v_isSharedCheck_1642_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_tail_1623_);
lean_inc(v_head_1622_);
lean_dec(v_a_1619_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1642_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_state_1627_; lean_object* v_activeScopes_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1641_; 
v_state_1627_ = lean_ctor_get(v_head_1622_, 0);
v_activeScopes_1628_ = lean_ctor_get(v_head_1622_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_head_1622_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1630_ = v_head_1622_;
v_isShared_1631_ = v_isSharedCheck_1641_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_activeScopes_1628_);
lean_inc(v_state_1627_);
lean_dec(v_head_1622_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1641_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_one_1632_; lean_object* v_n_1633_; lean_object* v___x_1635_; 
v_one_1632_ = lean_unsigned_to_nat(1u);
v_n_1633_ = lean_nat_sub(v_a_1618_, v_one_1632_);
if (v_isShared_1631_ == 0)
{
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_state_1627_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_activeScopes_1628_);
v___x_1635_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*2, v_isZero_1621_);
v___x_1636_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1633_, v_tail_1623_);
lean_dec(v_n_1633_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1636_);
lean_ctor_set(v___x_1625_, 0, v___x_1635_);
v___x_1638_ = v___x_1625_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1643_, v_a_1644_);
lean_dec(v_a_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1647_, v_a_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1654_, lean_object* v_s_1655_){
_start:
{
lean_object* v_stateStack_1656_; lean_object* v_scopedEntries_1657_; lean_object* v_newEntries_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_stateStack_1656_ = lean_ctor_get(v_s_1655_, 0);
v_scopedEntries_1657_ = lean_ctor_get(v_s_1655_, 1);
v_newEntries_1658_ = lean_ctor_get(v_s_1655_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_s_1655_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v_s_1655_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_newEntries_1658_);
lean_inc(v_scopedEntries_1657_);
lean_inc(v_stateStack_1656_);
lean_dec(v_s_1655_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1654_, v_stateStack_1656_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_scopedEntries_1657_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_newEntries_1658_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1667_, lean_object* v_s_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1667_, v_s_1668_);
lean_dec(v_depth_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1670_, lean_object* v_env_1671_, lean_object* v_depth_1672_){
_start:
{
lean_object* v_ext_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; 
v_ext_1673_ = lean_ctor_get(v_ext_1670_, 1);
lean_inc_ref(v_ext_1673_);
lean_dec_ref(v_ext_1670_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1674_, 0, v_depth_1672_);
v___x_1675_ = lean_box(1);
v___x_1676_ = lean_box(0);
v___x_1677_ = 1;
v___x_1678_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1673_, v_env_1671_, v___f_1674_, v___x_1675_, v___x_1676_, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_00_u03c3_1681_, lean_object* v_ext_1682_, lean_object* v_env_1683_, lean_object* v_depth_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1682_, v_env_1683_, v_depth_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1686_, lean_object* v_env_1687_, lean_object* v_b_1688_){
_start:
{
lean_object* v_ext_1689_; lean_object* v_toEnvExtension_1690_; lean_object* v_asyncMode_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_ext_1689_ = lean_ctor_get(v_ext_1686_, 1);
lean_inc_ref(v_ext_1689_);
lean_dec_ref(v_ext_1686_);
v_toEnvExtension_1690_ = lean_ctor_get(v_ext_1689_, 0);
v_asyncMode_1691_ = lean_ctor_get(v_toEnvExtension_1690_, 2);
lean_inc(v_asyncMode_1691_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_b_1688_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1689_, v_env_1687_, v___x_1692_, v_asyncMode_1691_, v___x_1693_);
lean_dec(v_asyncMode_1691_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_00_u03c3_1697_, lean_object* v_ext_1698_, lean_object* v_env_1699_, lean_object* v_b_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1698_, v_env_1699_, v_b_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1702_, lean_object* v_env_1703_, lean_object* v_namespaceName_1704_, lean_object* v_b_1705_){
_start:
{
lean_object* v_ext_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1717_; 
v_ext_1706_ = lean_ctor_get(v_ext_1702_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_ext_1702_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v_ext_1702_, 0);
lean_dec(v_unused_1718_);
v___x_1708_ = v_ext_1702_;
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_ext_1706_);
lean_dec(v_ext_1702_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_toEnvExtension_1710_; lean_object* v_asyncMode_1711_; lean_object* v___x_1713_; 
v_toEnvExtension_1710_ = lean_ctor_get(v_ext_1706_, 0);
v_asyncMode_1711_ = lean_ctor_get(v_toEnvExtension_1710_, 2);
lean_inc(v_asyncMode_1711_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 1, v_b_1705_);
lean_ctor_set(v___x_1708_, 0, v_namespaceName_1704_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_namespaceName_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_b_1705_);
v___x_1713_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_1706_, v_env_1703_, v___x_1713_, v_asyncMode_1711_, v___x_1714_);
lean_dec(v_asyncMode_1711_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_00_u03c3_1721_, lean_object* v_ext_1722_, lean_object* v_env_1723_, lean_object* v_namespaceName_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1722_, v_env_1723_, v_namespaceName_1724_, v_b_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1727_, lean_object* v_states_1728_, lean_object* v_b_1729_){
_start:
{
if (lean_obj_tag(v_states_1728_) == 0)
{
lean_dec(v_b_1729_);
lean_dec_ref(v_ext_1727_);
return v_states_1728_;
}
else
{
lean_object* v_descr_1730_; lean_object* v_head_1731_; lean_object* v_tail_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1755_; 
v_descr_1730_ = lean_ctor_get(v_ext_1727_, 0);
v_head_1731_ = lean_ctor_get(v_states_1728_, 0);
v_tail_1732_ = lean_ctor_get(v_states_1728_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_states_1728_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1734_ = v_states_1728_;
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_tail_1732_);
lean_inc(v_head_1731_);
lean_dec(v_states_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_addEntry_1736_; lean_object* v_state_1737_; lean_object* v_activeScopes_1738_; uint8_t v_delimitsLocal_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1754_; 
v_addEntry_1736_ = lean_ctor_get(v_descr_1730_, 4);
v_state_1737_ = lean_ctor_get(v_head_1731_, 0);
v_activeScopes_1738_ = lean_ctor_get(v_head_1731_, 1);
v_delimitsLocal_1739_ = lean_ctor_get_uint8(v_head_1731_, sizeof(void*)*2);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_head_1731_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1741_ = v_head_1731_;
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_activeScopes_1738_);
lean_inc(v_state_1737_);
lean_dec(v_head_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_top_1745_; 
lean_inc(v_addEntry_1736_);
lean_inc(v_b_1729_);
v___x_1743_ = lean_apply_2(v_addEntry_1736_, v_state_1737_, v_b_1729_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v_top_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_activeScopes_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*2, v_delimitsLocal_1739_);
v_top_1745_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
if (v_delimitsLocal_1739_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = l_Lean_stateStackModify___redArg(v_ext_1727_, v_tail_1732_, v_b_1729_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1746_);
lean_ctor_set(v___x_1734_, 0, v_top_1745_);
v___x_1748_ = v___x_1734_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_top_1745_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
else
{
lean_object* v___x_1751_; 
lean_dec(v_b_1729_);
lean_dec_ref(v_ext_1727_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_top_1745_);
v___x_1751_ = v___x_1734_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_top_1745_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_tail_1732_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_00_u03c3_1758_, lean_object* v_ext_1759_, lean_object* v_states_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_stateStackModify___redArg(v_ext_1759_, v_states_1760_, v_b_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_1763_, lean_object* v_b_1764_, lean_object* v_s_1765_){
_start:
{
lean_object* v_stateStack_1766_; lean_object* v_scopedEntries_1767_; lean_object* v_newEntries_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1776_; 
v_stateStack_1766_ = lean_ctor_get(v_s_1765_, 0);
v_scopedEntries_1767_ = lean_ctor_get(v_s_1765_, 1);
v_newEntries_1768_ = lean_ctor_get(v_s_1765_, 2);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_s_1765_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1770_ = v_s_1765_;
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_newEntries_1768_);
lean_inc(v_scopedEntries_1767_);
lean_inc(v_stateStack_1766_);
lean_dec(v_s_1765_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_stateStackModify___redArg(v_ext_1763_, v_stateStack_1766_, v_b_1764_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_scopedEntries_1767_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_newEntries_1768_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_1777_, lean_object* v_env_1778_, lean_object* v_b_1779_){
_start:
{
lean_object* v_ext_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v_ext_1780_ = lean_ctor_get(v_ext_1777_, 1);
lean_inc_ref(v_ext_1780_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1781_, 0, v_ext_1777_);
lean_closure_set(v___f_1781_, 1, v_b_1779_);
v___x_1782_ = lean_box(1);
v___x_1783_ = lean_box(0);
v___x_1784_ = 1;
v___x_1785_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_1780_, v_env_1778_, v___f_1781_, v___x_1782_, v___x_1783_, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_00_u03c3_1788_, lean_object* v_ext_1789_, lean_object* v_env_1790_, lean_object* v_b_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1789_, v_env_1790_, v_b_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_1793_, lean_object* v_ext_1794_, lean_object* v_b_1795_, uint8_t v_kind_1796_, lean_object* v_namespaceName_1797_){
_start:
{
switch(v_kind_1796_)
{
case 0:
{
lean_object* v___x_1798_; 
lean_dec(v_namespaceName_1797_);
v___x_1798_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1794_, v_env_1793_, v_b_1795_);
return v___x_1798_;
}
case 1:
{
lean_object* v___x_1799_; 
lean_dec(v_namespaceName_1797_);
v___x_1799_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_1794_, v_env_1793_, v_b_1795_);
return v___x_1799_;
}
default: 
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1794_, v_env_1793_, v_namespaceName_1797_, v_b_1795_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_1801_, lean_object* v_ext_1802_, lean_object* v_b_1803_, lean_object* v_kind_1804_, lean_object* v_namespaceName_1805_){
_start:
{
uint8_t v_kind_boxed_1806_; lean_object* v_res_1807_; 
v_kind_boxed_1806_ = lean_unbox(v_kind_1804_);
v_res_1807_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1801_, v_ext_1802_, v_b_1803_, v_kind_boxed_1806_, v_namespaceName_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_1808_, lean_object* v_00_u03b2_1809_, lean_object* v_00_u03c3_1810_, lean_object* v_env_1811_, lean_object* v_ext_1812_, lean_object* v_b_1813_, uint8_t v_kind_1814_, lean_object* v_namespaceName_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1811_, v_ext_1812_, v_b_1813_, v_kind_1814_, v_namespaceName_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_00_u03b2_1818_, lean_object* v_00_u03c3_1819_, lean_object* v_env_1820_, lean_object* v_ext_1821_, lean_object* v_b_1822_, lean_object* v_kind_1823_, lean_object* v_namespaceName_1824_){
_start:
{
uint8_t v_kind_boxed_1825_; lean_object* v_res_1826_; 
v_kind_boxed_1825_ = lean_unbox(v_kind_1823_);
v_res_1826_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_1817_, v_00_u03b2_1818_, v_00_u03c3_1819_, v_env_1820_, v_ext_1821_, v_b_1822_, v_kind_boxed_1825_, v_namespaceName_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_1827_, lean_object* v_b_1828_, uint8_t v_kind_1829_, lean_object* v_ns_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_1831_, v_ext_1827_, v_b_1828_, v_kind_1829_, v_ns_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_1833_, lean_object* v_b_1834_, lean_object* v_kind_1835_, lean_object* v_ns_1836_, lean_object* v_x_1837_){
_start:
{
uint8_t v_kind_boxed_1838_; lean_object* v_res_1839_; 
v_kind_boxed_1838_ = lean_unbox(v_kind_1835_);
v_res_1839_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_1833_, v_b_1834_, v_kind_boxed_1838_, v_ns_1836_, v_x_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_1840_, lean_object* v_ext_1841_, lean_object* v_b_1842_, uint8_t v_kind_1843_, lean_object* v_ns_1844_){
_start:
{
lean_object* v_modifyEnv_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; 
v_modifyEnv_1845_ = lean_ctor_get(v_inst_1840_, 1);
lean_inc(v_modifyEnv_1845_);
lean_dec_ref(v_inst_1840_);
v___x_1846_ = lean_box(v_kind_1843_);
v___f_1847_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1847_, 0, v_ext_1841_);
lean_closure_set(v___f_1847_, 1, v_b_1842_);
lean_closure_set(v___f_1847_, 2, v___x_1846_);
lean_closure_set(v___f_1847_, 3, v_ns_1844_);
v___x_1848_ = lean_apply_1(v_modifyEnv_1845_, v___f_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_1849_, lean_object* v_ext_1850_, lean_object* v_b_1851_, lean_object* v_kind_1852_, lean_object* v_ns_1853_){
_start:
{
uint8_t v_kind_boxed_1854_; lean_object* v_res_1855_; 
v_kind_boxed_1854_ = lean_unbox(v_kind_1852_);
v_res_1855_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_1849_, v_ext_1850_, v_b_1851_, v_kind_boxed_1854_, v_ns_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_ext_1859_, lean_object* v_b_1860_, uint8_t v_kind_1861_){
_start:
{
lean_object* v_toBind_1862_; lean_object* v_getCurrNamespace_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___x_1866_; 
v_toBind_1862_ = lean_ctor_get(v_inst_1856_, 1);
lean_inc(v_toBind_1862_);
lean_dec_ref(v_inst_1856_);
v_getCurrNamespace_1863_ = lean_ctor_get(v_inst_1857_, 0);
lean_inc(v_getCurrNamespace_1863_);
lean_dec_ref(v_inst_1857_);
v___x_1864_ = lean_box(v_kind_1861_);
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1865_, 0, v_inst_1858_);
lean_closure_set(v___f_1865_, 1, v_ext_1859_);
lean_closure_set(v___f_1865_, 2, v_b_1860_);
lean_closure_set(v___f_1865_, 3, v___x_1864_);
v___x_1866_ = lean_apply_4(v_toBind_1862_, lean_box(0), lean_box(0), v_getCurrNamespace_1863_, v___f_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_ext_1870_, lean_object* v_b_1871_, lean_object* v_kind_1872_){
_start:
{
uint8_t v_kind_boxed_1873_; lean_object* v_res_1874_; 
v_kind_boxed_1873_ = lean_unbox(v_kind_1872_);
v_res_1874_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1867_, v_inst_1868_, v_inst_1869_, v_ext_1870_, v_b_1871_, v_kind_boxed_1873_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_1875_, lean_object* v_00_u03b1_1876_, lean_object* v_00_u03b2_1877_, lean_object* v_00_u03c3_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_ext_1882_, lean_object* v_b_1883_, uint8_t v_kind_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_1879_, v_inst_1880_, v_inst_1881_, v_ext_1882_, v_b_1883_, v_kind_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_1886_, lean_object* v_00_u03b1_1887_, lean_object* v_00_u03b2_1888_, lean_object* v_00_u03c3_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_ext_1893_, lean_object* v_b_1894_, lean_object* v_kind_1895_){
_start:
{
uint8_t v_kind_boxed_1896_; lean_object* v_res_1897_; 
v_kind_boxed_1896_ = lean_unbox(v_kind_1895_);
v_res_1897_ = l_Lean_ScopedEnvExtension_add(v_m_1886_, v_00_u03b1_1887_, v_00_u03b2_1888_, v_00_u03c3_1889_, v_inst_1890_, v_inst_1891_, v_inst_1892_, v_ext_1893_, v_b_1894_, v_kind_boxed_1896_);
return v_res_1897_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1901_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_1902_ = lean_unsigned_to_nat(16u);
v___x_1903_ = lean_unsigned_to_nat(209u);
v___x_1904_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_1905_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_1906_ = l_mkPanicMessageWithDecl(v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_, v___x_1901_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_1907_, lean_object* v_ext_1908_, lean_object* v_env_1909_, lean_object* v_asyncMode_1910_){
_start:
{
lean_object* v_ext_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_stateStack_1915_; 
v_ext_1911_ = lean_ctor_get(v_ext_1908_, 1);
v___x_1912_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1912_, v_ext_1911_, v_env_1909_, v_asyncMode_1910_, v___x_1913_);
v_stateStack_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_stateStack_1915_);
lean_dec(v___x_1914_);
if (lean_obj_tag(v_stateStack_1915_) == 1)
{
lean_object* v_head_1916_; lean_object* v_state_1917_; 
v_head_1916_ = lean_ctor_get(v_stateStack_1915_, 0);
lean_inc(v_head_1916_);
lean_dec_ref_known(v_stateStack_1915_, 2);
v_state_1917_ = lean_ctor_get(v_head_1916_, 0);
lean_inc(v_state_1917_);
lean_dec(v_head_1916_);
return v_state_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec(v_stateStack_1915_);
v___x_1918_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_1919_ = l_panic___redArg(v_inst_1907_, v___x_1918_);
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_1920_, lean_object* v_ext_1921_, lean_object* v_env_1922_, lean_object* v_asyncMode_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1920_, v_ext_1921_, v_env_1922_, v_asyncMode_1923_);
lean_dec(v_asyncMode_1923_);
lean_dec_ref(v_ext_1921_);
lean_dec(v_inst_1920_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_1925_, lean_object* v_00_u03b1_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_inst_1928_, lean_object* v_ext_1929_, lean_object* v_env_1930_, lean_object* v_asyncMode_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_1928_, v_ext_1929_, v_env_1930_, v_asyncMode_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_1933_, lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_inst_1936_, lean_object* v_ext_1937_, lean_object* v_env_1938_, lean_object* v_asyncMode_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_1933_, v_00_u03b1_1934_, v_00_u03b2_1935_, v_inst_1936_, v_ext_1937_, v_env_1938_, v_asyncMode_1939_);
lean_dec(v_asyncMode_1939_);
lean_dec_ref(v_ext_1937_);
lean_dec(v_inst_1936_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ext_1941_, lean_object* v_as_1942_, size_t v_sz_1943_, size_t v_i_1944_, lean_object* v_b_1945_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_usize_dec_lt(v_i_1944_, v_sz_1943_);
if (v___x_1946_ == 0)
{
lean_dec_ref(v_ext_1941_);
return v_b_1945_;
}
else
{
lean_object* v_descr_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1962_; 
v_descr_1947_ = lean_ctor_get(v_ext_1941_, 0);
v_snd_1948_ = lean_ctor_get(v_b_1945_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_b_1945_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_b_1945_, 0);
lean_dec(v_unused_1963_);
v___x_1950_ = v_b_1945_;
v_isShared_1951_ = v_isSharedCheck_1962_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_dec(v_b_1945_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1962_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_addEntry_1952_; lean_object* v___x_1953_; lean_object* v_a_1954_; lean_object* v_state_1955_; lean_object* v___x_1957_; 
v_addEntry_1952_ = lean_ctor_get(v_descr_1947_, 4);
v___x_1953_ = lean_box(0);
v_a_1954_ = lean_array_uget_borrowed(v_as_1942_, v_i_1944_);
lean_inc(v_addEntry_1952_);
lean_inc(v_a_1954_);
v_state_1955_ = lean_apply_2(v_addEntry_1952_, v_snd_1948_, v_a_1954_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_state_1955_);
lean_ctor_set(v___x_1950_, 0, v___x_1953_);
v___x_1957_ = v___x_1950_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_state_1955_);
v___x_1957_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
size_t v___x_1958_; size_t v___x_1959_; 
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1944_, v___x_1958_);
v_i_1944_ = v___x_1959_;
v_b_1945_ = v___x_1957_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ext_1964_, lean_object* v_as_1965_, lean_object* v_sz_1966_, lean_object* v_i_1967_, lean_object* v_b_1968_){
_start:
{
size_t v_sz_boxed_1969_; size_t v_i_boxed_1970_; lean_object* v_res_1971_; 
v_sz_boxed_1969_ = lean_unbox_usize(v_sz_1966_);
lean_dec(v_sz_1966_);
v_i_boxed_1970_ = lean_unbox_usize(v_i_1967_);
lean_dec(v_i_1967_);
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1964_, v_as_1965_, v_sz_boxed_1969_, v_i_boxed_1970_, v_b_1968_);
lean_dec_ref(v_as_1965_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(lean_object* v_ext_1972_, lean_object* v_as_1973_, size_t v_sz_1974_, size_t v_i_1975_, lean_object* v_b_1976_){
_start:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_usize_dec_lt(v_i_1975_, v_sz_1974_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v_ext_1972_);
return v_b_1976_;
}
else
{
lean_object* v_descr_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1993_; 
v_descr_1978_ = lean_ctor_get(v_ext_1972_, 0);
v_snd_1979_ = lean_ctor_get(v_b_1976_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_b_1976_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v_b_1976_, 0);
lean_dec(v_unused_1994_);
v___x_1981_ = v_b_1976_;
v_isShared_1982_ = v_isSharedCheck_1993_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_dec(v_b_1976_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1993_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v_addEntry_1983_; lean_object* v___x_1984_; lean_object* v_a_1985_; lean_object* v_state_1986_; lean_object* v___x_1988_; 
v_addEntry_1983_ = lean_ctor_get(v_descr_1978_, 4);
v___x_1984_ = lean_box(0);
v_a_1985_ = lean_array_uget_borrowed(v_as_1973_, v_i_1975_);
lean_inc(v_addEntry_1983_);
lean_inc(v_a_1985_);
v_state_1986_ = lean_apply_2(v_addEntry_1983_, v_snd_1979_, v_a_1985_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v_state_1986_);
lean_ctor_set(v___x_1981_, 0, v___x_1984_);
v___x_1988_ = v___x_1981_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_state_1986_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1975_, v___x_1989_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_1972_, v_as_1973_, v_sz_1974_, v___x_1990_, v___x_1988_);
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ext_1995_, lean_object* v_as_1996_, lean_object* v_sz_1997_, lean_object* v_i_1998_, lean_object* v_b_1999_){
_start:
{
size_t v_sz_boxed_2000_; size_t v_i_boxed_2001_; lean_object* v_res_2002_; 
v_sz_boxed_2000_ = lean_unbox_usize(v_sz_1997_);
lean_dec(v_sz_1997_);
v_i_boxed_2001_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_1995_, v_as_1996_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1999_);
lean_dec_ref(v_as_1996_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_init_2003_, lean_object* v_ext_2004_, lean_object* v_n_2005_, lean_object* v_b_2006_){
_start:
{
if (lean_obj_tag(v_n_2005_) == 0)
{
lean_object* v_cs_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; size_t v_sz_2010_; size_t v___x_2011_; lean_object* v___x_2012_; lean_object* v_fst_2013_; 
v_cs_2007_ = lean_ctor_get(v_n_2005_, 0);
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v_b_2006_);
v_sz_2010_ = lean_array_size(v_cs_2007_);
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2003_, v_ext_2004_, v_cs_2007_, v_sz_2010_, v___x_2011_, v___x_2009_);
v_fst_2013_ = lean_ctor_get(v___x_2012_, 0);
if (lean_obj_tag(v_fst_2013_) == 0)
{
lean_object* v_snd_2014_; lean_object* v___x_2015_; 
v_snd_2014_ = lean_ctor_get(v___x_2012_, 1);
lean_inc(v_snd_2014_);
lean_dec_ref(v___x_2012_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_snd_2014_);
return v___x_2015_;
}
else
{
lean_object* v_val_2016_; 
lean_inc_ref(v_fst_2013_);
lean_dec_ref(v___x_2012_);
v_val_2016_ = lean_ctor_get(v_fst_2013_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v_fst_2013_, 1);
return v_val_2016_;
}
}
else
{
lean_object* v_vs_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; size_t v_sz_2020_; size_t v___x_2021_; lean_object* v___x_2022_; lean_object* v_fst_2023_; 
v_vs_2017_ = lean_ctor_get(v_n_2005_, 0);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v_b_2006_);
v_sz_2020_ = lean_array_size(v_vs_2017_);
v___x_2021_ = ((size_t)0ULL);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2004_, v_vs_2017_, v_sz_2020_, v___x_2021_, v___x_2019_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
if (lean_obj_tag(v_fst_2023_) == 0)
{
lean_object* v_snd_2024_; lean_object* v___x_2025_; 
v_snd_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2022_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_snd_2024_);
return v___x_2025_;
}
else
{
lean_object* v_val_2026_; 
lean_inc_ref(v_fst_2023_);
lean_dec_ref(v___x_2022_);
v_val_2026_ = lean_ctor_get(v_fst_2023_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v_fst_2023_, 1);
return v_val_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_init_2027_, lean_object* v_ext_2028_, lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_ext_2028_);
return v_b_2032_;
}
else
{
lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2052_; 
v_snd_2034_ = lean_ctor_get(v_b_2032_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_b_2032_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_b_2032_, 0);
lean_dec(v_unused_2053_);
v___x_2036_ = v_b_2032_;
v_isShared_2037_ = v_isSharedCheck_2052_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_dec(v_b_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2052_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_a_2038_; lean_object* v___x_2039_; 
v_a_2038_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
lean_inc(v_snd_2034_);
lean_inc_ref(v_ext_2028_);
v___x_2039_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2027_, v_ext_2028_, v_a_2038_, v_snd_2034_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec_ref(v_ext_2028_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2040_);
v___x_2042_ = v___x_2036_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_snd_2034_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_snd_2034_);
v_a_2044_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2045_ = lean_box(0);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v_a_2044_);
lean_ctor_set(v___x_2036_, 0, v___x_2045_);
v___x_2047_ = v___x_2036_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_a_2044_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; 
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2031_, v___x_2048_);
v_i_2031_ = v___x_2049_;
v_b_2032_ = v___x_2047_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_init_2054_, lean_object* v_ext_2055_, lean_object* v_as_2056_, lean_object* v_sz_2057_, lean_object* v_i_2058_, lean_object* v_b_2059_){
_start:
{
size_t v_sz_boxed_2060_; size_t v_i_boxed_2061_; lean_object* v_res_2062_; 
v_sz_boxed_2060_ = lean_unbox_usize(v_sz_2057_);
lean_dec(v_sz_2057_);
v_i_boxed_2061_ = lean_unbox_usize(v_i_2058_);
lean_dec(v_i_2058_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2054_, v_ext_2055_, v_as_2056_, v_sz_boxed_2060_, v_i_boxed_2061_, v_b_2059_);
lean_dec_ref(v_as_2056_);
lean_dec(v_init_2054_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_init_2063_, lean_object* v_ext_2064_, lean_object* v_n_2065_, lean_object* v_b_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2063_, v_ext_2064_, v_n_2065_, v_b_2066_);
lean_dec_ref(v_n_2065_);
lean_dec(v_init_2063_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(lean_object* v_ext_2068_, lean_object* v_as_2069_, size_t v_sz_2070_, size_t v_i_2071_, lean_object* v_b_2072_){
_start:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_lt(v_i_2071_, v_sz_2070_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_ext_2068_);
return v_b_2072_;
}
else
{
lean_object* v_descr_2074_; lean_object* v_snd_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2089_; 
v_descr_2074_ = lean_ctor_get(v_ext_2068_, 0);
v_snd_2075_ = lean_ctor_get(v_b_2072_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_b_2072_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v_b_2072_, 0);
lean_dec(v_unused_2090_);
v___x_2077_ = v_b_2072_;
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snd_2075_);
lean_dec(v_b_2072_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_addEntry_2079_; lean_object* v___x_2080_; lean_object* v_a_2081_; lean_object* v_state_2082_; lean_object* v___x_2084_; 
v_addEntry_2079_ = lean_ctor_get(v_descr_2074_, 4);
v___x_2080_ = lean_box(0);
v_a_2081_ = lean_array_uget_borrowed(v_as_2069_, v_i_2071_);
lean_inc(v_addEntry_2079_);
lean_inc(v_a_2081_);
v_state_2082_ = lean_apply_2(v_addEntry_2079_, v_snd_2075_, v_a_2081_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_state_2082_);
lean_ctor_set(v___x_2077_, 0, v___x_2080_);
v___x_2084_ = v___x_2077_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_state_2082_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
size_t v___x_2085_; size_t v___x_2086_; 
v___x_2085_ = ((size_t)1ULL);
v___x_2086_ = lean_usize_add(v_i_2071_, v___x_2085_);
v_i_2071_ = v___x_2086_;
v_b_2072_ = v___x_2084_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2091_, lean_object* v_as_2092_, lean_object* v_sz_2093_, lean_object* v_i_2094_, lean_object* v_b_2095_){
_start:
{
size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2093_);
lean_dec(v_sz_2093_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2091_, v_as_2092_, v_sz_boxed_2096_, v_i_boxed_2097_, v_b_2095_);
lean_dec_ref(v_as_2092_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_ext_2099_, lean_object* v_as_2100_, size_t v_sz_2101_, size_t v_i_2102_, lean_object* v_b_2103_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_usize_dec_lt(v_i_2102_, v_sz_2101_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v_ext_2099_);
return v_b_2103_;
}
else
{
lean_object* v_descr_2105_; lean_object* v_snd_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2120_; 
v_descr_2105_ = lean_ctor_get(v_ext_2099_, 0);
v_snd_2106_ = lean_ctor_get(v_b_2103_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_b_2103_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_b_2103_, 0);
lean_dec(v_unused_2121_);
v___x_2108_ = v_b_2103_;
v_isShared_2109_ = v_isSharedCheck_2120_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_snd_2106_);
lean_dec(v_b_2103_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2120_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_addEntry_2110_; lean_object* v___x_2111_; lean_object* v_a_2112_; lean_object* v_state_2113_; lean_object* v___x_2115_; 
v_addEntry_2110_ = lean_ctor_get(v_descr_2105_, 4);
v___x_2111_ = lean_box(0);
v_a_2112_ = lean_array_uget_borrowed(v_as_2100_, v_i_2102_);
lean_inc(v_addEntry_2110_);
lean_inc(v_a_2112_);
v_state_2113_ = lean_apply_2(v_addEntry_2110_, v_snd_2106_, v_a_2112_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v_state_2113_);
lean_ctor_set(v___x_2108_, 0, v___x_2111_);
v___x_2115_ = v___x_2108_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_state_2113_);
v___x_2115_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_add(v_i_2102_, v___x_2116_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2099_, v_as_2100_, v_sz_2101_, v___x_2117_, v___x_2115_);
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_ext_2122_, lean_object* v_as_2123_, lean_object* v_sz_2124_, lean_object* v_i_2125_, lean_object* v_b_2126_){
_start:
{
size_t v_sz_boxed_2127_; size_t v_i_boxed_2128_; lean_object* v_res_2129_; 
v_sz_boxed_2127_ = lean_unbox_usize(v_sz_2124_);
lean_dec(v_sz_2124_);
v_i_boxed_2128_ = lean_unbox_usize(v_i_2125_);
lean_dec(v_i_2125_);
v_res_2129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2122_, v_as_2123_, v_sz_boxed_2127_, v_i_boxed_2128_, v_b_2126_);
lean_dec_ref(v_as_2123_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_ext_2130_, lean_object* v_t_2131_, lean_object* v_init_2132_){
_start:
{
lean_object* v_root_2133_; lean_object* v_tail_2134_; lean_object* v___x_2135_; 
v_root_2133_ = lean_ctor_get(v_t_2131_, 0);
v_tail_2134_ = lean_ctor_get(v_t_2131_, 1);
lean_inc_ref(v_ext_2130_);
lean_inc(v_init_2132_);
v___x_2135_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2132_, v_ext_2130_, v_root_2133_, v_init_2132_);
lean_dec(v_init_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
lean_dec_ref(v_ext_2130_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
return v_a_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; size_t v_sz_2140_; size_t v___x_2141_; lean_object* v___x_2142_; lean_object* v_fst_2143_; 
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_a_2137_);
v_sz_2140_ = lean_array_size(v_tail_2134_);
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2130_, v_tail_2134_, v_sz_2140_, v___x_2141_, v___x_2139_);
v_fst_2143_ = lean_ctor_get(v___x_2142_, 0);
if (lean_obj_tag(v_fst_2143_) == 0)
{
lean_object* v_snd_2144_; 
v_snd_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_snd_2144_);
lean_dec_ref(v___x_2142_);
return v_snd_2144_;
}
else
{
lean_object* v_val_2145_; 
lean_inc_ref(v_fst_2143_);
lean_dec_ref(v___x_2142_);
v_val_2145_ = lean_ctor_get(v_fst_2143_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_fst_2143_, 1);
return v_val_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_ext_2146_, lean_object* v_t_2147_, lean_object* v_init_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2146_, v_t_2147_, v_init_2148_);
lean_dec_ref(v_t_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v_namespaceName_2150_, lean_object* v_ext_2151_, lean_object* v_s_2152_){
_start:
{
lean_object* v_stateStack_2153_; 
v_stateStack_2153_ = lean_ctor_get(v_s_2152_, 0);
lean_inc(v_stateStack_2153_);
if (lean_obj_tag(v_stateStack_2153_) == 1)
{
lean_object* v_scopedEntries_2154_; lean_object* v_newEntries_2155_; lean_object* v_head_2156_; lean_object* v_tail_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2186_; 
v_scopedEntries_2154_ = lean_ctor_get(v_s_2152_, 1);
v_newEntries_2155_ = lean_ctor_get(v_s_2152_, 2);
v_head_2156_ = lean_ctor_get(v_stateStack_2153_, 0);
v_tail_2157_ = lean_ctor_get(v_stateStack_2153_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_stateStack_2153_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2159_ = v_stateStack_2153_;
v_isShared_2160_ = v_isSharedCheck_2186_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_tail_2157_);
lean_inc(v_head_2156_);
lean_dec(v_stateStack_2153_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2186_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___y_2162_; lean_object* v_state_2167_; lean_object* v_activeScopes_2168_; uint8_t v_delimitsLocal_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2185_; 
v_state_2167_ = lean_ctor_get(v_head_2156_, 0);
v_activeScopes_2168_ = lean_ctor_get(v_head_2156_, 1);
v_delimitsLocal_2169_ = lean_ctor_get_uint8(v_head_2156_, sizeof(void*)*2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_head_2156_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2171_ = v_head_2156_;
v_isShared_2172_ = v_isSharedCheck_2185_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_activeScopes_2168_);
lean_inc(v_state_2167_);
lean_dec(v_head_2156_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2185_;
goto v_resetjp_2170_;
}
v___jp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___y_2162_);
v___x_2164_ = v___x_2159_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___y_2162_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_tail_2157_);
v___x_2164_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v_scopedEntries_2154_);
lean_ctor_set(v___x_2165_, 2, v_newEntries_2155_);
return v___x_2165_;
}
}
v_resetjp_2170_:
{
uint8_t v___x_2173_; 
v___x_2173_ = l_Lean_NameSet_contains(v_activeScopes_2168_, v_namespaceName_2150_);
if (v___x_2173_ == 0)
{
lean_object* v_activeScopes_2174_; lean_object* v___x_2175_; 
lean_inc(v_newEntries_2155_);
lean_inc_ref(v_scopedEntries_2154_);
lean_dec_ref(v_s_2152_);
lean_inc(v_namespaceName_2150_);
v_activeScopes_2174_ = l_Lean_NameSet_insert(v_activeScopes_2168_, v_namespaceName_2150_);
v___x_2175_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2154_, v_namespaceName_2150_);
lean_dec(v_namespaceName_2150_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v_ext_2151_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_activeScopes_2174_);
v___x_2177_ = v___x_2171_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_state_2167_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_activeScopes_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*2, v_delimitsLocal_2169_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
v___y_2162_ = v___x_2177_;
goto v___jp_2161_;
}
}
else
{
lean_object* v_val_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v_val_2179_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2180_ = 1;
v___x_2181_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2151_, v_val_2179_, v_state_2167_);
lean_dec(v_val_2179_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_activeScopes_2174_);
lean_ctor_set(v___x_2171_, 0, v___x_2181_);
v___x_2183_ = v___x_2171_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_activeScopes_2174_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*2, v___x_2180_);
v___y_2162_ = v___x_2183_;
goto v___jp_2161_;
}
}
}
else
{
lean_del_object(v___x_2171_);
lean_dec(v_activeScopes_2168_);
lean_dec(v_state_2167_);
lean_del_object(v___x_2159_);
lean_dec(v_tail_2157_);
lean_dec_ref(v_ext_2151_);
lean_dec(v_namespaceName_2150_);
return v_s_2152_;
}
}
}
}
else
{
lean_dec(v_stateStack_2153_);
lean_dec_ref(v_ext_2151_);
lean_dec(v_namespaceName_2150_);
return v_s_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2187_, lean_object* v_env_2188_, lean_object* v_namespaceName_2189_){
_start:
{
lean_object* v_ext_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; 
v_ext_2190_ = lean_ctor_get(v_ext_2187_, 1);
lean_inc_ref(v_ext_2190_);
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2191_, 0, v_namespaceName_2189_);
lean_closure_set(v___f_2191_, 1, v_ext_2187_);
v___x_2192_ = lean_box(1);
v___x_2193_ = lean_box(0);
v___x_2194_ = 1;
v___x_2195_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2190_, v_env_2188_, v___f_2191_, v___x_2192_, v___x_2193_, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2196_, lean_object* v_00_u03b2_2197_, lean_object* v_00_u03c3_2198_, lean_object* v_ext_2199_, lean_object* v_env_2200_, lean_object* v_namespaceName_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2199_, v_env_2200_, v_namespaceName_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2203_, lean_object* v_00_u03c3_2204_, lean_object* v_00_u03b1_2205_, lean_object* v_ext_2206_, lean_object* v_t_2207_, lean_object* v_init_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_2206_, v_t_2207_, v_init_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2210_, lean_object* v_00_u03c3_2211_, lean_object* v_00_u03b1_2212_, lean_object* v_ext_2213_, lean_object* v_t_2214_, lean_object* v_init_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2210_, v_00_u03c3_2211_, v_00_u03b1_2212_, v_ext_2213_, v_t_2214_, v_init_2215_);
lean_dec_ref(v_t_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2217_, lean_object* v_00_u03c3_2218_, lean_object* v_init_2219_, lean_object* v_00_u03b1_2220_, lean_object* v_ext_2221_, lean_object* v_n_2222_, lean_object* v_b_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_2219_, v_ext_2221_, v_n_2222_, v_b_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2225_, lean_object* v_00_u03c3_2226_, lean_object* v_init_2227_, lean_object* v_00_u03b1_2228_, lean_object* v_ext_2229_, lean_object* v_n_2230_, lean_object* v_b_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2225_, v_00_u03c3_2226_, v_init_2227_, v_00_u03b1_2228_, v_ext_2229_, v_n_2230_, v_b_2231_);
lean_dec_ref(v_n_2230_);
lean_dec(v_init_2227_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2233_, lean_object* v_00_u03c3_2234_, lean_object* v_00_u03b1_2235_, lean_object* v_ext_2236_, lean_object* v_as_2237_, size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_b_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_2236_, v_as_2237_, v_sz_2238_, v_i_2239_, v_b_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2242_, lean_object* v_00_u03c3_2243_, lean_object* v_00_u03b1_2244_, lean_object* v_ext_2245_, lean_object* v_as_2246_, lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_b_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2242_, v_00_u03c3_2243_, v_00_u03b1_2244_, v_ext_2245_, v_as_2246_, v_sz_boxed_2250_, v_i_boxed_2251_, v_b_2249_);
lean_dec_ref(v_as_2246_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2253_, lean_object* v_00_u03c3_2254_, lean_object* v_init_2255_, lean_object* v_00_u03b1_2256_, lean_object* v_ext_2257_, lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_b_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_2255_, v_ext_2257_, v_as_2258_, v_sz_2259_, v_i_2260_, v_b_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2263_, lean_object* v_00_u03c3_2264_, lean_object* v_init_2265_, lean_object* v_00_u03b1_2266_, lean_object* v_ext_2267_, lean_object* v_as_2268_, lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_b_2271_){
_start:
{
size_t v_sz_boxed_2272_; size_t v_i_boxed_2273_; lean_object* v_res_2274_; 
v_sz_boxed_2272_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2273_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2263_, v_00_u03c3_2264_, v_init_2265_, v_00_u03b1_2266_, v_ext_2267_, v_as_2268_, v_sz_boxed_2272_, v_i_boxed_2273_, v_b_2271_);
lean_dec_ref(v_as_2268_);
lean_dec(v_init_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2275_, lean_object* v_00_u03c3_2276_, lean_object* v_00_u03b1_2277_, lean_object* v_ext_2278_, lean_object* v_as_2279_, size_t v_sz_2280_, size_t v_i_2281_, lean_object* v_b_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_2278_, v_as_2279_, v_sz_2280_, v_i_2281_, v_b_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_00_u03c3_2285_, lean_object* v_00_u03b1_2286_, lean_object* v_ext_2287_, lean_object* v_as_2288_, lean_object* v_sz_2289_, lean_object* v_i_2290_, lean_object* v_b_2291_){
_start:
{
size_t v_sz_boxed_2292_; size_t v_i_boxed_2293_; lean_object* v_res_2294_; 
v_sz_boxed_2292_ = lean_unbox_usize(v_sz_2289_);
lean_dec(v_sz_2289_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_2284_, v_00_u03c3_2285_, v_00_u03b1_2286_, v_ext_2287_, v_as_2288_, v_sz_boxed_2292_, v_i_boxed_2293_, v_b_2291_);
lean_dec_ref(v_as_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2295_, lean_object* v_00_u03c3_2296_, lean_object* v_00_u03b1_2297_, lean_object* v_ext_2298_, lean_object* v_as_2299_, size_t v_sz_2300_, size_t v_i_2301_, lean_object* v_b_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_2298_, v_as_2299_, v_sz_2300_, v_i_2301_, v_b_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2304_, lean_object* v_00_u03c3_2305_, lean_object* v_00_u03b1_2306_, lean_object* v_ext_2307_, lean_object* v_as_2308_, lean_object* v_sz_2309_, lean_object* v_i_2310_, lean_object* v_b_2311_){
_start:
{
size_t v_sz_boxed_2312_; size_t v_i_boxed_2313_; lean_object* v_res_2314_; 
v_sz_boxed_2312_ = lean_unbox_usize(v_sz_2309_);
lean_dec(v_sz_2309_);
v_i_boxed_2313_ = lean_unbox_usize(v_i_2310_);
lean_dec(v_i_2310_);
v_res_2314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_2304_, v_00_u03c3_2305_, v_00_u03b1_2306_, v_ext_2307_, v_as_2308_, v_sz_boxed_2312_, v_i_boxed_2313_, v_b_2311_);
lean_dec_ref(v_as_2308_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_2315_, lean_object* v_00_u03c3_2316_, lean_object* v_00_u03b1_2317_, lean_object* v_ext_2318_, lean_object* v_as_2319_, size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_b_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_2318_, v_as_2319_, v_sz_2320_, v_i_2321_, v_b_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2324_, lean_object* v_00_u03c3_2325_, lean_object* v_00_u03b1_2326_, lean_object* v_ext_2327_, lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_b_2331_){
_start:
{
size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_2324_, v_00_u03c3_2325_, v_00_u03b1_2326_, v_ext_2327_, v_as_2328_, v_sz_boxed_2332_, v_i_boxed_2333_, v_b_2331_);
lean_dec_ref(v_as_2328_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2335_, lean_object* v_s_2336_){
_start:
{
lean_object* v_stateStack_2337_; 
v_stateStack_2337_ = lean_ctor_get(v_s_2336_, 0);
lean_inc(v_stateStack_2337_);
if (lean_obj_tag(v_stateStack_2337_) == 1)
{
lean_object* v_head_2338_; lean_object* v_scopedEntries_2339_; lean_object* v_newEntries_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2367_; 
v_head_2338_ = lean_ctor_get(v_stateStack_2337_, 0);
lean_inc(v_head_2338_);
v_scopedEntries_2339_ = lean_ctor_get(v_s_2336_, 1);
v_newEntries_2340_ = lean_ctor_get(v_s_2336_, 2);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_s_2336_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; 
v_unused_2368_ = lean_ctor_get(v_s_2336_, 0);
lean_dec(v_unused_2368_);
v___x_2342_ = v_s_2336_;
v_isShared_2343_ = v_isSharedCheck_2367_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_newEntries_2340_);
lean_inc(v_scopedEntries_2339_);
lean_dec(v_s_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2367_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_tail_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2365_; 
v_tail_2344_ = lean_ctor_get(v_stateStack_2337_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_stateStack_2337_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_stateStack_2337_, 0);
lean_dec(v_unused_2366_);
v___x_2346_ = v_stateStack_2337_;
v_isShared_2347_ = v_isSharedCheck_2365_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_tail_2344_);
lean_dec(v_stateStack_2337_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2365_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_state_2348_; lean_object* v_activeScopes_2349_; uint8_t v_delimitsLocal_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2364_; 
v_state_2348_ = lean_ctor_get(v_head_2338_, 0);
v_activeScopes_2349_ = lean_ctor_get(v_head_2338_, 1);
v_delimitsLocal_2350_ = lean_ctor_get_uint8(v_head_2338_, sizeof(void*)*2);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_head_2338_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2352_ = v_head_2338_;
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_activeScopes_2349_);
lean_inc(v_state_2348_);
lean_dec(v_head_2338_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_apply_1(v_f_2335_, v_state_2348_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_activeScopes_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2363_, sizeof(void*)*2, v_delimitsLocal_2350_);
v___x_2356_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2356_);
v___x_2358_ = v___x_2346_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_tail_2344_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2358_);
v___x_2360_ = v___x_2342_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_scopedEntries_2339_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_newEntries_2340_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
else
{
lean_dec(v_stateStack_2337_);
lean_dec(v_f_2335_);
return v_s_2336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2369_, lean_object* v_env_2370_, lean_object* v_f_2371_){
_start:
{
lean_object* v_ext_2372_; lean_object* v_toEnvExtension_2373_; lean_object* v_asyncMode_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; 
v_ext_2372_ = lean_ctor_get(v_ext_2369_, 1);
lean_inc_ref(v_ext_2372_);
lean_dec_ref(v_ext_2369_);
v_toEnvExtension_2373_ = lean_ctor_get(v_ext_2372_, 0);
v_asyncMode_2374_ = lean_ctor_get(v_toEnvExtension_2373_, 2);
lean_inc(v_asyncMode_2374_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2375_, 0, v_f_2371_);
v___x_2376_ = lean_box(0);
v___x_2377_ = 1;
v___x_2378_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v_ext_2372_, v_env_2370_, v___f_2375_, v_asyncMode_2374_, v___x_2376_, v___x_2377_);
lean_dec(v_asyncMode_2374_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2379_, lean_object* v_00_u03b2_2380_, lean_object* v_00_u03c3_2381_, lean_object* v_ext_2382_, lean_object* v_env_2383_, lean_object* v_f_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2382_, v_env_2383_, v_f_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2386_, lean_object* v_____s_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_apply_2(v_toPure_2386_, lean_box(0), v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2390_, lean_object* v_toPure_2391_, lean_object* v_r_2392_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
v___x_2394_ = lean_apply_2(v_toPure_2391_, lean_box(0), v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2395_, lean_object* v_toBind_2396_, lean_object* v___f_2397_, lean_object* v_a_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_modifyEnv_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_modifyEnv_2401_ = lean_ctor_get(v_inst_2395_, 1);
lean_inc(v_modifyEnv_2401_);
lean_dec_ref(v_inst_2395_);
v___x_2402_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2402_, 0, lean_box(0));
lean_closure_set(v___x_2402_, 1, lean_box(0));
lean_closure_set(v___x_2402_, 2, lean_box(0));
lean_closure_set(v___x_2402_, 3, v_a_2398_);
v___x_2403_ = lean_apply_1(v_modifyEnv_2401_, v___x_2402_);
v___x_2404_ = lean_apply_4(v_toBind_2396_, lean_box(0), lean_box(0), v___x_2403_, v___f_2397_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2405_, lean_object* v_inst_2406_, lean_object* v_toBind_2407_, lean_object* v_inst_2408_, lean_object* v___f_2409_, lean_object* v_____do__lift_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; size_t v_sz_2414_; size_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2411_ = lean_box(0);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2412_, 0, v___x_2411_);
lean_closure_set(v___f_2412_, 1, v_toPure_2405_);
lean_inc(v_toBind_2407_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2413_, 0, v_inst_2406_);
lean_closure_set(v___f_2413_, 1, v_toBind_2407_);
lean_closure_set(v___f_2413_, 2, v___f_2412_);
v_sz_2414_ = lean_array_size(v_____do__lift_2410_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2408_, v_____do__lift_2410_, v___f_2413_, v_sz_2414_, v___x_2415_, v___x_2411_);
v___x_2417_ = lean_apply_4(v_toBind_2407_, lean_box(0), lean_box(0), v___x_2416_, v___f_2409_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = l_Lean_scopedEnvExtensionsRef;
v___x_2419_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2419_, 0, lean_box(0));
lean_closure_set(v___x_2419_, 1, lean_box(0));
lean_closure_set(v___x_2419_, 2, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_){
_start:
{
lean_object* v_toApplicative_2423_; lean_object* v_toBind_2424_; lean_object* v_toPure_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; 
v_toApplicative_2423_ = lean_ctor_get(v_inst_2420_, 0);
v_toBind_2424_ = lean_ctor_get(v_inst_2420_, 1);
lean_inc_n(v_toBind_2424_, 2);
v_toPure_2425_ = lean_ctor_get(v_toApplicative_2423_, 1);
lean_inc_n(v_toPure_2425_, 2);
v___x_2426_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2427_ = lean_apply_2(v_inst_2422_, lean_box(0), v___x_2426_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2428_, 0, v_toPure_2425_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2429_, 0, v_toPure_2425_);
lean_closure_set(v___f_2429_, 1, v_inst_2421_);
lean_closure_set(v___f_2429_, 2, v_toBind_2424_);
lean_closure_set(v___f_2429_, 3, v_inst_2420_);
lean_closure_set(v___f_2429_, 4, v___f_2428_);
v___x_2430_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v___x_2427_, v___f_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_pushScope___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2436_, lean_object* v_toBind_2437_, lean_object* v___f_2438_, lean_object* v_a_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_modifyEnv_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_modifyEnv_2442_ = lean_ctor_get(v_inst_2436_, 1);
lean_inc(v_modifyEnv_2442_);
lean_dec_ref(v_inst_2436_);
v___x_2443_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2443_, 0, lean_box(0));
lean_closure_set(v___x_2443_, 1, lean_box(0));
lean_closure_set(v___x_2443_, 2, lean_box(0));
lean_closure_set(v___x_2443_, 3, v_a_2439_);
v___x_2444_ = lean_apply_1(v_modifyEnv_2442_, v___x_2443_);
v___x_2445_ = lean_apply_4(v_toBind_2437_, lean_box(0), lean_box(0), v___x_2444_, v___f_2438_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2446_, lean_object* v_inst_2447_, lean_object* v_toBind_2448_, lean_object* v_inst_2449_, lean_object* v___f_2450_, lean_object* v_____do__lift_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; size_t v_sz_2455_; size_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2452_ = lean_box(0);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2453_, 0, v___x_2452_);
lean_closure_set(v___f_2453_, 1, v_toPure_2446_);
lean_inc(v_toBind_2448_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2454_, 0, v_inst_2447_);
lean_closure_set(v___f_2454_, 1, v_toBind_2448_);
lean_closure_set(v___f_2454_, 2, v___f_2453_);
v_sz_2455_ = lean_array_size(v_____do__lift_2451_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2449_, v_____do__lift_2451_, v___f_2454_, v_sz_2455_, v___x_2456_, v___x_2452_);
v___x_2458_ = lean_apply_4(v_toBind_2448_, lean_box(0), lean_box(0), v___x_2457_, v___f_2450_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_){
_start:
{
lean_object* v_toApplicative_2462_; lean_object* v_toBind_2463_; lean_object* v_toPure_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; 
v_toApplicative_2462_ = lean_ctor_get(v_inst_2459_, 0);
v_toBind_2463_ = lean_ctor_get(v_inst_2459_, 1);
lean_inc_n(v_toBind_2463_, 2);
v_toPure_2464_ = lean_ctor_get(v_toApplicative_2462_, 1);
lean_inc_n(v_toPure_2464_, 2);
v___x_2465_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2466_ = lean_apply_2(v_inst_2461_, lean_box(0), v___x_2465_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2467_, 0, v_toPure_2464_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2468_, 0, v_toPure_2464_);
lean_closure_set(v___f_2468_, 1, v_inst_2460_);
lean_closure_set(v___f_2468_, 2, v_toBind_2463_);
lean_closure_set(v___f_2468_, 3, v_inst_2459_);
lean_closure_set(v___f_2468_, 4, v___f_2467_);
v___x_2469_ = lean_apply_4(v_toBind_2463_, lean_box(0), lean_box(0), v___x_2466_, v___f_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_popScope___redArg(v_inst_2471_, v_inst_2472_, v_inst_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2475_, lean_object* v_depth_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2475_, v_x_2477_, v_depth_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2479_, lean_object* v_depth_2480_, lean_object* v_toBind_2481_, lean_object* v___f_2482_, lean_object* v_a_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_modifyEnv_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_modifyEnv_2486_ = lean_ctor_get(v_inst_2479_, 1);
lean_inc(v_modifyEnv_2486_);
lean_dec_ref(v_inst_2479_);
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2487_, 0, v_a_2483_);
lean_closure_set(v___f_2487_, 1, v_depth_2480_);
v___x_2488_ = lean_apply_1(v_modifyEnv_2486_, v___f_2487_);
v___x_2489_ = lean_apply_4(v_toBind_2481_, lean_box(0), lean_box(0), v___x_2488_, v___f_2482_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2490_, lean_object* v_inst_2491_, lean_object* v_depth_2492_, lean_object* v_toBind_2493_, lean_object* v_inst_2494_, lean_object* v___f_2495_, lean_object* v_____do__lift_2496_){
_start:
{
lean_object* v___x_2497_; lean_object* v___f_2498_; lean_object* v___f_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2497_ = lean_box(0);
v___f_2498_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2498_, 0, v___x_2497_);
lean_closure_set(v___f_2498_, 1, v_toPure_2490_);
lean_inc(v_toBind_2493_);
v___f_2499_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2499_, 0, v_inst_2491_);
lean_closure_set(v___f_2499_, 1, v_depth_2492_);
lean_closure_set(v___f_2499_, 2, v_toBind_2493_);
lean_closure_set(v___f_2499_, 3, v___f_2498_);
v_sz_2500_ = lean_array_size(v_____do__lift_2496_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2494_, v_____do__lift_2496_, v___f_2499_, v_sz_2500_, v___x_2501_, v___x_2497_);
v___x_2503_ = lean_apply_4(v_toBind_2493_, lean_box(0), lean_box(0), v___x_2502_, v___f_2495_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_depth_2507_){
_start:
{
lean_object* v_toApplicative_2508_; lean_object* v_toBind_2509_; lean_object* v_toPure_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; 
v_toApplicative_2508_ = lean_ctor_get(v_inst_2504_, 0);
v_toBind_2509_ = lean_ctor_get(v_inst_2504_, 1);
lean_inc_n(v_toBind_2509_, 2);
v_toPure_2510_ = lean_ctor_get(v_toApplicative_2508_, 1);
lean_inc_n(v_toPure_2510_, 2);
v___x_2511_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2512_ = lean_apply_2(v_inst_2506_, lean_box(0), v___x_2511_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2513_, 0, v_toPure_2510_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2514_, 0, v_toPure_2510_);
lean_closure_set(v___f_2514_, 1, v_inst_2505_);
lean_closure_set(v___f_2514_, 2, v_depth_2507_);
lean_closure_set(v___f_2514_, 3, v_toBind_2509_);
lean_closure_set(v___f_2514_, 4, v_inst_2504_);
lean_closure_set(v___f_2514_, 5, v___f_2513_);
v___x_2515_ = lean_apply_4(v_toBind_2509_, lean_box(0), lean_box(0), v___x_2512_, v___f_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_depth_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_setDelimitsLocal___redArg(v_inst_2517_, v_inst_2518_, v_inst_2519_, v_depth_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2522_, lean_object* v_namespaceName_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2522_, v_x_2524_, v_namespaceName_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2526_, lean_object* v_namespaceName_2527_, lean_object* v_toBind_2528_, lean_object* v___f_2529_, lean_object* v_a_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_modifyEnv_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_modifyEnv_2533_ = lean_ctor_get(v_inst_2526_, 1);
lean_inc(v_modifyEnv_2533_);
lean_dec_ref(v_inst_2526_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2534_, 0, v_a_2530_);
lean_closure_set(v___f_2534_, 1, v_namespaceName_2527_);
v___x_2535_ = lean_apply_1(v_modifyEnv_2533_, v___f_2534_);
v___x_2536_ = lean_apply_4(v_toBind_2528_, lean_box(0), lean_box(0), v___x_2535_, v___f_2529_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2537_, lean_object* v_inst_2538_, lean_object* v_namespaceName_2539_, lean_object* v_toBind_2540_, lean_object* v_inst_2541_, lean_object* v___f_2542_, lean_object* v_____do__lift_2543_){
_start:
{
lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; size_t v_sz_2547_; size_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2544_ = lean_box(0);
v___f_2545_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2545_, 0, v___x_2544_);
lean_closure_set(v___f_2545_, 1, v_toPure_2537_);
lean_inc(v_toBind_2540_);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2546_, 0, v_inst_2538_);
lean_closure_set(v___f_2546_, 1, v_namespaceName_2539_);
lean_closure_set(v___f_2546_, 2, v_toBind_2540_);
lean_closure_set(v___f_2546_, 3, v___f_2545_);
v_sz_2547_ = lean_array_size(v_____do__lift_2543_);
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2541_, v_____do__lift_2543_, v___f_2546_, v_sz_2547_, v___x_2548_, v___x_2544_);
v___x_2550_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2549_, v___f_2542_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_namespaceName_2554_){
_start:
{
lean_object* v_toApplicative_2555_; lean_object* v_toBind_2556_; lean_object* v_toPure_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; 
v_toApplicative_2555_ = lean_ctor_get(v_inst_2551_, 0);
v_toBind_2556_ = lean_ctor_get(v_inst_2551_, 1);
lean_inc_n(v_toBind_2556_, 2);
v_toPure_2557_ = lean_ctor_get(v_toApplicative_2555_, 1);
lean_inc_n(v_toPure_2557_, 2);
v___x_2558_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2559_ = lean_apply_2(v_inst_2553_, lean_box(0), v___x_2558_);
v___f_2560_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2560_, 0, v_toPure_2557_);
v___f_2561_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2561_, 0, v_toPure_2557_);
lean_closure_set(v___f_2561_, 1, v_inst_2552_);
lean_closure_set(v___f_2561_, 2, v_namespaceName_2554_);
lean_closure_set(v___f_2561_, 3, v_toBind_2556_);
lean_closure_set(v___f_2561_, 4, v_inst_2551_);
lean_closure_set(v___f_2561_, 5, v___f_2560_);
v___x_2562_ = lean_apply_4(v_toBind_2556_, lean_box(0), lean_box(0), v___x_2559_, v___f_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_namespaceName_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_activateScoped___redArg(v_inst_2564_, v_inst_2565_, v_inst_2566_, v_namespaceName_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_2570_){
_start:
{
lean_inc(v___y_2570_);
return v___y_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_2571_);
lean_dec(v___y_2571_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_2573_, lean_object* v_a_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_a_2574_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_2578_, lean_object* v_a_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_2578_, v_a_2579_, v___y_2580_);
lean_dec_ref(v___y_2580_);
lean_dec(v_x_2578_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_initial_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_2591_){
_start:
{
lean_object* v_name_2593_; lean_object* v_addEntry_2594_; lean_object* v_initial_2595_; lean_object* v_finalizeImport_2596_; lean_object* v_exportEntry_x3f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_name_2593_ = lean_ctor_get(v_descr_2591_, 0);
lean_inc(v_name_2593_);
v_addEntry_2594_ = lean_ctor_get(v_descr_2591_, 1);
lean_inc(v_addEntry_2594_);
v_initial_2595_ = lean_ctor_get(v_descr_2591_, 2);
lean_inc(v_initial_2595_);
v_finalizeImport_2596_ = lean_ctor_get(v_descr_2591_, 3);
lean_inc(v_finalizeImport_2596_);
v_exportEntry_x3f_2597_ = lean_ctor_get(v_descr_2591_, 4);
lean_inc_ref(v_exportEntry_x3f_2597_);
lean_dec_ref(v_descr_2591_);
v___f_2598_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_2599_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2600_, 0, v_initial_2595_);
v___x_2601_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2601_, 0, v_name_2593_);
lean_ctor_set(v___x_2601_, 1, v___f_2600_);
lean_ctor_set(v___x_2601_, 2, v___f_2599_);
lean_ctor_set(v___x_2601_, 3, v___f_2598_);
lean_ctor_set(v___x_2601_, 4, v_addEntry_2594_);
lean_ctor_set(v___x_2601_, 5, v_finalizeImport_2596_);
lean_ctor_set(v___x_2601_, 6, v_exportEntry_x3f_2597_);
v___x_2602_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_2606_, lean_object* v_00_u03c3_2607_, lean_object* v_descr_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_00_u03c3_2612_, lean_object* v_descr_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_2611_, v_00_u03c3_2612_, v_descr_2613_);
return v_res_2615_;
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
