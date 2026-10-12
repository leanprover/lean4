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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0 = (const lean_object*)&l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value;
static const lean_string_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "scoped environment extension `"};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2_value;
static const lean_string_object l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "` with `logWrites` must set `entryDecl\?`"};
static const lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3 = (const lean_object*)&l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
static const lean_ctor_object l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0 = (const lean_object*)&l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_16_);
lean_dec_ref_known(v_t_11_, 2);
v___x_17_ = lean_apply_2(v_k_12_, v_a_15_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_ScopedEnvExtension_Entry_ctorElim(v_00_u03b1_25_, v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim___redArg(lean_object* v_t_32_, lean_object* v_global_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_32_, v_global_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_global_elim(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_global_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_37_, v_global_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim___redArg(lean_object* v_t_41_, lean_object* v_scoped_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_41_, v_scoped_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Entry_scoped_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_scoped_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_46_, v_scoped_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = lean_unsigned_to_nat(16u);
v___x_52_ = lean_mk_array(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__0);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_56_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__2);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__3);
v___x_60_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__1);
v___x_61_ = 1;
v___x_62_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_59_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*2, v___x_61_);
return v___x_62_;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_65_;
v_res_65_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
stack->m_obj
 = v_res_65_;
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
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg(){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_73_;
v_res_73_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg();
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg___boxed(lean_object* v___dummy_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_79_ = lean_box(0);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_79_);
return v___x_80_;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg(){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_83_;
v_res_83_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___boxed(lean_object* v___dummy_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v_res_85_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_00_u03c3_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_90_;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg(){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg___boxed(lean_object* v___dummy_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg();
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_127_ = l_Lean_mkAtom(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_129_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_130_ = lean_array_push(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_140_ = l_Lean_mkAtom(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_142_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_143_ = lean_array_push(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_145_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_146_ = lean_box(2);
v___x_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_149_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_150_ = lean_array_push(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_152_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_153_ = lean_box(2);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
lean_ctor_set(v___x_154_, 2, v___x_151_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_156_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_157_ = lean_array_push(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_159_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_160_ = lean_box(2);
v___x_161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_158_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_163_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_164_ = lean_array_push(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_166_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_167_ = lean_box(2);
v___x_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_170_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_171_ = lean_array_push(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_173_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_174_ = lean_box(2);
v___x_175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_172_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_176_;
}
}
uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(lean_object* v_descr_177_){
_start:
{
uint8_t v_trackGen_178_; 
v_trackGen_178_ = lean_ctor_get_uint8(v_descr_177_, sizeof(void*)*8);
if (v_trackGen_178_ == 0)
{
uint8_t v_logWrites_179_; 
v_logWrites_179_ = lean_ctor_get_uint8(v_descr_177_, sizeof(void*)*8 + 1);
return v_logWrites_179_;
}
else
{
return v_trackGen_178_;
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_177_ = stack[0].m_obj;
uint8_t v_res_180_;
v_res_180_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_177_);
stack->m_num = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg___boxed(lean_object* v_descr_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_181_);
lean_dec_ref(v_descr_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_00_u03c3_186_, lean_object* v_descr_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_Descr_tracksScopes_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_187_ = stack[3].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes(lean_box(0), lean_box(0), lean_box(0), v_descr_187_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___boxed(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_00_u03c3_192_, lean_object* v_descr_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes(v_00_u03b1_190_, v_00_u03b2_191_, v_00_u03c3_192_, v_descr_193_);
lean_dec_ref(v_descr_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object* v_descr_196_, lean_object* v_s_197_, lean_object* v_b_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_196_);
if (v___x_199_ == 0)
{
lean_dec(v_b_198_);
lean_dec_ref(v_descr_196_);
return v_s_197_;
}
else
{
lean_object* v_entryDecl_x3f_200_; 
v_entryDecl_x3f_200_ = lean_ctor_get(v_descr_196_, 7);
lean_inc(v_entryDecl_x3f_200_);
lean_dec_ref(v_descr_196_);
if (lean_obj_tag(v_entryDecl_x3f_200_) == 0)
{
lean_object* v_state_201_; lean_object* v_activeScopes_202_; uint8_t v_delimitsLocal_203_; lean_object* v_scopeChangedDecls_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_b_198_);
v_state_201_ = lean_ctor_get(v_s_197_, 0);
v_activeScopes_202_ = lean_ctor_get(v_s_197_, 1);
v_delimitsLocal_203_ = lean_ctor_get_uint8(v_s_197_, sizeof(void*)*3);
v_scopeChangedDecls_204_ = lean_ctor_get(v_s_197_, 2);
v_isSharedCheck_211_ = !lean_is_exclusive(v_s_197_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v_s_197_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_scopeChangedDecls_204_);
lean_inc(v_activeScopes_202_);
lean_inc(v_state_201_);
lean_dec(v_s_197_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_state_201_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_activeScopes_202_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v_scopeChangedDecls_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*3, v_delimitsLocal_203_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*3 + 1, v___x_199_);
return v___x_209_;
}
}
}
else
{
lean_object* v_state_212_; lean_object* v_activeScopes_213_; uint8_t v_delimitsLocal_214_; lean_object* v_scopeChangedDecls_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
v_state_212_ = lean_ctor_get(v_s_197_, 0);
v_activeScopes_213_ = lean_ctor_get(v_s_197_, 1);
v_delimitsLocal_214_ = lean_ctor_get_uint8(v_s_197_, sizeof(void*)*3);
v_scopeChangedDecls_215_ = lean_ctor_get(v_s_197_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_s_197_);
if (v_isSharedCheck_225_ == 0)
{
v___x_217_ = v_s_197_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_scopeChangedDecls_215_);
lean_inc(v_activeScopes_213_);
lean_inc(v_state_212_);
lean_dec(v_s_197_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_val_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v_val_219_ = lean_ctor_get(v_entryDecl_x3f_200_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v_entryDecl_x3f_200_, 1);
v___x_220_ = lean_apply_1(v_val_219_, v_b_198_);
v___x_221_ = lean_array_push(v_scopeChangedDecls_215_, v___x_220_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v___x_221_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_state_212_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_activeScopes_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v___x_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*3, v_delimitsLocal_214_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*3 + 1, v___x_199_);
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_00_u03c3_228_, lean_object* v_descr_229_, lean_object* v_s_230_, lean_object* v_b_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_229_, v_s_230_, v_b_231_);
return v___x_232_;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_236_ = stack[0].m_obj;
lean_object* v___y_237_ = stack[1].m_obj;
lean_object* v___y_238_ = stack[2].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_236_, v___y_237_, v___y_238_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_243_, v___y_244_, v___y_245_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v_x_243_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_248_, lean_object* v_x_249_){
_start:
{
lean_inc(v_inst_248_);
return v_inst_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_250_, v_x_251_);
lean_dec(v_x_251_);
lean_dec(v_inst_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_253_, lean_object* v_x_254_){
_start:
{
lean_inc(v_s_253_);
return v_s_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_255_, lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_255_, v_x_256_);
lean_dec(v_x_256_);
lean_dec(v_s_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_259_);
lean_inc_ref_n(v___x_260_, 2);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_262_, v_a_263_);
lean_dec_ref(v_x_262_);
return v_res_264_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = l_instInhabitedError;
v___x_269_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, lean_box(0));
lean_closure_set(v___x_269_, 2, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_271_){
_start:
{
lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___f_272_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_273_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_273_, 0, v_inst_271_);
v___f_274_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_275_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_276_ = lean_box(0);
v___x_277_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_278_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_279_ = 0;
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_281_, 0, v___x_276_);
lean_ctor_set(v___x_281_, 1, v___x_277_);
lean_ctor_set(v___x_281_, 2, v___f_272_);
lean_ctor_set(v___x_281_, 3, v___f_273_);
lean_ctor_set(v___x_281_, 4, v___f_274_);
lean_ctor_set(v___x_281_, 5, v___x_278_);
lean_ctor_set(v___x_281_, 6, v___f_275_);
lean_ctor_set(v___x_281_, 7, v___x_280_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*8, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*8 + 1, v___x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_00_u03c3_284_, lean_object* v_inst_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_285_);
return v___x_286_;
}
}
lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_289_){
_start:
{
lean_object* v_mkInitial_291_; lean_object* v___x_292_; 
v_mkInitial_291_ = lean_ctor_get(v_descr_289_, 1);
lean_inc_ref(v_mkInitial_291_);
lean_dec_ref(v_descr_289_);
v___x_292_ = lean_apply_1(v_mkInitial_291_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_309_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_309_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_309_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_309_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; uint8_t v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_297_ = l_Lean_NameSet_empty;
v___x_298_ = 1;
v___x_299_ = 0;
v___x_300_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_301_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_301_, 0, v_a_293_);
lean_ctor_set(v___x_301_, 1, v___x_297_);
lean_ctor_set(v___x_301_, 2, v___x_300_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*3, v___x_298_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*3 + 1, v___x_299_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_305_);
v___x_307_ = v___x_295_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_292_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_292_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_mkInitial___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_289_ = stack[0].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_289_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_319_);
return v_res_321_;
}
}
lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_00_u03c3_324_, lean_object* v_descr_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_325_);
return v___x_327_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_mkInitial_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_325_ = stack[3].m_obj;
lean_object* v_res_328_;
v_res_328_ = l_Lean_ScopedEnvExtension_mkInitial(lean_box(0), lean_box(0), lean_box(0), v_descr_325_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_00_u03c3_331_, lean_object* v_descr_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_329_, v_00_u03b2_330_, v_00_u03c3_331_, v_descr_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; uint8_t v___x_341_; 
v_key_338_ = lean_ctor_get(v_x_336_, 0);
v_value_339_ = lean_ctor_get(v_x_336_, 1);
v_tail_340_ = lean_ctor_get(v_x_336_, 2);
v___x_341_ = lean_name_eq(v_key_338_, v_a_335_);
if (v___x_341_ == 0)
{
v_x_336_ = v_tail_340_;
goto _start;
}
else
{
lean_object* v___x_343_; 
lean_inc(v_value_339_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_value_339_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_buckets_349_; lean_object* v___x_350_; uint64_t v___y_352_; 
v_buckets_349_ = lean_ctor_get(v_m_347_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
if (lean_obj_tag(v_a_348_) == 0)
{
uint64_t v___x_366_; 
v___x_366_ = 1723ULL;
v___y_352_ = v___x_366_;
goto v___jp_351_;
}
else
{
uint64_t v_hash_367_; 
v_hash_367_ = lean_ctor_get_uint64(v_a_348_, sizeof(void*)*2);
v___y_352_ = v_hash_367_;
goto v___jp_351_;
}
v___jp_351_:
{
uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v_fold_355_; uint64_t v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_353_ = 32ULL;
v___x_354_ = lean_uint64_shift_right(v___y_352_, v___x_353_);
v_fold_355_ = lean_uint64_xor(v___y_352_, v___x_354_);
v___x_356_ = 16ULL;
v___x_357_ = lean_uint64_shift_right(v_fold_355_, v___x_356_);
v___x_358_ = lean_uint64_xor(v_fold_355_, v___x_357_);
v___x_359_ = lean_uint64_to_usize(v___x_358_);
v___x_360_ = lean_usize_of_nat(v___x_350_);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_sub(v___x_360_, v___x_361_);
v___x_363_ = lean_usize_land(v___x_359_, v___x_362_);
v___x_364_ = lean_array_uget_borrowed(v_buckets_349_, v___x_363_);
v___x_365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_348_, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_m_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_371_, lean_object* v_vals_372_, lean_object* v_i_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_array_get_size(v_keys_371_);
v___x_376_ = lean_nat_dec_lt(v_i_373_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_i_373_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_k_x27_378_; uint8_t v___x_379_; 
v_k_x27_378_ = lean_array_fget_borrowed(v_keys_371_, v_i_373_);
v___x_379_ = lean_name_eq(v_k_374_, v_k_x27_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_i_373_, v___x_380_);
lean_dec(v_i_373_);
v_i_373_ = v___x_381_;
goto _start;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_array_fget_borrowed(v_vals_372_, v_i_373_);
lean_dec(v_i_373_);
lean_inc(v___x_383_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_k_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_385_, v_vals_386_, v_i_387_, v_k_388_);
lean_dec(v_k_388_);
lean_dec_ref(v_vals_386_);
lean_dec_ref(v_keys_385_);
return v_res_389_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_390_, size_t v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_es_393_; lean_object* v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v_j_397_; lean_object* v___x_398_; 
v_es_393_ = lean_ctor_get(v_x_390_, 0);
v___x_394_ = lean_box(2);
v___x_395_ = ((size_t)31ULL);
v___x_396_ = lean_usize_land(v_x_391_, v___x_395_);
v_j_397_ = lean_usize_to_nat(v___x_396_);
v___x_398_ = lean_array_get_borrowed(v___x_394_, v_es_393_, v_j_397_);
lean_dec(v_j_397_);
switch(lean_obj_tag(v___x_398_))
{
case 0:
{
lean_object* v_key_399_; lean_object* v_val_400_; uint8_t v___x_401_; 
v_key_399_ = lean_ctor_get(v___x_398_, 0);
v_val_400_ = lean_ctor_get(v___x_398_, 1);
v___x_401_ = lean_name_eq(v_x_392_, v_key_399_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
lean_inc(v_val_400_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_val_400_);
return v___x_403_;
}
}
case 1:
{
lean_object* v_node_404_; size_t v___x_405_; size_t v___x_406_; 
v_node_404_ = lean_ctor_get(v___x_398_, 0);
v___x_405_ = ((size_t)5ULL);
v___x_406_ = lean_usize_shift_right(v_x_391_, v___x_405_);
v_x_390_ = v_node_404_;
v_x_391_ = v___x_406_;
goto _start;
}
default: 
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
}
else
{
lean_object* v_ks_409_; lean_object* v_vs_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_ks_409_ = lean_ctor_get(v_x_390_, 0);
v_vs_410_ = lean_ctor_get(v_x_390_, 1);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_409_, v_vs_410_, v___x_411_, v_x_392_);
return v___x_412_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_390_ = stack[0].m_obj;
size_t v_x_391_ = stack[1].m_num;
lean_object* v_x_392_ = stack[2].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_390_, v_x_391_, v_x_392_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
size_t v_x_1094__boxed_417_; lean_object* v_res_418_; 
v_x_1094__boxed_417_ = lean_unbox_usize(v_x_415_);
lean_dec(v_x_415_);
v_res_418_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_414_, v_x_1094__boxed_417_, v_x_416_);
lean_dec(v_x_416_);
lean_dec_ref(v_x_414_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint64_t v___y_422_; 
if (lean_obj_tag(v_x_420_) == 0)
{
uint64_t v___x_425_; 
v___x_425_ = 1723ULL;
v___y_422_ = v___x_425_;
goto v___jp_421_;
}
else
{
uint64_t v_hash_426_; 
v_hash_426_ = lean_ctor_get_uint64(v_x_420_, sizeof(void*)*2);
v___y_422_ = v_hash_426_;
goto v___jp_421_;
}
v___jp_421_:
{
size_t v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_uint64_to_usize(v___y_422_);
v___x_424_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_419_, v___x_423_, v_x_420_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_427_, v_x_428_);
lean_dec(v_x_428_);
lean_dec_ref(v_x_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_stage_u2081_432_; 
v_stage_u2081_432_ = lean_ctor_get_uint8(v_x_430_, sizeof(void*)*2);
if (v_stage_u2081_432_ == 0)
{
lean_object* v_map_u2081_433_; lean_object* v_map_u2082_434_; lean_object* v___x_435_; 
v_map_u2081_433_ = lean_ctor_get(v_x_430_, 0);
v_map_u2082_434_ = lean_ctor_get(v_x_430_, 1);
v___x_435_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_434_, v_x_431_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_433_, v_x_431_);
return v___x_436_;
}
else
{
return v___x_435_;
}
}
else
{
lean_object* v_map_u2081_437_; lean_object* v___x_438_; 
v_map_u2081_437_ = lean_ctor_get(v_x_430_, 0);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_437_, v_x_431_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec_ref(v_x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_442_, lean_object* v_b_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_b_443_);
lean_dec(v_a_442_);
return v_x_444_;
}
else
{
lean_object* v_key_445_; lean_object* v_value_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_459_; 
v_key_445_ = lean_ctor_get(v_x_444_, 0);
v_value_446_ = lean_ctor_get(v_x_444_, 1);
v_tail_447_ = lean_ctor_get(v_x_444_, 2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_459_ == 0)
{
v___x_449_ = v_x_444_;
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_value_446_);
lean_inc(v_key_445_);
lean_dec(v_x_444_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_name_eq(v_key_445_, v_a_442_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_442_, v_b_443_, v_tail_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 2, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_key_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_value_446_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v_value_446_);
lean_dec(v_key_445_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_b_443_);
lean_ctor_set(v___x_449_, 0, v_a_442_);
v___x_457_ = v___x_449_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_442_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_b_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_tail_447_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
return v_x_460_;
}
else
{
lean_object* v_key_462_; lean_object* v_value_463_; lean_object* v_tail_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_490_; 
v_key_462_ = lean_ctor_get(v_x_461_, 0);
v_value_463_ = lean_ctor_get(v_x_461_, 1);
v_tail_464_ = lean_ctor_get(v_x_461_, 2);
v_isSharedCheck_490_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_490_ == 0)
{
v___x_466_ = v_x_461_;
v_isShared_467_ = v_isSharedCheck_490_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_tail_464_);
lean_inc(v_value_463_);
lean_inc(v_key_462_);
lean_dec(v_x_461_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_490_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; uint64_t v___y_470_; 
v___x_468_ = lean_array_get_size(v_x_460_);
if (lean_obj_tag(v_key_462_) == 0)
{
uint64_t v___x_488_; 
v___x_488_ = 1723ULL;
v___y_470_ = v___x_488_;
goto v___jp_469_;
}
else
{
uint64_t v_hash_489_; 
v_hash_489_ = lean_ctor_get_uint64(v_key_462_, sizeof(void*)*2);
v___y_470_ = v_hash_489_;
goto v___jp_469_;
}
v___jp_469_:
{
uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___y_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___y_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_468_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_x_460_, v___x_481_);
lean_inc(v___x_482_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 2, v___x_482_);
v___x_484_ = v___x_466_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_key_462_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_value_463_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_482_);
v___x_484_ = v_reuseFailAlloc_487_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; 
v___x_485_ = lean_array_uset(v_x_460_, v___x_481_, v___x_484_);
v_x_460_ = v___x_485_;
v_x_461_ = v_tail_464_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_491_, lean_object* v_source_492_, lean_object* v_target_493_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_array_get_size(v_source_492_);
v___x_495_ = lean_nat_dec_lt(v_i_491_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_source_492_);
lean_dec(v_i_491_);
return v_target_493_;
}
else
{
lean_object* v_es_496_; lean_object* v___x_497_; lean_object* v_source_498_; lean_object* v_target_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_es_496_ = lean_array_fget(v_source_492_, v_i_491_);
v___x_497_ = lean_box(0);
v_source_498_ = lean_array_fset(v_source_492_, v_i_491_, v___x_497_);
v_target_499_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_493_, v_es_496_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_i_491_, v___x_500_);
lean_dec(v_i_491_);
v_i_491_ = v___x_501_;
v_source_492_ = v_source_498_;
v_target_493_ = v_target_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_nbuckets_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_504_ = lean_array_get_size(v_data_503_);
v___x_505_ = lean_unsigned_to_nat(2u);
v_nbuckets_506_ = lean_nat_mul(v___x_504_, v___x_505_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_box(0);
v___x_509_ = lean_mk_array(v_nbuckets_506_, v___x_508_);
v___x_510_ = lean_array_propagate_mark(v_data_503_, v___x_509_);
v___x_511_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_507_, v_data_503_, v___x_510_);
return v___x_511_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
else
{
lean_object* v_key_515_; lean_object* v_tail_516_; uint8_t v___x_517_; 
v_key_515_ = lean_ctor_get(v_x_513_, 0);
v_tail_516_ = lean_ctor_get(v_x_513_, 2);
v___x_517_ = lean_name_eq(v_key_515_, v_a_512_);
if (v___x_517_ == 0)
{
v_x_513_ = v_tail_516_;
goto _start;
}
else
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_512_ = stack[0].m_obj;
lean_object* v_x_513_ = stack[1].m_obj;
uint8_t v_res_519_;
v_res_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_512_, v_x_513_);
stack->m_num = v_res_519_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec(v_a_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_524_, lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
lean_object* v_size_527_; lean_object* v_buckets_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_574_; 
v_size_527_ = lean_ctor_get(v_m_524_, 0);
v_buckets_528_ = lean_ctor_get(v_m_524_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_m_524_);
if (v_isSharedCheck_574_ == 0)
{
v___x_530_ = v_m_524_;
v_isShared_531_ = v_isSharedCheck_574_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_buckets_528_);
lean_inc(v_size_527_);
lean_dec(v_m_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_574_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; uint64_t v___y_534_; 
v___x_532_ = lean_array_get_size(v_buckets_528_);
if (lean_obj_tag(v_a_525_) == 0)
{
uint64_t v___x_572_; 
v___x_572_ = 1723ULL;
v___y_534_ = v___x_572_;
goto v___jp_533_;
}
else
{
uint64_t v_hash_573_; 
v_hash_573_ = lean_ctor_get_uint64(v_a_525_, sizeof(void*)*2);
v___y_534_ = v_hash_573_;
goto v___jp_533_;
}
v___jp_533_:
{
uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v_fold_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_bkt_546_; uint8_t v___x_547_; 
v___x_535_ = 32ULL;
v___x_536_ = lean_uint64_shift_right(v___y_534_, v___x_535_);
v_fold_537_ = lean_uint64_xor(v___y_534_, v___x_536_);
v___x_538_ = 16ULL;
v___x_539_ = lean_uint64_shift_right(v_fold_537_, v___x_538_);
v___x_540_ = lean_uint64_xor(v_fold_537_, v___x_539_);
v___x_541_ = lean_uint64_to_usize(v___x_540_);
v___x_542_ = lean_usize_of_nat(v___x_532_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_usize_land(v___x_541_, v___x_544_);
v_bkt_546_ = lean_array_uget_borrowed(v_buckets_528_, v___x_545_);
v___x_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_525_, v_bkt_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v_size_x27_549_; lean_object* v___x_550_; lean_object* v_buckets_x27_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v_size_x27_549_ = lean_nat_add(v_size_527_, v___x_548_);
lean_dec(v_size_527_);
lean_inc(v_bkt_546_);
v___x_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_550_, 0, v_a_525_);
lean_ctor_set(v___x_550_, 1, v_b_526_);
lean_ctor_set(v___x_550_, 2, v_bkt_546_);
v_buckets_x27_551_ = lean_array_uset(v_buckets_528_, v___x_545_, v___x_550_);
v___x_552_ = lean_unsigned_to_nat(4u);
v___x_553_ = lean_nat_mul(v_size_x27_549_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = lean_nat_div(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_array_get_size(v_buckets_x27_551_);
v___x_557_ = lean_nat_dec_le(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v_val_558_; lean_object* v___x_560_; 
v_val_558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_551_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_val_558_);
lean_ctor_set(v___x_530_, 0, v_size_x27_549_);
v___x_560_ = v___x_530_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_size_x27_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_val_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v___x_563_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_buckets_x27_551_);
lean_ctor_set(v___x_530_, 0, v_size_x27_549_);
v___x_563_ = v___x_530_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_size_x27_549_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_buckets_x27_551_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v___x_565_; lean_object* v_buckets_x27_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_inc(v_bkt_546_);
v___x_565_ = lean_box(0);
v_buckets_x27_566_ = lean_array_uset(v_buckets_528_, v___x_545_, v___x_565_);
v___x_567_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_525_, v_b_526_, v_bkt_546_);
v___x_568_ = lean_array_uset(v_buckets_x27_566_, v___x_545_, v___x_567_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___x_568_);
v___x_570_ = v___x_530_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_527_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_ks_579_; lean_object* v_vs_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_604_; 
v_ks_579_ = lean_ctor_get(v_x_575_, 0);
v_vs_580_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_604_ == 0)
{
v___x_582_ = v_x_575_;
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_vs_580_);
lean_inc(v_ks_579_);
lean_dec(v_x_575_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_array_get_size(v_ks_579_);
v___x_585_ = lean_nat_dec_lt(v_x_576_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec(v_x_576_);
v___x_586_ = lean_array_push(v_ks_579_, v_x_577_);
v___x_587_ = lean_array_push(v_vs_580_, v_x_578_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___x_587_);
lean_ctor_set(v___x_582_, 0, v___x_586_);
v___x_589_ = v___x_582_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v_k_x27_591_; uint8_t v___x_592_; 
v_k_x27_591_ = lean_array_fget_borrowed(v_ks_579_, v_x_576_);
v___x_592_ = lean_name_eq(v_x_577_, v_k_x27_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
if (v_isShared_583_ == 0)
{
v___x_594_ = v___x_582_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ks_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_vs_580_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_x_576_, v___x_595_);
lean_dec(v_x_576_);
v_x_575_ = v___x_594_;
v_x_576_ = v___x_596_;
goto _start;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = lean_array_fset(v_ks_579_, v_x_576_, v_x_577_);
v___x_600_ = lean_array_fset(v_vs_580_, v_x_576_, v_x_578_);
lean_dec(v_x_576_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___x_600_);
lean_ctor_set(v___x_582_, 0, v___x_599_);
v___x_602_ = v___x_582_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_605_, lean_object* v_k_606_, lean_object* v_v_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_605_, v___x_608_, v_k_606_, v_v_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_610_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_611_, size_t v_x_612_, size_t v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v_es_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_j_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_es_616_ = lean_ctor_get(v_x_611_, 0);
v___x_617_ = ((size_t)31ULL);
v___x_618_ = lean_usize_land(v_x_612_, v___x_617_);
v_j_619_ = lean_usize_to_nat(v___x_618_);
v___x_620_ = lean_array_get_size(v_es_616_);
v___x_621_ = lean_nat_dec_lt(v_j_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v_j_619_);
lean_dec(v_x_615_);
lean_dec(v_x_614_);
return v_x_611_;
}
else
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_660_; 
lean_inc_ref(v_es_616_);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_x_611_, 0);
lean_dec(v_unused_661_);
v___x_623_ = v_x_611_;
v_isShared_624_ = v_isSharedCheck_660_;
goto v_resetjp_622_;
}
else
{
lean_dec(v_x_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_660_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v_xs_x27_627_; lean_object* v___y_629_; 
v_v_625_ = lean_array_fget(v_es_616_, v_j_619_);
v___x_626_ = lean_box(0);
v_xs_x27_627_ = lean_array_fset(v_es_616_, v_j_619_, v___x_626_);
switch(lean_obj_tag(v_v_625_))
{
case 0:
{
lean_object* v_key_634_; lean_object* v_val_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
v_key_634_ = lean_ctor_get(v_v_625_, 0);
v_val_635_ = lean_ctor_get(v_v_625_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_v_625_);
if (v_isSharedCheck_645_ == 0)
{
v___x_637_ = v_v_625_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_val_635_);
lean_inc(v_key_634_);
lean_dec(v_v_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___x_639_; 
v___x_639_ = lean_name_eq(v_x_614_, v_key_634_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_del_object(v___x_637_);
v___x_640_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_634_, v_val_635_, v_x_614_, v_x_615_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
v___y_629_ = v___x_641_;
goto v___jp_628_;
}
else
{
lean_object* v___x_643_; 
lean_dec(v_val_635_);
lean_dec(v_key_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_615_);
lean_ctor_set(v___x_637_, 0, v_x_614_);
v___x_643_ = v___x_637_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_x_614_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_615_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
}
}
}
case 1:
{
lean_object* v_node_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
v_node_646_ = lean_ctor_get(v_v_625_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_v_625_);
if (v_isSharedCheck_658_ == 0)
{
v___x_648_ = v_v_625_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_node_646_);
lean_dec(v_v_625_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_650_ = ((size_t)5ULL);
v___x_651_ = lean_usize_shift_right(v_x_612_, v___x_650_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_add(v_x_613_, v___x_652_);
v___x_654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_646_, v___x_651_, v___x_653_, v_x_614_, v_x_615_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_654_);
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_629_ = v___x_656_;
goto v___jp_628_;
}
}
}
default: 
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_x_614_);
lean_ctor_set(v___x_659_, 1, v_x_615_);
v___y_629_ = v___x_659_;
goto v___jp_628_;
}
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_array_fset(v_xs_x27_627_, v_j_619_, v___y_629_);
lean_dec(v_j_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_630_);
v___x_632_ = v___x_623_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v_ks_662_; lean_object* v_vs_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_681_; 
v_ks_662_ = lean_ctor_get(v_x_611_, 0);
v_vs_663_ = lean_ctor_get(v_x_611_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_681_ == 0)
{
v___x_665_ = v_x_611_;
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_vs_663_);
lean_inc(v_ks_662_);
lean_dec(v_x_611_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_ks_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_vs_663_);
v___x_668_ = v_reuseFailAlloc_680_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v_newNode_669_; size_t v___x_670_; uint8_t v___x_671_; 
v_newNode_669_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_668_, v_x_614_, v_x_615_);
v___x_670_ = ((size_t)7ULL);
v___x_671_ = lean_usize_dec_le(v___x_670_, v_x_613_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_669_);
v___x_673_ = lean_unsigned_to_nat(4u);
v___x_674_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
if (v___x_674_ == 0)
{
lean_object* v_ks_675_; lean_object* v_vs_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_ks_675_ = lean_ctor_get(v_newNode_669_, 0);
lean_inc_ref(v_ks_675_);
v_vs_676_ = lean_ctor_get(v_newNode_669_, 1);
lean_inc_ref(v_vs_676_);
lean_dec_ref(v_newNode_669_);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_613_, v_ks_675_, v_vs_676_, v___x_677_, v___x_678_);
lean_dec_ref(v_vs_676_);
lean_dec_ref(v_ks_675_);
return v___x_679_;
}
else
{
return v_newNode_669_;
}
}
else
{
return v_newNode_669_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_611_ = stack[0].m_obj;
size_t v_x_612_ = stack[1].m_num;
size_t v_x_613_ = stack[2].m_num;
lean_object* v_x_614_ = stack[3].m_obj;
lean_object* v_x_615_ = stack[4].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_611_, v_x_612_, v_x_613_, v_x_614_, v_x_615_);
stack->m_obj
 = v_res_682_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_683_, lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_i_686_, lean_object* v_entries_687_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_array_get_size(v_keys_684_);
v___x_689_ = lean_nat_dec_lt(v_i_686_, v___x_688_);
if (v___x_689_ == 0)
{
lean_dec(v_i_686_);
return v_entries_687_;
}
else
{
lean_object* v_k_690_; lean_object* v_v_691_; uint64_t v___y_693_; 
v_k_690_ = lean_array_fget_borrowed(v_keys_684_, v_i_686_);
v_v_691_ = lean_array_fget_borrowed(v_vals_685_, v_i_686_);
if (lean_obj_tag(v_k_690_) == 0)
{
uint64_t v___x_704_; 
v___x_704_ = 1723ULL;
v___y_693_ = v___x_704_;
goto v___jp_692_;
}
else
{
uint64_t v_hash_705_; 
v_hash_705_ = lean_ctor_get_uint64(v_k_690_, sizeof(void*)*2);
v___y_693_ = v_hash_705_;
goto v___jp_692_;
}
v___jp_692_:
{
size_t v_h_694_; size_t v___x_695_; lean_object* v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v_h_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_h_694_ = lean_uint64_to_usize(v___y_693_);
v___x_695_ = ((size_t)5ULL);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_sub(v_depth_683_, v___x_697_);
v___x_699_ = lean_usize_mul(v___x_695_, v___x_698_);
v_h_700_ = lean_usize_shift_right(v_h_694_, v___x_699_);
v___x_701_ = lean_nat_add(v_i_686_, v___x_696_);
lean_dec(v_i_686_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v___x_702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_687_, v_h_700_, v_depth_683_, v_k_690_, v_v_691_);
v_i_686_ = v___x_701_;
v_entries_687_ = v___x_702_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_683_ = stack[0].m_num;
lean_object* v_keys_684_ = stack[1].m_obj;
lean_object* v_vals_685_ = stack[2].m_obj;
lean_object* v_i_686_ = stack[3].m_obj;
lean_object* v_entries_687_ = stack[4].m_obj;
lean_object* v_res_706_;
v_res_706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_683_, v_keys_684_, v_vals_685_, v_i_686_, v_entries_687_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_707_, lean_object* v_keys_708_, lean_object* v_vals_709_, lean_object* v_i_710_, lean_object* v_entries_711_){
_start:
{
size_t v_depth_boxed_712_; lean_object* v_res_713_; 
v_depth_boxed_712_ = lean_unbox_usize(v_depth_707_);
lean_dec(v_depth_707_);
v_res_713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_712_, v_keys_708_, v_vals_709_, v_i_710_, v_entries_711_);
lean_dec_ref(v_vals_709_);
lean_dec_ref(v_keys_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_1653__boxed_719_; size_t v_x_1654__boxed_720_; lean_object* v_res_721_; 
v_x_1653__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_1654__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_714_, v_x_1653__boxed_719_, v_x_1654__boxed_720_, v_x_717_, v_x_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
uint64_t v___y_726_; 
if (lean_obj_tag(v_x_723_) == 0)
{
uint64_t v___x_730_; 
v___x_730_ = 1723ULL;
v___y_726_ = v___x_730_;
goto v___jp_725_;
}
else
{
uint64_t v_hash_731_; 
v_hash_731_ = lean_ctor_get_uint64(v_x_723_, sizeof(void*)*2);
v___y_726_ = v_hash_731_;
goto v___jp_725_;
}
v___jp_725_:
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_uint64_to_usize(v___y_726_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_722_, v___x_727_, v___x_728_, v_x_723_, v_x_724_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
uint8_t v_stage_u2081_735_; 
v_stage_u2081_735_ = lean_ctor_get_uint8(v_x_732_, sizeof(void*)*2);
if (v_stage_u2081_735_ == 0)
{
lean_object* v_map_u2081_736_; lean_object* v_map_u2082_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_map_u2081_736_ = lean_ctor_get(v_x_732_, 0);
v_map_u2082_737_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v_x_732_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_map_u2082_737_);
lean_inc(v_map_u2081_736_);
lean_dec(v_x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_737_, v_x_733_, v_x_734_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_map_u2081_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*2, v_stage_u2081_735_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_map_u2081_746_; lean_object* v_map_u2082_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_map_u2081_746_ = lean_ctor_get(v_x_732_, 0);
v_map_u2082_747_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v_x_732_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_map_u2082_747_);
lean_inc(v_map_u2081_746_);
lean_dec(v_x_732_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_746_, v_x_733_, v_x_734_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_map_u2082_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*2, v_stage_u2081_735_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(32u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_759_ = ((size_t)5ULL);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_unsigned_to_nat(32u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_764_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_762_);
lean_ctor_set(v___x_764_, 2, v___x_760_);
lean_ctor_set(v___x_764_, 3, v___x_760_);
lean_ctor_set_usize(v___x_764_, 4, v___x_759_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_765_, lean_object* v_ns_766_, lean_object* v_b_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_765_, v_ns_766_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_770_ = l_Lean_PersistentArray_push___redArg(v___x_769_, v_b_767_);
v___x_771_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_765_, v_ns_766_, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_val_772_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_768_, 1);
v___x_773_ = l_Lean_PersistentArray_push___redArg(v_val_772_, v_b_767_);
v___x_774_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_765_, v_ns_766_, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_775_, lean_object* v_scopedEntries_776_, lean_object* v_ns_777_, lean_object* v_b_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_776_, v_ns_777_, v_b_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_784_, v_x_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec_ref(v_x_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_797_, v_x_798_, v_x_799_);
lean_dec(v_x_799_);
lean_dec_ref(v_x_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_801_, lean_object* v_m_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_802_, v_a_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_805_, v_m_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_m_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_810_, v_x_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_814_, lean_object* v_m_815_, lean_object* v_a_816_, lean_object* v_b_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_815_, v_a_816_, v_b_817_);
return v___x_818_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_819_, lean_object* v_x_820_, size_t v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_820_, v_x_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_820_ = stack[1].m_obj;
size_t v_x_821_ = stack[2].m_num;
lean_object* v_x_822_ = stack[3].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_box(0), v_x_820_, v_x_821_, v_x_822_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
size_t v_x_2110__boxed_829_; lean_object* v_res_830_; 
v_x_2110__boxed_829_ = lean_unbox_usize(v_x_827_);
lean_dec(v_x_827_);
v_res_830_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_825_, v_x_826_, v_x_2110__boxed_829_, v_x_828_);
lean_dec(v_x_828_);
lean_dec_ref(v_x_826_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_831_, lean_object* v_a_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_835_, lean_object* v_a_836_, lean_object* v_x_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_835_, v_a_836_, v_x_837_);
lean_dec(v_x_837_);
lean_dec(v_a_836_);
return v_res_838_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, size_t v_x_841_, size_t v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_840_, v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_840_ = stack[1].m_obj;
size_t v_x_841_ = stack[2].m_num;
size_t v_x_842_ = stack[3].m_num;
lean_object* v_x_843_ = stack[4].m_obj;
lean_object* v_x_844_ = stack[5].m_obj;
lean_object* v_res_846_;
v_res_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_box(0), v_x_840_, v_x_841_, v_x_842_, v_x_843_, v_x_844_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
size_t v_x_2136__boxed_853_; size_t v_x_2137__boxed_854_; lean_object* v_res_855_; 
v_x_2136__boxed_853_ = lean_unbox_usize(v_x_849_);
lean_dec(v_x_849_);
v_x_2137__boxed_854_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_res_855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_847_, v_x_848_, v_x_2136__boxed_853_, v_x_2137__boxed_854_, v_x_851_, v_x_852_);
return v_res_855_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_857_ = stack[1].m_obj;
lean_object* v_x_858_ = stack[2].m_obj;
uint8_t v_res_860_;
v_res_860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_box(0), v_a_857_, v_x_858_);
stack->m_num = v_res_860_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_861_, lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_861_, v_a_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_a_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_866_, lean_object* v_data_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_870_, v_b_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_heq_877_, lean_object* v_i_878_, lean_object* v_k_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_875_, v_vals_876_, v_i_878_, v_k_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_881_, lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_heq_884_, lean_object* v_i_885_, lean_object* v_k_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_881_, v_keys_882_, v_vals_883_, v_heq_884_, v_i_885_, v_k_886_);
lean_dec(v_k_886_);
lean_dec_ref(v_vals_883_);
lean_dec_ref(v_keys_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_888_, lean_object* v_n_889_, lean_object* v_k_890_, lean_object* v_v_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_889_, v_k_890_, v_v_891_);
return v___x_892_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_893_, size_t v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_entries_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_894_, v_keys_895_, v_vals_896_, v_i_898_, v_entries_899_);
return v___x_900_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_894_ = stack[1].m_num;
lean_object* v_keys_895_ = stack[2].m_obj;
lean_object* v_vals_896_ = stack[3].m_obj;
lean_object* v_i_898_ = stack[5].m_obj;
lean_object* v_entries_899_ = stack[6].m_obj;
lean_object* v_res_901_;
v_res_901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_box(0), v_depth_894_, v_keys_895_, v_vals_896_, lean_box(0), v_i_898_, v_entries_899_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_902_, lean_object* v_depth_903_, lean_object* v_keys_904_, lean_object* v_vals_905_, lean_object* v_heq_906_, lean_object* v_i_907_, lean_object* v_entries_908_){
_start:
{
size_t v_depth_boxed_909_; lean_object* v_res_910_; 
v_depth_boxed_909_ = lean_unbox_usize(v_depth_903_);
lean_dec(v_depth_903_);
v_res_910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_902_, v_depth_boxed_909_, v_keys_904_, v_vals_905_, v_heq_906_, v_i_907_, v_entries_908_);
lean_dec_ref(v_vals_905_);
lean_dec_ref(v_keys_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_911_, lean_object* v_i_912_, lean_object* v_source_913_, lean_object* v_target_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_912_, v_source_913_, v_target_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_917_, v_x_918_, v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_923_, v_x_924_);
return v___x_925_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_a_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v_descr_926_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_930_);
return v___x_939_;
}
else
{
lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_980_; 
v_fst_940_ = lean_ctor_get(v_b_930_, 0);
v_snd_941_ = lean_ctor_get(v_b_930_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_b_930_);
if (v_isSharedCheck_980_ == 0)
{
v___x_943_ = v_b_930_;
v_isShared_944_ = v_isSharedCheck_980_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v_b_930_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_980_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_a_945_; 
v_a_945_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_ofOLeanEntry_947_; lean_object* v_addEntry_948_; lean_object* v___x_949_; 
v_a_946_ = lean_ctor_get(v_a_945_, 0);
v_ofOLeanEntry_947_ = lean_ctor_get(v_descr_926_, 2);
v_addEntry_948_ = lean_ctor_get(v_descr_926_, 4);
lean_inc_ref(v_ofOLeanEntry_947_);
lean_inc_ref(v___y_931_);
lean_inc(v_a_946_);
lean_inc(v_fst_940_);
v___x_949_ = lean_apply_4(v_ofOLeanEntry_947_, v_fst_940_, v_a_946_, v___y_931_, lean_box(0));
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
lean_inc(v_addEntry_948_);
v___x_951_ = lean_apply_2(v_addEntry_948_, v_fst_940_, v_a_950_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_951_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_snd_941_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_934_ = v___x_953_;
goto v___jp_933_;
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_dec_ref(v_descr_926_);
v_a_955_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_949_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v_ofOLeanEntry_965_; lean_object* v___x_966_; 
v_a_963_ = lean_ctor_get(v_a_945_, 0);
v_a_964_ = lean_ctor_get(v_a_945_, 1);
v_ofOLeanEntry_965_ = lean_ctor_get(v_descr_926_, 2);
lean_inc_ref(v_ofOLeanEntry_965_);
lean_inc_ref(v___y_931_);
lean_inc(v_a_964_);
lean_inc(v_fst_940_);
v___x_966_ = lean_apply_4(v_ofOLeanEntry_965_, v_fst_940_, v_a_964_, v___y_931_, lean_box(0));
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
lean_inc(v_a_963_);
v___x_968_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_941_, v_a_963_, v_a_967_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_968_);
v___x_970_ = v___x_943_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_a_934_ = v___x_970_;
goto v___jp_933_;
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_dec_ref(v_descr_926_);
v_a_972_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_966_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_966_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_929_, v___x_935_);
v_i_929_ = v___x_936_;
v_b_930_ = v_a_934_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_926_ = stack[0].m_obj;
lean_object* v_as_927_ = stack[1].m_obj;
size_t v_sz_928_ = stack[2].m_num;
size_t v_i_929_ = stack[3].m_num;
lean_object* v_b_930_ = stack[4].m_obj;
lean_object* v___y_931_ = stack[5].m_obj;
lean_object* v_res_981_;
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_926_, v_as_927_, v_sz_928_, v_i_929_, v_b_930_, v___y_931_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_982_, lean_object* v_as_983_, lean_object* v_sz_984_, lean_object* v_i_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
size_t v_sz_boxed_989_; size_t v_i_boxed_990_; lean_object* v_res_991_; 
v_sz_boxed_989_ = lean_unbox_usize(v_sz_984_);
lean_dec(v_sz_984_);
v_i_boxed_990_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_res_991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_982_, v_as_983_, v_sz_boxed_989_, v_i_boxed_990_, v_b_986_, v___y_987_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v_as_983_);
return v_res_991_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_992_, lean_object* v_as_993_, size_t v_sz_994_, size_t v_i_995_, lean_object* v_b_996_, lean_object* v___y_997_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = lean_usize_dec_lt(v_i_995_, v_sz_994_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref(v_descr_992_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_b_996_);
return v___x_1000_;
}
else
{
lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1026_; 
v_fst_1001_ = lean_ctor_get(v_b_996_, 0);
v_snd_1002_ = lean_ctor_get(v_b_996_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_b_996_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1004_ = v_b_996_;
v_isShared_1005_ = v_isSharedCheck_1026_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_inc(v_fst_1001_);
lean_dec(v_b_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1026_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_a_1006_; lean_object* v___x_1008_; 
v_a_1006_ = lean_array_uget_borrowed(v_as_993_, v_i_995_);
if (v_isShared_1005_ == 0)
{
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_fst_1001_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1002_);
v___x_1008_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v_sz_1009_ = lean_array_size(v_a_1006_);
v___x_1010_ = ((size_t)0ULL);
lean_inc_ref(v_descr_992_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_992_, v_a_1006_, v_sz_1009_, v___x_1010_, v___x_1008_, v___y_997_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v_fst_1013_; lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1024_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v_fst_1013_ = lean_ctor_get(v_a_1012_, 0);
v_snd_1014_ = lean_ctor_get(v_a_1012_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1016_ = v_a_1012_;
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_inc(v_fst_1013_);
lean_dec(v_a_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_fst_1013_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_snd_1014_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
size_t v___x_1020_; size_t v___x_1021_; 
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_995_, v___x_1020_);
v_i_995_ = v___x_1021_;
v_b_996_ = v___x_1019_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_992_);
return v___x_1011_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_992_ = stack[0].m_obj;
lean_object* v_as_993_ = stack[1].m_obj;
size_t v_sz_994_ = stack[2].m_num;
size_t v_i_995_ = stack[3].m_num;
lean_object* v_b_996_ = stack[4].m_obj;
lean_object* v___y_997_ = stack[5].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_992_, v_as_993_, v_sz_994_, v_i_995_, v_b_996_, v___y_997_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_1028_, lean_object* v_as_1029_, lean_object* v_sz_1030_, lean_object* v_i_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1030_);
lean_dec(v_sz_1030_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1028_, v_as_1029_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1032_, v___y_1033_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_as_1029_);
return v_res_1037_;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_1038_, lean_object* v_as_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_mkInitial_1042_; lean_object* v_finalizeImport_1043_; lean_object* v___x_1044_; 
v_mkInitial_1042_ = lean_ctor_get(v_descr_1038_, 1);
v_finalizeImport_1043_ = lean_ctor_get(v_descr_1038_, 5);
lean_inc(v_finalizeImport_1043_);
lean_inc_ref(v_mkInitial_1042_);
v___x_1044_ = lean_apply_1(v_mkInitial_1042_, lean_box(0));
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = 1;
v___x_1047_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1045_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v_sz_1049_ = lean_array_size(v_as_1039_);
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1038_, v_as_1039_, v_sz_1049_, v___x_1050_, v___x_1048_, v_a_1040_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1075_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1075_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1075_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1074_; 
v_fst_1056_ = lean_ctor_get(v_a_1052_, 0);
v_snd_1057_ = lean_ctor_get(v_a_1052_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1059_ = v_a_1052_;
v_isShared_1060_ = v_isSharedCheck_1074_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snd_1057_);
lean_inc(v_fst_1056_);
lean_dec(v_a_1052_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1074_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1061_ = lean_apply_1(v_finalizeImport_1043_, v_fst_1056_);
v___x_1062_ = l_Lean_NameSet_empty;
v___x_1063_ = 0;
v___x_1064_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1065_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1065_, 0, v___x_1061_);
lean_ctor_set(v___x_1065_, 1, v___x_1062_);
lean_ctor_set(v___x_1065_, 2, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*3, v___x_1046_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*3 + 1, v___x_1063_);
v___x_1066_ = lean_box(0);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 1);
lean_ctor_set(v___x_1059_, 1, v___x_1066_);
lean_ctor_set(v___x_1059_, 0, v___x_1065_);
v___x_1068_ = v___x_1059_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_snd_1057_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1069_);
v___x_1071_ = v___x_1054_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_finalizeImport_1043_);
v_a_1076_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1051_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1051_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_finalizeImport_1043_);
lean_dec_ref(v_descr_1038_);
v_a_1084_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1044_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1044_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_addImportedFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1038_ = stack[0].m_obj;
lean_object* v_as_1039_ = stack[1].m_obj;
lean_object* v_a_1040_ = stack[2].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1038_, v_as_1039_, v_a_1040_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1093_, lean_object* v_as_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1093_, v_as_1094_, v_a_1095_);
lean_dec_ref(v_a_1095_);
lean_dec_ref(v_as_1094_);
return v_res_1097_;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_00_u03c3_1100_, lean_object* v_descr_1101_, lean_object* v_as_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1101_, v_as_1102_, v_a_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_addImportedFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1101_ = stack[3].m_obj;
lean_object* v_as_1102_ = stack[4].m_obj;
lean_object* v_a_1103_ = stack[5].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l_Lean_ScopedEnvExtension_addImportedFn(lean_box(0), lean_box(0), lean_box(0), v_descr_1101_, v_as_1102_, v_a_1103_);
stack->m_obj
 = v_res_1106_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_00_u03c3_1109_, lean_object* v_descr_1110_, lean_object* v_as_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1107_, v_00_u03b2_1108_, v_00_u03c3_1109_, v_descr_1110_, v_as_1111_, v_a_1112_);
lean_dec_ref(v_a_1112_);
lean_dec_ref(v_as_1111_);
return v_res_1114_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03c3_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_descr_1118_, lean_object* v_as_1119_, size_t v_sz_1120_, size_t v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1118_, v_as_1119_, v_sz_1120_, v_i_1121_, v_b_1122_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1118_ = stack[3].m_obj;
lean_object* v_as_1119_ = stack[4].m_obj;
size_t v_sz_1120_ = stack[5].m_num;
size_t v_i_1121_ = stack[6].m_num;
lean_object* v_b_1122_ = stack[7].m_obj;
lean_object* v___y_1123_ = stack[8].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_box(0), lean_box(0), lean_box(0), v_descr_1118_, v_as_1119_, v_sz_1120_, v_i_1121_, v_b_1122_, v___y_1123_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03c3_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_descr_1130_, lean_object* v_as_1131_, lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1127_, v_00_u03c3_1128_, v_00_u03b2_1129_, v_descr_1130_, v_as_1131_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1134_, v___y_1135_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_as_1131_);
return v_res_1139_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03c3_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_descr_1143_, lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1143_, v_as_1144_, v_sz_1145_, v_i_1146_, v_b_1147_, v___y_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1143_ = stack[3].m_obj;
lean_object* v_as_1144_ = stack[4].m_obj;
size_t v_sz_1145_ = stack[5].m_num;
size_t v_i_1146_ = stack[6].m_num;
lean_object* v_b_1147_ = stack[7].m_obj;
lean_object* v___y_1148_ = stack[8].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_box(0), lean_box(0), lean_box(0), v_descr_1143_, v_as_1144_, v_sz_1145_, v_i_1146_, v_b_1147_, v___y_1148_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03c3_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_descr_1155_, lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1152_, v_00_u03c3_1153_, v_00_u03b2_1154_, v_descr_1155_, v_as_1156_, v_sz_boxed_1162_, v_i_boxed_1163_, v_b_1159_, v___y_1160_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_as_1156_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1165_, lean_object* v_descr_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
if (lean_obj_tag(v_a_1168_) == 0)
{
lean_object* v___x_1170_; 
lean_dec(v_a_1167_);
lean_dec_ref(v_descr_1166_);
v___x_1170_ = l_List_reverse___redArg(v_a_1169_);
return v___x_1170_;
}
else
{
lean_object* v_head_1171_; lean_object* v_tail_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1201_; 
v_head_1171_ = lean_ctor_get(v_a_1168_, 0);
v_tail_1172_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1174_ = v_a_1168_;
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_tail_1172_);
lean_inc(v_head_1171_);
lean_dec(v_a_1168_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1201_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___y_1177_; lean_object* v_state_1182_; lean_object* v_activeScopes_1183_; uint8_t v_delimitsLocal_1184_; uint8_t v_scopeChanged_1185_; lean_object* v_scopeChangedDecls_1186_; uint8_t v___x_1187_; 
v_state_1182_ = lean_ctor_get(v_head_1171_, 0);
v_activeScopes_1183_ = lean_ctor_get(v_head_1171_, 1);
v_delimitsLocal_1184_ = lean_ctor_get_uint8(v_head_1171_, sizeof(void*)*3);
v_scopeChanged_1185_ = lean_ctor_get_uint8(v_head_1171_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1186_ = lean_ctor_get(v_head_1171_, 2);
v___x_1187_ = l_Lean_NameSet_contains(v_activeScopes_1183_, v_a_1165_);
if (v___x_1187_ == 0)
{
v___y_1177_ = v_head_1171_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1197_; 
lean_inc_ref(v_scopeChangedDecls_1186_);
lean_inc(v_activeScopes_1183_);
lean_inc(v_state_1182_);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_head_1171_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1198_ = lean_ctor_get(v_head_1171_, 2);
lean_dec(v_unused_1198_);
v_unused_1199_ = lean_ctor_get(v_head_1171_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_head_1171_, 0);
lean_dec(v_unused_1200_);
v___x_1189_ = v_head_1171_;
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v_head_1171_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1197_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_addEntry_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_addEntry_1191_ = lean_ctor_get(v_descr_1166_, 4);
lean_inc(v_addEntry_1191_);
lean_inc(v_a_1167_);
v___x_1192_ = lean_apply_2(v_addEntry_1191_, v_state_1182_, v_a_1167_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_activeScopes_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_scopeChangedDecls_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3, v_delimitsLocal_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 1, v_scopeChanged_1185_);
v___x_1194_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
lean_inc(v_a_1167_);
lean_inc_ref(v_descr_1166_);
v___x_1195_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1166_, v___x_1194_, v_a_1167_);
v___y_1177_ = v___x_1195_;
goto v___jp_1176_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_a_1169_);
lean_ctor_set(v___x_1174_, 0, v___y_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___y_1177_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_a_1169_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
v_a_1168_ = v_tail_1172_;
v_a_1169_ = v___x_1179_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1202_, lean_object* v_descr_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1202_, v_descr_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_object* v___x_1212_; 
lean_dec(v_a_1209_);
lean_dec_ref(v_descr_1208_);
v___x_1212_ = l_List_reverse___redArg(v_a_1211_);
return v___x_1212_;
}
else
{
lean_object* v_head_1213_; lean_object* v_tail_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1236_; 
v_head_1213_ = lean_ctor_get(v_a_1210_, 0);
v_tail_1214_ = lean_ctor_get(v_a_1210_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1216_ = v_a_1210_;
v_isShared_1217_ = v_isSharedCheck_1236_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_tail_1214_);
lean_inc(v_head_1213_);
lean_dec(v_a_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1236_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_addEntry_1218_; lean_object* v_state_1219_; lean_object* v_activeScopes_1220_; uint8_t v_delimitsLocal_1221_; uint8_t v_scopeChanged_1222_; lean_object* v_scopeChangedDecls_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1235_; 
v_addEntry_1218_ = lean_ctor_get(v_descr_1208_, 4);
v_state_1219_ = lean_ctor_get(v_head_1213_, 0);
v_activeScopes_1220_ = lean_ctor_get(v_head_1213_, 1);
v_delimitsLocal_1221_ = lean_ctor_get_uint8(v_head_1213_, sizeof(void*)*3);
v_scopeChanged_1222_ = lean_ctor_get_uint8(v_head_1213_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1223_ = lean_ctor_get(v_head_1213_, 2);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_head_1213_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1225_ = v_head_1213_;
v_isShared_1226_ = v_isSharedCheck_1235_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_scopeChangedDecls_1223_);
lean_inc(v_activeScopes_1220_);
lean_inc(v_state_1219_);
lean_dec(v_head_1213_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1235_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_inc(v_addEntry_1218_);
lean_inc(v_a_1209_);
v___x_1227_ = lean_apply_2(v_addEntry_1218_, v_state_1219_, v_a_1209_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_activeScopes_1220_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_scopeChangedDecls_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3, v_delimitsLocal_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*3 + 1, v_scopeChanged_1222_);
v___x_1229_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_a_1211_);
lean_ctor_set(v___x_1216_, 0, v___x_1229_);
v___x_1231_ = v___x_1216_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_a_1211_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
v_a_1210_ = v_tail_1214_;
v_a_1211_ = v___x_1231_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1237_, lean_object* v_s_1238_, lean_object* v_e_1239_){
_start:
{
if (lean_obj_tag(v_e_1239_) == 0)
{
lean_object* v_stateStack_1240_; lean_object* v_scopedEntries_1241_; lean_object* v_newEntries_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1262_; 
v_stateStack_1240_ = lean_ctor_get(v_s_1238_, 0);
v_scopedEntries_1241_ = lean_ctor_get(v_s_1238_, 1);
v_newEntries_1242_ = lean_ctor_get(v_s_1238_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_s_1238_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1244_ = v_s_1238_;
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_newEntries_1242_);
lean_inc(v_scopedEntries_1241_);
lean_inc(v_stateStack_1240_);
lean_dec(v_s_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1261_; 
v_a_1246_ = lean_ctor_get(v_e_1239_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_e_1239_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1248_ = v_e_1239_;
v_isShared_1249_ = v_isSharedCheck_1261_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v_e_1239_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1261_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_toOLeanEntry_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v_toOLeanEntry_1250_ = lean_ctor_get(v_descr_1237_, 3);
lean_inc(v_toOLeanEntry_1250_);
v___x_1251_ = lean_box(0);
lean_inc(v_a_1246_);
v___x_1252_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1237_, v_a_1246_, v_stateStack_1240_, v___x_1251_);
v___x_1253_ = lean_apply_1(v_toOLeanEntry_1250_, v_a_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1253_);
v___x_1255_ = v___x_1248_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_newEntries_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 2, v___x_1256_);
lean_ctor_set(v___x_1244_, 0, v___x_1252_);
v___x_1258_ = v___x_1244_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_scopedEntries_1241_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1263_; lean_object* v_scopedEntries_1264_; lean_object* v_newEntries_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1287_; 
v_stateStack_1263_ = lean_ctor_get(v_s_1238_, 0);
v_scopedEntries_1264_ = lean_ctor_get(v_s_1238_, 1);
v_newEntries_1265_ = lean_ctor_get(v_s_1238_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_s_1238_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1267_ = v_s_1238_;
v_isShared_1268_ = v_isSharedCheck_1287_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_newEntries_1265_);
lean_inc(v_scopedEntries_1264_);
lean_inc(v_stateStack_1263_);
lean_dec(v_s_1238_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1287_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_a_1269_; lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1286_; 
v_a_1269_ = lean_ctor_get(v_e_1239_, 0);
v_a_1270_ = lean_ctor_get(v_e_1239_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_e_1239_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1272_ = v_e_1239_;
v_isShared_1273_ = v_isSharedCheck_1286_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_inc(v_a_1269_);
lean_dec(v_e_1239_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1286_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_toOLeanEntry_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v_toOLeanEntry_1274_ = lean_ctor_get(v_descr_1237_, 3);
lean_inc(v_toOLeanEntry_1274_);
v___x_1275_ = lean_box(0);
lean_inc_n(v_a_1270_, 2);
v___x_1276_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1269_, v_descr_1237_, v_a_1270_, v_stateStack_1263_, v___x_1275_);
lean_inc(v_a_1269_);
v___x_1277_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1264_, v_a_1269_, v_a_1270_);
v___x_1278_ = lean_apply_1(v_toOLeanEntry_1274_, v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1278_);
v___x_1280_ = v___x_1272_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1269_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_newEntries_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1281_);
lean_ctor_set(v___x_1267_, 1, v___x_1277_);
lean_ctor_set(v___x_1267_, 0, v___x_1276_);
v___x_1283_ = v___x_1267_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1288_, lean_object* v_00_u03b2_1289_, lean_object* v_00_u03c3_1290_, lean_object* v_descr_1291_, lean_object* v_s_1292_, lean_object* v_e_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1291_, v_s_1292_, v_e_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_00_u03b1_1297_, lean_object* v_descr_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1303_, lean_object* v_a_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_00_u03b1_1306_, lean_object* v_descr_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1304_, v_descr_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1312_, lean_object* v_a_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_00_u03b1_1315_, lean_object* v_descr_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1312_, v_a_1313_, v_00_u03b2_1314_, v_00_u03b1_1315_, v_descr_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1313_);
return v_res_1320_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1321_, lean_object* v_env_1322_, lean_object* v_as_1323_, size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_b_1326_){
_start:
{
lean_object* v_a_1328_; uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_lt(v_i_1325_, v_sz_1324_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_env_1322_);
lean_dec_ref(v_descr_1321_);
return v_b_1326_;
}
else
{
lean_object* v_snd_1333_; lean_object* v_fst_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1434_; 
v_snd_1333_ = lean_ctor_get(v_b_1326_, 1);
v_fst_1334_ = lean_ctor_get(v_b_1326_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_b_1326_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1336_ = v_b_1326_;
v_isShared_1337_ = v_isSharedCheck_1434_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1333_);
lean_inc(v_fst_1334_);
lean_dec(v_b_1326_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1434_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1433_; 
v_fst_1338_ = lean_ctor_get(v_snd_1333_, 0);
v_snd_1339_ = lean_ctor_get(v_snd_1333_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_snd_1333_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1341_ = v_snd_1333_;
v_isShared_1342_ = v_isSharedCheck_1433_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_inc(v_fst_1338_);
lean_dec(v_snd_1333_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1433_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_a_1343_; 
v_a_1343_ = lean_array_uget(v_as_1323_, v_i_1325_);
if (lean_obj_tag(v_a_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1393_; 
v_a_1344_ = lean_ctor_get(v_a_1343_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_a_1343_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1346_ = v_a_1343_;
v_isShared_1347_ = v_isSharedCheck_1393_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v_a_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1393_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_exportEntry_x3f_1348_; lean_object* v___x_1349_; lean_object* v_exported_1350_; lean_object* v_server_1351_; lean_object* v_private_1352_; lean_object* v___y_1354_; lean_object* v_server_1355_; lean_object* v_exported_1374_; 
v_exportEntry_x3f_1348_ = lean_ctor_get(v_descr_1321_, 6);
lean_inc_ref(v_exportEntry_x3f_1348_);
lean_inc_ref(v_env_1322_);
v___x_1349_ = lean_apply_2(v_exportEntry_x3f_1348_, v_env_1322_, v_a_1344_);
v_exported_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_exported_1350_);
v_server_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_server_1351_);
v_private_1352_ = lean_ctor_get(v___x_1349_, 2);
lean_inc(v_private_1352_);
lean_dec_ref(v___x_1349_);
if (lean_obj_tag(v_exported_1350_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
v_val_1384_ = lean_ctor_get(v_exported_1350_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_exported_1350_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1386_ = v_exported_1350_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v_exported_1350_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 0);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_array_push(v_fst_1334_, v___x_1389_);
v_exported_1374_ = v___x_1390_;
goto v___jp_1373_;
}
}
}
else
{
lean_dec(v_exported_1350_);
v_exported_1374_ = v_fst_1334_;
goto v___jp_1373_;
}
v___jp_1353_:
{
if (lean_obj_tag(v_private_1352_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1358_; 
v_val_1356_ = lean_ctor_get(v_private_1352_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v_private_1352_, 1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_val_1356_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_val_1356_);
v___x_1358_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_array_push(v_snd_1339_, v___x_1358_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1359_);
lean_ctor_set(v___x_1341_, 0, v_server_1355_);
v___x_1361_ = v___x_1341_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_server_1355_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1361_);
lean_ctor_set(v___x_1336_, 0, v___y_1354_);
v___x_1363_ = v___x_1336_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___y_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_a_1328_ = v___x_1363_;
goto v___jp_1327_;
}
}
}
}
else
{
lean_object* v___x_1368_; 
lean_dec(v_private_1352_);
lean_del_object(v___x_1346_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_server_1355_);
v___x_1368_ = v___x_1341_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_server_1355_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1339_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1368_);
lean_ctor_set(v___x_1336_, 0, v___y_1354_);
v___x_1370_ = v___x_1336_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___y_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v_a_1328_ = v___x_1370_;
goto v___jp_1327_;
}
}
}
}
v___jp_1373_:
{
if (lean_obj_tag(v_server_1351_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1383_; 
v_val_1375_ = lean_ctor_get(v_server_1351_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_server_1351_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1377_ = v_server_1351_;
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_val_1375_);
lean_dec(v_server_1351_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 0);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_val_1375_);
v___x_1380_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_array_push(v_fst_1338_, v___x_1380_);
v___y_1354_ = v_exported_1374_;
v_server_1355_ = v___x_1381_;
goto v___jp_1353_;
}
}
}
else
{
lean_dec(v_server_1351_);
v___y_1354_ = v_exported_1374_;
v_server_1355_ = v_fst_1338_;
goto v___jp_1353_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1432_; 
v_a_1394_ = lean_ctor_get(v_a_1343_, 0);
v_a_1395_ = lean_ctor_get(v_a_1343_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1343_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1397_ = v_a_1343_;
v_isShared_1398_ = v_isSharedCheck_1432_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_inc(v_a_1394_);
lean_dec(v_a_1343_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1432_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_exportEntry_x3f_1399_; lean_object* v___x_1400_; lean_object* v_exported_1401_; lean_object* v_server_1402_; lean_object* v_private_1403_; lean_object* v___y_1405_; lean_object* v_server_1406_; lean_object* v_exported_1425_; 
v_exportEntry_x3f_1399_ = lean_ctor_get(v_descr_1321_, 6);
lean_inc_ref(v_exportEntry_x3f_1399_);
lean_inc_ref(v_env_1322_);
v___x_1400_ = lean_apply_2(v_exportEntry_x3f_1399_, v_env_1322_, v_a_1395_);
v_exported_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_exported_1401_);
v_server_1402_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_server_1402_);
v_private_1403_ = lean_ctor_get(v___x_1400_, 2);
lean_inc(v_private_1403_);
lean_dec_ref(v___x_1400_);
if (lean_obj_tag(v_exported_1401_) == 1)
{
lean_object* v_val_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_val_1429_ = lean_ctor_get(v_exported_1401_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v_exported_1401_, 1);
lean_inc(v_a_1394_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1394_);
lean_ctor_set(v___x_1430_, 1, v_val_1429_);
v___x_1431_ = lean_array_push(v_fst_1334_, v___x_1430_);
v_exported_1425_ = v___x_1431_;
goto v___jp_1424_;
}
else
{
lean_dec(v_exported_1401_);
v_exported_1425_ = v_fst_1334_;
goto v___jp_1424_;
}
v___jp_1404_:
{
if (lean_obj_tag(v_private_1403_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1409_; 
v_val_1407_ = lean_ctor_get(v_private_1403_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v_private_1403_, 1);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v_val_1407_);
v___x_1409_ = v___x_1397_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1394_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_val_1407_);
v___x_1409_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_array_push(v_snd_1339_, v___x_1409_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1410_);
lean_ctor_set(v___x_1341_, 0, v_server_1406_);
v___x_1412_ = v___x_1341_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_server_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1412_);
lean_ctor_set(v___x_1336_, 0, v___y_1405_);
v___x_1414_ = v___x_1336_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___y_1405_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
v_a_1328_ = v___x_1414_;
goto v___jp_1327_;
}
}
}
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_private_1403_);
lean_del_object(v___x_1397_);
lean_dec(v_a_1394_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_server_1406_);
v___x_1419_ = v___x_1341_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_server_1406_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_snd_1339_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1419_);
lean_ctor_set(v___x_1336_, 0, v___y_1405_);
v___x_1421_ = v___x_1336_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___y_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
v_a_1328_ = v___x_1421_;
goto v___jp_1327_;
}
}
}
}
v___jp_1424_:
{
if (lean_obj_tag(v_server_1402_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_val_1426_ = lean_ctor_get(v_server_1402_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v_server_1402_, 1);
lean_inc(v_a_1394_);
v___x_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_a_1394_);
lean_ctor_set(v___x_1427_, 1, v_val_1426_);
v___x_1428_ = lean_array_push(v_fst_1338_, v___x_1427_);
v___y_1405_ = v_exported_1425_;
v_server_1406_ = v___x_1428_;
goto v___jp_1404_;
}
else
{
lean_dec(v_server_1402_);
v___y_1405_ = v_exported_1425_;
v_server_1406_ = v_fst_1338_;
goto v___jp_1404_;
}
}
}
}
}
}
}
v___jp_1327_:
{
size_t v___x_1329_; size_t v___x_1330_; 
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1325_, v___x_1329_);
v_i_1325_ = v___x_1330_;
v_b_1326_ = v_a_1328_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1321_ = stack[0].m_obj;
lean_object* v_env_1322_ = stack[1].m_obj;
lean_object* v_as_1323_ = stack[2].m_obj;
size_t v_sz_1324_ = stack[3].m_num;
size_t v_i_1325_ = stack[4].m_num;
lean_object* v_b_1326_ = stack[5].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1321_, v_env_1322_, v_as_1323_, v_sz_1324_, v_i_1325_, v_b_1326_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1436_, lean_object* v_env_1437_, lean_object* v_as_1438_, lean_object* v_sz_1439_, lean_object* v_i_1440_, lean_object* v_b_1441_){
_start:
{
size_t v_sz_boxed_1442_; size_t v_i_boxed_1443_; lean_object* v_res_1444_; 
v_sz_boxed_1442_ = lean_unbox_usize(v_sz_1439_);
lean_dec(v_sz_1439_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1436_, v_env_1437_, v_as_1438_, v_sz_boxed_1442_, v_i_boxed_1443_, v_b_1441_);
lean_dec_ref(v_as_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1452_, lean_object* v_env_1453_, lean_object* v_s_1454_){
_start:
{
lean_object* v_newEntries_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1472_; 
v_newEntries_1455_ = lean_ctor_get(v_s_1454_, 2);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_s_1454_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; lean_object* v_unused_1474_; 
v_unused_1473_ = lean_ctor_get(v_s_1454_, 1);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_s_1454_, 0);
lean_dec(v_unused_1474_);
v___x_1457_ = v_s_1454_;
v_isShared_1458_ = v_isSharedCheck_1472_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_newEntries_1455_);
lean_dec(v_s_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1472_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_1464_; lean_object* v_snd_1465_; lean_object* v_fst_1466_; lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1470_; 
v___x_1459_ = lean_array_mk(v_newEntries_1455_);
v___x_1460_ = l_Array_reverse___redArg(v___x_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1462_ = lean_array_size(v___x_1460_);
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1452_, v_env_1453_, v___x_1460_, v_sz_1462_, v___x_1463_, v___x_1461_);
lean_dec_ref(v___x_1460_);
v_snd_1465_ = lean_ctor_get(v___x_1464_, 1);
lean_inc(v_snd_1465_);
v_fst_1466_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_fst_1466_);
lean_dec_ref(v___x_1464_);
v_fst_1467_ = lean_ctor_get(v_snd_1465_, 0);
lean_inc(v_fst_1467_);
v_snd_1468_ = lean_ctor_get(v_snd_1465_, 1);
lean_inc(v_snd_1468_);
lean_dec(v_snd_1465_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 2, v_snd_1468_);
lean_ctor_set(v___x_1457_, 1, v_fst_1467_);
lean_ctor_set(v___x_1457_, 0, v_fst_1466_);
v___x_1470_ = v___x_1457_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_fst_1466_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_fst_1467_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_snd_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1475_, lean_object* v_00_u03b2_1476_, lean_object* v_00_u03c3_1477_, lean_object* v_descr_1478_, lean_object* v_env_1479_, lean_object* v_s_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1478_, v_env_1479_, v_s_1480_);
return v___x_1481_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_00_u03c3_1484_, lean_object* v_descr_1485_, lean_object* v_env_1486_, lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1485_, v_env_1486_, v_as_1487_, v_sz_1488_, v_i_1489_, v_b_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1485_ = stack[3].m_obj;
lean_object* v_env_1486_ = stack[4].m_obj;
lean_object* v_as_1487_ = stack[5].m_obj;
size_t v_sz_1488_ = stack[6].m_num;
size_t v_i_1489_ = stack[7].m_num;
lean_object* v_b_1490_ = stack[8].m_obj;
lean_object* v_res_1492_;
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_box(0), lean_box(0), lean_box(0), v_descr_1485_, v_env_1486_, v_as_1487_, v_sz_1488_, v_i_1489_, v_b_1490_);
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_00_u03c3_1495_, lean_object* v_descr_1496_, lean_object* v_env_1497_, lean_object* v_as_1498_, lean_object* v_sz_1499_, lean_object* v_i_1500_, lean_object* v_b_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1499_);
lean_dec(v_sz_1499_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1493_, v_00_u03b2_1494_, v_00_u03c3_1495_, v_descr_1496_, v_env_1497_, v_as_1498_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1501_);
lean_dec_ref(v_as_1498_);
return v_res_1504_;
}
}
lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1505_ = stack[0].m_obj;
lean_object* v___y_1506_ = stack[1].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1505_, v___y_1506_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1511_, v___y_1512_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v_x_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1515_, lean_object* v_x_1516_){
_start:
{
lean_inc_ref(v_s_1515_);
return v_s_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1517_, v_x_1518_);
lean_dec_ref(v_x_1518_);
lean_dec_ref(v_s_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1525_, v_x_1526_);
lean_dec_ref(v_x_1526_);
lean_dec_ref(v_x_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1530_);
lean_dec_ref(v_x_1530_);
return v_res_1531_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1537_; lean_object* v___f_1538_; lean_object* v___f_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___f_1537_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1538_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1539_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1540_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1543_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1541_);
lean_ctor_set(v___x_1543_, 2, v___f_1540_);
lean_ctor_set(v___x_1543_, 3, v___f_1539_);
lean_ctor_set(v___x_1543_, 4, v___f_1538_);
lean_ctor_set(v___x_1543_, 5, v___f_1537_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1544_){
_start:
{
lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___f_1545_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1546_, 0, v_inst_1544_);
v___f_1547_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1548_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1551_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1552_ = 0;
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1554_, 0, v___x_1549_);
lean_ctor_set(v___x_1554_, 1, v___x_1550_);
lean_ctor_set(v___x_1554_, 2, v___f_1545_);
lean_ctor_set(v___x_1554_, 3, v___f_1546_);
lean_ctor_set(v___x_1554_, 4, v___f_1547_);
lean_ctor_set(v___x_1554_, 5, v___x_1551_);
lean_ctor_set(v___x_1554_, 6, v___f_1548_);
lean_ctor_set(v___x_1554_, 7, v___x_1553_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*8, v___x_1552_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*8 + 1, v___x_1552_);
v___x_1555_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_00_u03c3_1559_, lean_object* v_inst_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1564_, lean_object* v_inst_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1565_);
return v___x_1568_;
}
}
lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1573_ = lean_st_mk_ref(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT void l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1575_;
v_res_1575_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_x_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_x_1580_);
lean_dec_ref(v_x_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1585_){
_start:
{
lean_object* v_newEntries_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_newEntries_1586_ = lean_ctor_get(v_s_1585_, 2);
v___x_1587_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1588_ = l_List_lengthTR___redArg(v_newEntries_1586_);
v___x_1589_ = l_Nat_reprFast(v___x_1588_);
v___x_1590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1587_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1592_);
lean_dec_ref(v_s_1592_);
return v_res_1593_;
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1598_){
_start:
{
lean_object* v_name_1600_; uint8_t v_trackGen_1601_; uint8_t v_logWrites_1602_; lean_object* v_entryDecl_x3f_1603_; lean_object* v___f_1604_; lean_object* v___f_1605_; 
v_name_1600_ = lean_ctor_get(v_descr_1598_, 0);
v_trackGen_1601_ = lean_ctor_get_uint8(v_descr_1598_, sizeof(void*)*8);
v_logWrites_1602_ = lean_ctor_get_uint8(v_descr_1598_, sizeof(void*)*8 + 1);
v_entryDecl_x3f_1603_ = lean_ctor_get(v_descr_1598_, 7);
v___f_1604_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1605_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
if (v_logWrites_1602_ == 0)
{
goto v___jp_1606_;
}
else
{
if (lean_obj_tag(v_entryDecl_x3f_1603_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_inc(v_name_1600_);
lean_dec_ref(v_descr_1598_);
v___x_1637_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2));
v___x_1638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1600_, v_logWrites_1602_);
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
lean_dec_ref(v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3));
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_mk_io_user_error(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
else
{
goto v___jp_1606_;
}
}
v___jp_1606_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_inc_ref_n(v_descr_1598_, 4);
v___x_1607_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1607_, 0, lean_box(0));
lean_closure_set(v___x_1607_, 1, lean_box(0));
lean_closure_set(v___x_1607_, 2, lean_box(0));
lean_closure_set(v___x_1607_, 3, v_descr_1598_);
v___x_1608_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1608_, 0, lean_box(0));
lean_closure_set(v___x_1608_, 1, lean_box(0));
lean_closure_set(v___x_1608_, 2, lean_box(0));
lean_closure_set(v___x_1608_, 3, v_descr_1598_);
v___x_1609_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1609_, 0, lean_box(0));
lean_closure_set(v___x_1609_, 1, lean_box(0));
lean_closure_set(v___x_1609_, 2, lean_box(0));
lean_closure_set(v___x_1609_, 3, v_descr_1598_);
v___x_1610_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1610_, 0, lean_box(0));
lean_closure_set(v___x_1610_, 1, lean_box(0));
lean_closure_set(v___x_1610_, 2, lean_box(0));
lean_closure_set(v___x_1610_, 3, v_descr_1598_);
v___x_1611_ = lean_box(2);
v___x_1612_ = lean_box(0);
lean_inc(v_name_1600_);
v___x_1613_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1613_, 0, v_name_1600_);
lean_ctor_set(v___x_1613_, 1, v___x_1607_);
lean_ctor_set(v___x_1613_, 2, v___x_1608_);
lean_ctor_set(v___x_1613_, 3, v___x_1609_);
lean_ctor_set(v___x_1613_, 4, v___x_1610_);
lean_ctor_set(v___x_1613_, 5, v___f_1605_);
lean_ctor_set(v___x_1613_, 6, v___x_1611_);
lean_ctor_set(v___x_1613_, 7, v___x_1612_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*8, v_trackGen_1601_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*8 + 1, v_logWrites_1602_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___f_1604_);
v___x_1615_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1614_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1628_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1628_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1628_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_descr_1598_);
lean_ctor_set(v___x_1620_, 1, v_a_1616_);
v___x_1621_ = l_Lean_scopedEnvExtensionsRef;
v___x_1622_ = lean_st_ref_take(v___x_1621_);
lean_inc_ref(v___x_1620_);
v___x_1623_ = lean_array_push(v___x_1622_, v___x_1620_);
v___x_1624_ = lean_st_ref_put(v___x_1621_, v___x_1623_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1626_ = v___x_1618_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1620_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_descr_1598_);
v_a_1629_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1615_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1615_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
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
}
}
LEAN_EXPORT void l_Lean_registerScopedEnvExtensionUnsafe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1598_ = stack[0].m_obj;
lean_object* v_res_1644_;
v_res_1644_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1598_);
stack->m_obj
 = v_res_1644_;
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1645_);
return v_res_1647_;
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_00_u03c3_1650_, lean_object* v_descr_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT void l_Lean_registerScopedEnvExtensionUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_1651_ = stack[3].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l_Lean_registerScopedEnvExtensionUnsafe(lean_box(0), lean_box(0), lean_box(0), v_descr_1651_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_, lean_object* v_00_u03c3_1657_, lean_object* v_descr_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1655_, v_00_u03b2_1656_, v_00_u03c3_1657_, v_descr_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0(lean_object* v_f_1661_, lean_object* v_ps_1662_){
_start:
{
lean_object* v_importedEntries_1663_; lean_object* v_state_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_importedEntries_1663_ = lean_ctor_get(v_ps_1662_, 0);
v_state_1664_ = lean_ctor_get(v_ps_1662_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_ps_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_ps_1662_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_state_1664_);
lean_inc(v_importedEntries_1663_);
lean_dec(v_ps_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_apply_1(v_f_1661_, v_state_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_importedEntries_1663_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(lean_object* v_as_1673_, size_t v_i_1674_, size_t v_stop_1675_, lean_object* v_b_1676_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_eq(v_i_1674_, v_stop_1675_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; size_t v___x_1680_; size_t v___x_1681_; 
v___x_1678_ = lean_array_uget_borrowed(v_as_1673_, v_i_1674_);
lean_inc(v___x_1678_);
v___x_1679_ = l_Lean_Environment_logDeclChange(v_b_1676_, v___x_1678_);
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1674_, v___x_1680_);
v_i_1674_ = v___x_1681_;
v_b_1676_ = v___x_1679_;
goto _start;
}
else
{
return v_b_1676_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1673_ = stack[0].m_obj;
size_t v_i_1674_ = stack[1].m_num;
size_t v_stop_1675_ = stack[2].m_num;
lean_object* v_b_1676_ = stack[3].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_as_1673_, v_i_1674_, v_stop_1675_, v_b_1676_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0___boxed(lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_stop_1686_, lean_object* v_b_1687_){
_start:
{
size_t v_i_boxed_1688_; size_t v_stop_boxed_1689_; lean_object* v_res_1690_; 
v_i_boxed_1688_ = lean_unbox_usize(v_i_1685_);
lean_dec(v_i_1685_);
v_stop_boxed_1689_ = lean_unbox_usize(v_stop_1686_);
lean_dec(v_stop_1686_);
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_as_1684_, v_i_boxed_1688_, v_stop_boxed_1689_, v_b_1687_);
lean_dec_ref(v_as_1684_);
return v_res_1690_;
}
}
lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(lean_object* v_ext_1691_, lean_object* v_env_1692_, uint8_t v_changed_1693_, lean_object* v_f_1694_, lean_object* v_changedDecls_1695_){
_start:
{
lean_object* v___f_1696_; uint8_t v___y_1698_; lean_object* v___y_1699_; 
v___f_1696_ = lean_alloc_closure((void*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1696_, 0, v_f_1694_);
if (v_changed_1693_ == 0)
{
v___y_1698_ = v_changed_1693_;
v___y_1699_ = v_env_1692_;
goto v___jp_1697_;
}
else
{
lean_object* v_descr_1705_; uint8_t v___x_1706_; 
v_descr_1705_ = lean_ctor_get(v_ext_1691_, 0);
v___x_1706_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_1705_);
if (v___x_1706_ == 0)
{
v___y_1698_ = v___x_1706_;
v___y_1699_ = v_env_1692_;
goto v___jp_1697_;
}
else
{
uint8_t v_logWrites_1707_; 
v_logWrites_1707_ = lean_ctor_get_uint8(v_descr_1705_, sizeof(void*)*8 + 1);
if (v_logWrites_1707_ == 0)
{
v___y_1698_ = v___x_1706_;
v___y_1699_ = v_env_1692_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_array_get_size(v_changedDecls_1695_);
v___x_1710_ = lean_nat_dec_lt(v___x_1708_, v___x_1709_);
if (v___x_1710_ == 0)
{
v___y_1698_ = v___x_1706_;
v___y_1699_ = v_env_1692_;
goto v___jp_1697_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_nat_dec_le(v___x_1709_, v___x_1709_);
if (v___x_1711_ == 0)
{
if (v___x_1710_ == 0)
{
v___y_1698_ = v___x_1706_;
v___y_1699_ = v_env_1692_;
goto v___jp_1697_;
}
else
{
size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = lean_usize_of_nat(v___x_1709_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1695_, v___x_1712_, v___x_1713_, v_env_1692_);
v___y_1698_ = v___x_1706_;
v___y_1699_ = v___x_1714_;
goto v___jp_1697_;
}
}
else
{
size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = lean_usize_of_nat(v___x_1709_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1695_, v___x_1715_, v___x_1716_, v_env_1692_);
v___y_1698_ = v___x_1706_;
v___y_1699_ = v___x_1717_;
goto v___jp_1697_;
}
}
}
}
}
v___jp_1697_:
{
lean_object* v_ext_1700_; lean_object* v_toEnvExtension_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_ext_1700_ = lean_ctor_get(v_ext_1691_, 1);
lean_inc_ref(v_ext_1700_);
lean_dec_ref(v_ext_1691_);
v_toEnvExtension_1701_ = lean_ctor_get(v_ext_1700_, 0);
lean_inc_ref(v_toEnvExtension_1701_);
lean_dec_ref(v_ext_1700_);
v___x_1702_ = lean_box(1);
v___x_1703_ = lean_box(0);
v___x_1704_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1701_, v___y_1699_, v___f_1696_, v___x_1702_, v___x_1703_, v___y_1698_);
return v___x_1704_;
}
}
}
LEAN_EXPORT void l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1691_ = stack[0].m_obj;
lean_object* v_env_1692_ = stack[1].m_obj;
uint8_t v_changed_1693_ = stack[2].m_num;
lean_object* v_f_1694_ = stack[3].m_obj;
lean_object* v_changedDecls_1695_ = stack[4].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1691_, v_env_1692_, v_changed_1693_, v_f_1694_, v_changedDecls_1695_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___boxed(lean_object* v_ext_1719_, lean_object* v_env_1720_, lean_object* v_changed_1721_, lean_object* v_f_1722_, lean_object* v_changedDecls_1723_){
_start:
{
uint8_t v_changed_boxed_1724_; lean_object* v_res_1725_; 
v_changed_boxed_1724_ = lean_unbox(v_changed_1721_);
v_res_1725_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1719_, v_env_1720_, v_changed_boxed_1724_, v_f_1722_, v_changedDecls_1723_);
lean_dec_ref(v_changedDecls_1723_);
return v_res_1725_;
}
}
lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_object* v_00_u03b1_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_00_u03c3_1728_, lean_object* v_ext_1729_, lean_object* v_env_1730_, uint8_t v_changed_1731_, lean_object* v_f_1732_, lean_object* v_changedDecls_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1729_, v_env_1730_, v_changed_1731_, v_f_1732_, v_changedDecls_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT void l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_1729_ = stack[3].m_obj;
lean_object* v_env_1730_ = stack[4].m_obj;
uint8_t v_changed_1731_ = stack[5].m_num;
lean_object* v_f_1732_ = stack[6].m_obj;
lean_object* v_changedDecls_1733_ = stack[7].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_box(0), lean_box(0), lean_box(0), v_ext_1729_, v_env_1730_, v_changed_1731_, v_f_1732_, v_changedDecls_1733_);
stack->m_obj
 = v_res_1735_;
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_00_u03c3_1738_, lean_object* v_ext_1739_, lean_object* v_env_1740_, lean_object* v_changed_1741_, lean_object* v_f_1742_, lean_object* v_changedDecls_1743_){
_start:
{
uint8_t v_changed_boxed_1744_; lean_object* v_res_1745_; 
v_changed_boxed_1744_ = lean_unbox(v_changed_1741_);
v_res_1745_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(v_00_u03b1_1736_, v_00_u03b2_1737_, v_00_u03c3_1738_, v_ext_1739_, v_env_1740_, v_changed_boxed_1744_, v_f_1742_, v_changedDecls_1743_);
lean_dec_ref(v_changedDecls_1743_);
return v_res_1745_;
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(uint8_t v___x_1746_, lean_object* v_s_1747_){
_start:
{
lean_object* v_stateStack_1748_; 
v_stateStack_1748_ = lean_ctor_get(v_s_1747_, 0);
if (lean_obj_tag(v_stateStack_1748_) == 0)
{
return v_s_1747_;
}
else
{
lean_object* v_head_1749_; lean_object* v_scopedEntries_1750_; lean_object* v_newEntries_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1771_; 
lean_inc_ref(v_stateStack_1748_);
v_head_1749_ = lean_ctor_get(v_stateStack_1748_, 0);
lean_inc(v_head_1749_);
v_scopedEntries_1750_ = lean_ctor_get(v_s_1747_, 1);
v_newEntries_1751_ = lean_ctor_get(v_s_1747_, 2);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_s_1747_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_s_1747_, 0);
lean_dec(v_unused_1772_);
v___x_1753_ = v_s_1747_;
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_newEntries_1751_);
lean_inc(v_scopedEntries_1750_);
lean_dec(v_s_1747_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_state_1755_; lean_object* v_activeScopes_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1769_; 
v_state_1755_ = lean_ctor_get(v_head_1749_, 0);
v_activeScopes_1756_ = lean_ctor_get(v_head_1749_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_head_1749_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_head_1749_, 2);
lean_dec(v_unused_1770_);
v___x_1758_ = v_head_1749_;
v_isShared_1759_ = v_isSharedCheck_1769_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_activeScopes_1756_);
lean_inc(v_state_1755_);
lean_dec(v_head_1749_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1769_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = 1;
v___x_1761_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 2, v___x_1761_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_state_1755_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_activeScopes_1756_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*3, v___x_1760_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*3 + 1, v___x_1746_);
v___x_1764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_stateStack_1748_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1764_);
v___x_1766_ = v___x_1753_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_scopedEntries_1750_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_newEntries_1751_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1746_ = stack[0].m_num;
lean_object* v_s_1747_ = stack[1].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(v___x_1746_, v_s_1747_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed(lean_object* v___x_1774_, lean_object* v_s_1775_){
_start:
{
uint8_t v___x_59__boxed_1776_; lean_object* v_res_1777_; 
v___x_59__boxed_1776_ = lean_unbox(v___x_1774_);
v_res_1777_ = l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(v___x_59__boxed_1776_, v_s_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1781_, lean_object* v_env_1782_){
_start:
{
uint8_t v___x_1783_; lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = 0;
v___f_1784_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1785_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1786_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1781_, v_env_1782_, v___x_1783_, v___f_1784_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_00_u03c3_1789_, lean_object* v_ext_1790_, lean_object* v_env_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1790_, v_env_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_tail_1793_, lean_object* v_s_1794_){
_start:
{
lean_object* v_scopedEntries_1795_; lean_object* v_newEntries_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v_scopedEntries_1795_ = lean_ctor_get(v_s_1794_, 1);
v_newEntries_1796_ = lean_ctor_get(v_s_1794_, 2);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_s_1794_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v_s_1794_, 0);
lean_dec(v_unused_1804_);
v___x_1798_ = v_s_1794_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_newEntries_1796_);
lean_inc(v_scopedEntries_1795_);
lean_dec(v_s_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_tail_1793_);
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_tail_1793_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_scopedEntries_1795_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_newEntries_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1805_, lean_object* v_env_1806_){
_start:
{
lean_object* v_ext_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v_stateStack_1813_; 
v_ext_1807_ = lean_ctor_get(v_ext_1805_, 1);
v___x_1808_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1809_ = lean_box(1);
v___x_1810_ = lean_box(0);
v___x_1811_ = 0;
lean_inc_ref(v_env_1806_);
v___x_1812_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1808_, v_ext_1807_, v_env_1806_, v___x_1809_, v___x_1810_, v___x_1811_);
v_stateStack_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_stateStack_1813_);
lean_dec(v___x_1812_);
if (lean_obj_tag(v_stateStack_1813_) == 1)
{
lean_object* v_tail_1814_; 
v_tail_1814_ = lean_ctor_get(v_stateStack_1813_, 1);
lean_inc(v_tail_1814_);
if (lean_obj_tag(v_tail_1814_) == 1)
{
lean_object* v_head_1815_; uint8_t v_scopeChanged_1816_; lean_object* v_scopeChangedDecls_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v_head_1815_ = lean_ctor_get(v_stateStack_1813_, 0);
lean_inc(v_head_1815_);
lean_dec_ref_known(v_stateStack_1813_, 2);
v_scopeChanged_1816_ = lean_ctor_get_uint8(v_head_1815_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1817_ = lean_ctor_get(v_head_1815_, 2);
lean_inc_ref(v_scopeChangedDecls_1817_);
lean_dec(v_head_1815_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1818_, 0, v_tail_1814_);
v___x_1819_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1805_, v_env_1806_, v_scopeChanged_1816_, v___f_1818_, v_scopeChangedDecls_1817_);
lean_dec_ref(v_scopeChangedDecls_1817_);
return v___x_1819_;
}
else
{
lean_dec_ref_known(v_stateStack_1813_, 2);
lean_dec(v_tail_1814_);
lean_dec_ref(v_ext_1805_);
return v_env_1806_;
}
}
else
{
lean_dec(v_stateStack_1813_);
lean_dec_ref(v_ext_1805_);
return v_env_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_00_u03c3_1822_, lean_object* v_ext_1823_, lean_object* v_env_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1823_, v_env_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_zero_1828_; uint8_t v_isZero_1829_; 
v_zero_1828_ = lean_unsigned_to_nat(0u);
v_isZero_1829_ = lean_nat_dec_eq(v_a_1826_, v_zero_1828_);
if (v_isZero_1829_ == 1)
{
return v_a_1827_;
}
else
{
if (lean_obj_tag(v_a_1827_) == 0)
{
return v_a_1827_;
}
else
{
lean_object* v_head_1830_; lean_object* v_tail_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1852_; 
v_head_1830_ = lean_ctor_get(v_a_1827_, 0);
v_tail_1831_ = lean_ctor_get(v_a_1827_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1833_ = v_a_1827_;
v_isShared_1834_ = v_isSharedCheck_1852_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_tail_1831_);
lean_inc(v_head_1830_);
lean_dec(v_a_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1852_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_state_1835_; lean_object* v_activeScopes_1836_; uint8_t v_scopeChanged_1837_; lean_object* v_scopeChangedDecls_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1851_; 
v_state_1835_ = lean_ctor_get(v_head_1830_, 0);
v_activeScopes_1836_ = lean_ctor_get(v_head_1830_, 1);
v_scopeChanged_1837_ = lean_ctor_get_uint8(v_head_1830_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1838_ = lean_ctor_get(v_head_1830_, 2);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_head_1830_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1840_ = v_head_1830_;
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_scopeChangedDecls_1838_);
lean_inc(v_activeScopes_1836_);
lean_inc(v_state_1835_);
lean_dec(v_head_1830_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_one_1842_; lean_object* v_n_1843_; lean_object* v___x_1845_; 
v_one_1842_ = lean_unsigned_to_nat(1u);
v_n_1843_ = lean_nat_sub(v_a_1826_, v_one_1842_);
if (v_isShared_1841_ == 0)
{
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_state_1835_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_activeScopes_1836_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_scopeChangedDecls_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*3 + 1, v_scopeChanged_1837_);
v___x_1845_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*3, v_isZero_1829_);
v___x_1846_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1843_, v_tail_1831_);
lean_dec(v_n_1843_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1846_);
lean_ctor_set(v___x_1833_, 0, v___x_1845_);
v___x_1848_ = v___x_1833_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1853_, v_a_1854_);
lean_dec(v_a_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1857_, v_a_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1864_, lean_object* v_s_1865_){
_start:
{
lean_object* v_stateStack_1866_; lean_object* v_scopedEntries_1867_; lean_object* v_newEntries_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_stateStack_1866_ = lean_ctor_get(v_s_1865_, 0);
v_scopedEntries_1867_ = lean_ctor_get(v_s_1865_, 1);
v_newEntries_1868_ = lean_ctor_get(v_s_1865_, 2);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_s_1865_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v_s_1865_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_newEntries_1868_);
lean_inc(v_scopedEntries_1867_);
lean_inc(v_stateStack_1866_);
lean_dec(v_s_1865_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1864_, v_stateStack_1866_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_scopedEntries_1867_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_newEntries_1868_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1877_, lean_object* v_s_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1877_, v_s_1878_);
lean_dec(v_depth_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1880_, lean_object* v_env_1881_, lean_object* v_depth_1882_){
_start:
{
lean_object* v___f_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1883_, 0, v_depth_1882_);
v___x_1884_ = 0;
v___x_1885_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1886_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1880_, v_env_1881_, v___x_1884_, v___f_1883_, v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1887_, lean_object* v_00_u03b2_1888_, lean_object* v_00_u03c3_1889_, lean_object* v_ext_1890_, lean_object* v_env_1891_, lean_object* v_depth_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1890_, v_env_1891_, v_depth_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg(lean_object* v_ext_1896_, lean_object* v_b_1897_){
_start:
{
lean_object* v_descr_1898_; lean_object* v_entryDecl_x3f_1899_; 
v_descr_1898_ = lean_ctor_get(v_ext_1896_, 0);
lean_inc_ref(v_descr_1898_);
lean_dec_ref(v_ext_1896_);
v_entryDecl_x3f_1899_ = lean_ctor_get(v_descr_1898_, 7);
lean_inc(v_entryDecl_x3f_1899_);
lean_dec_ref(v_descr_1898_);
if (lean_obj_tag(v_entryDecl_x3f_1899_) == 1)
{
lean_object* v_val_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_val_1900_ = lean_ctor_get(v_entryDecl_x3f_1899_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_entryDecl_x3f_1899_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v_entryDecl_x3f_1899_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_val_1900_);
lean_dec(v_entryDecl_x3f_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_apply_1(v_val_1900_, v_b_1897_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1909_; 
lean_dec(v_entryDecl_x3f_1899_);
lean_dec(v_b_1897_);
v___x_1909_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_00_u03c3_1912_, lean_object* v_ext_1913_, lean_object* v_b_1914_){
_start:
{
lean_object* v_descr_1915_; lean_object* v_entryDecl_x3f_1916_; 
v_descr_1915_ = lean_ctor_get(v_ext_1913_, 0);
lean_inc_ref(v_descr_1915_);
lean_dec_ref(v_ext_1913_);
v_entryDecl_x3f_1916_ = lean_ctor_get(v_descr_1915_, 7);
lean_inc(v_entryDecl_x3f_1916_);
lean_dec_ref(v_descr_1915_);
if (lean_obj_tag(v_entryDecl_x3f_1916_) == 1)
{
lean_object* v_val_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_val_1917_ = lean_ctor_get(v_entryDecl_x3f_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_entryDecl_x3f_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v_entryDecl_x3f_1916_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_val_1917_);
lean_dec(v_entryDecl_x3f_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_apply_1(v_val_1917_, v_b_1914_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_entryDecl_x3f_1916_);
lean_dec(v_b_1914_);
v___x_1926_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0(lean_object* v_addEntryFn_1927_, lean_object* v___x_1928_, lean_object* v_s_1929_){
_start:
{
lean_object* v_importedEntries_1930_; lean_object* v_state_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v_importedEntries_1930_ = lean_ctor_get(v_s_1929_, 0);
v_state_1931_ = lean_ctor_get(v_s_1929_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_s_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1933_ = v_s_1929_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_state_1931_);
lean_inc(v_importedEntries_1930_);
lean_dec(v_s_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_state_1935_; lean_object* v___x_1937_; 
v_state_1935_ = lean_apply_2(v_addEntryFn_1927_, v_state_1931_, v___x_1928_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_state_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_importedEntries_1930_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_state_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1940_, lean_object* v_env_1941_, lean_object* v_b_1942_){
_start:
{
lean_object* v_ext_1943_; lean_object* v_toEnvExtension_1944_; lean_object* v_descr_1945_; lean_object* v_addEntryFn_1946_; lean_object* v_asyncMode_1947_; uint8_t v_logWrites_1948_; lean_object* v_entryDecl_x3f_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v_declName_1954_; 
v_ext_1943_ = lean_ctor_get(v_ext_1940_, 1);
lean_inc_ref(v_ext_1943_);
v_toEnvExtension_1944_ = lean_ctor_get(v_ext_1943_, 0);
lean_inc_ref(v_toEnvExtension_1944_);
v_descr_1945_ = lean_ctor_get(v_ext_1940_, 0);
lean_inc_ref(v_descr_1945_);
lean_dec_ref(v_ext_1940_);
v_addEntryFn_1946_ = lean_ctor_get(v_ext_1943_, 3);
lean_inc(v_addEntryFn_1946_);
lean_dec_ref(v_ext_1943_);
v_asyncMode_1947_ = lean_ctor_get(v_toEnvExtension_1944_, 2);
lean_inc(v_asyncMode_1947_);
v_logWrites_1948_ = lean_ctor_get_uint8(v_toEnvExtension_1944_, sizeof(void*)*6);
v_entryDecl_x3f_1949_ = lean_ctor_get(v_descr_1945_, 7);
lean_inc(v_entryDecl_x3f_1949_);
lean_dec_ref(v_descr_1945_);
lean_inc(v_b_1942_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_b_1942_);
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1951_, 0, v_addEntryFn_1946_);
lean_closure_set(v___f_1951_, 1, v___x_1950_);
v___x_1952_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1949_) == 1)
{
lean_object* v_val_1959_; lean_object* v___x_1960_; 
v_val_1959_ = lean_ctor_get(v_entryDecl_x3f_1949_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v_entryDecl_x3f_1949_, 1);
v___x_1960_ = lean_apply_1(v_val_1959_, v_b_1942_);
v_declName_1954_ = v___x_1960_;
goto v___jp_1953_;
}
else
{
lean_dec(v_entryDecl_x3f_1949_);
lean_dec(v_b_1942_);
v_declName_1954_ = v___x_1952_;
goto v___jp_1953_;
}
v___jp_1953_:
{
uint8_t v___x_1955_; 
v___x_1955_ = 1;
if (v_logWrites_1948_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_declName_1954_);
v___x_1956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1944_, v_env_1941_, v___f_1951_, v_asyncMode_1947_, v___x_1952_, v___x_1955_);
lean_dec(v_asyncMode_1947_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = l_Lean_Environment_logDeclChange(v_env_1941_, v_declName_1954_);
v___x_1958_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1944_, v___x_1957_, v___f_1951_, v_asyncMode_1947_, v___x_1952_, v___x_1955_);
lean_dec(v_asyncMode_1947_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1961_, lean_object* v_00_u03b2_1962_, lean_object* v_00_u03c3_1963_, lean_object* v_ext_1964_, lean_object* v_env_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1964_, v_env_1965_, v_b_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1968_, lean_object* v_env_1969_, lean_object* v_namespaceName_1970_, lean_object* v_b_1971_){
_start:
{
lean_object* v_ext_1972_; lean_object* v_toEnvExtension_1973_; lean_object* v_descr_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1995_; 
v_ext_1972_ = lean_ctor_get(v_ext_1968_, 1);
lean_inc_ref(v_ext_1972_);
v_toEnvExtension_1973_ = lean_ctor_get(v_ext_1972_, 0);
lean_inc_ref(v_toEnvExtension_1973_);
v_descr_1974_ = lean_ctor_get(v_ext_1968_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_ext_1968_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_ext_1968_, 1);
lean_dec(v_unused_1996_);
v___x_1976_ = v_ext_1968_;
v_isShared_1977_ = v_isSharedCheck_1995_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_descr_1974_);
lean_dec(v_ext_1968_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1995_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_addEntryFn_1978_; lean_object* v_asyncMode_1979_; uint8_t v_logWrites_1980_; lean_object* v_entryDecl_x3f_1981_; lean_object* v___x_1983_; 
v_addEntryFn_1978_ = lean_ctor_get(v_ext_1972_, 3);
lean_inc(v_addEntryFn_1978_);
lean_dec_ref(v_ext_1972_);
v_asyncMode_1979_ = lean_ctor_get(v_toEnvExtension_1973_, 2);
lean_inc(v_asyncMode_1979_);
v_logWrites_1980_ = lean_ctor_get_uint8(v_toEnvExtension_1973_, sizeof(void*)*6);
v_entryDecl_x3f_1981_ = lean_ctor_get(v_descr_1974_, 7);
lean_inc(v_entryDecl_x3f_1981_);
lean_dec_ref(v_descr_1974_);
lean_inc(v_b_1971_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 1);
lean_ctor_set(v___x_1976_, 1, v_b_1971_);
lean_ctor_set(v___x_1976_, 0, v_namespaceName_1970_);
v___x_1983_ = v___x_1976_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_namespaceName_1970_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_b_1971_);
v___x_1983_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v_declName_1987_; 
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1984_, 0, v_addEntryFn_1978_);
lean_closure_set(v___f_1984_, 1, v___x_1983_);
v___x_1985_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1981_) == 1)
{
lean_object* v_val_1992_; lean_object* v___x_1993_; 
v_val_1992_ = lean_ctor_get(v_entryDecl_x3f_1981_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v_entryDecl_x3f_1981_, 1);
v___x_1993_ = lean_apply_1(v_val_1992_, v_b_1971_);
v_declName_1987_ = v___x_1993_;
goto v___jp_1986_;
}
else
{
lean_dec(v_entryDecl_x3f_1981_);
lean_dec(v_b_1971_);
v_declName_1987_ = v___x_1985_;
goto v___jp_1986_;
}
v___jp_1986_:
{
uint8_t v___x_1988_; 
v___x_1988_ = 1;
if (v_logWrites_1980_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v_declName_1987_);
v___x_1989_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1973_, v_env_1969_, v___f_1984_, v_asyncMode_1979_, v___x_1985_, v___x_1988_);
lean_dec(v_asyncMode_1979_);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = l_Lean_Environment_logDeclChange(v_env_1969_, v_declName_1987_);
v___x_1991_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1973_, v___x_1990_, v___f_1984_, v_asyncMode_1979_, v___x_1985_, v___x_1988_);
lean_dec(v_asyncMode_1979_);
return v___x_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_00_u03c3_1999_, lean_object* v_ext_2000_, lean_object* v_env_2001_, lean_object* v_namespaceName_2002_, lean_object* v_b_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2000_, v_env_2001_, v_namespaceName_2002_, v_b_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_2005_, lean_object* v_states_2006_, lean_object* v_b_2007_){
_start:
{
if (lean_obj_tag(v_states_2006_) == 0)
{
lean_dec(v_b_2007_);
lean_dec_ref(v_ext_2005_);
return v_states_2006_;
}
else
{
lean_object* v_descr_2008_; lean_object* v_head_2009_; lean_object* v_tail_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2037_; 
v_descr_2008_ = lean_ctor_get(v_ext_2005_, 0);
v_head_2009_ = lean_ctor_get(v_states_2006_, 0);
v_tail_2010_ = lean_ctor_get(v_states_2006_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_states_2006_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2012_ = v_states_2006_;
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_tail_2010_);
lean_inc(v_head_2009_);
lean_dec(v_states_2006_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2037_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_addEntry_2014_; lean_object* v_state_2015_; lean_object* v_activeScopes_2016_; uint8_t v_delimitsLocal_2017_; uint8_t v_scopeChanged_2018_; lean_object* v_scopeChangedDecls_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2036_; 
v_addEntry_2014_ = lean_ctor_get(v_descr_2008_, 4);
v_state_2015_ = lean_ctor_get(v_head_2009_, 0);
v_activeScopes_2016_ = lean_ctor_get(v_head_2009_, 1);
v_delimitsLocal_2017_ = lean_ctor_get_uint8(v_head_2009_, sizeof(void*)*3);
v_scopeChanged_2018_ = lean_ctor_get_uint8(v_head_2009_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2019_ = lean_ctor_get(v_head_2009_, 2);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_head_2009_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2021_ = v_head_2009_;
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_scopeChangedDecls_2019_);
lean_inc(v_activeScopes_2016_);
lean_inc(v_state_2015_);
lean_dec(v_head_2009_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
lean_inc(v_addEntry_2014_);
lean_inc(v_b_2007_);
v___x_2023_ = lean_apply_2(v_addEntry_2014_, v_state_2015_, v_b_2007_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_activeScopes_2016_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_scopeChangedDecls_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*3, v_delimitsLocal_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*3 + 1, v_scopeChanged_2018_);
v___x_2025_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v_top_2026_; uint8_t v_delimitsLocal_2027_; 
lean_inc(v_b_2007_);
lean_inc_ref(v_descr_2008_);
v_top_2026_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2008_, v___x_2025_, v_b_2007_);
v_delimitsLocal_2027_ = lean_ctor_get_uint8(v_top_2026_, sizeof(void*)*3);
if (v_delimitsLocal_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = l_Lean_stateStackModify___redArg(v_ext_2005_, v_tail_2010_, v_b_2007_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2028_);
lean_ctor_set(v___x_2012_, 0, v_top_2026_);
v___x_2030_ = v___x_2012_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_top_2026_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
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
lean_object* v___x_2033_; 
lean_dec(v_b_2007_);
lean_dec_ref(v_ext_2005_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_top_2026_);
v___x_2033_ = v___x_2012_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_top_2026_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_tail_2010_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_00_u03c3_2040_, lean_object* v_ext_2041_, lean_object* v_states_2042_, lean_object* v_b_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_stateStackModify___redArg(v_ext_2041_, v_states_2042_, v_b_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_2045_, lean_object* v_b_2046_, lean_object* v_ps_2047_){
_start:
{
lean_object* v_state_2048_; lean_object* v_importedEntries_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2067_; 
v_state_2048_ = lean_ctor_get(v_ps_2047_, 1);
v_importedEntries_2049_ = lean_ctor_get(v_ps_2047_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_ps_2047_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2051_ = v_ps_2047_;
v_isShared_2052_ = v_isSharedCheck_2067_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_state_2048_);
lean_inc(v_importedEntries_2049_);
lean_dec(v_ps_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2067_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_stateStack_2053_; lean_object* v_scopedEntries_2054_; lean_object* v_newEntries_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
v_stateStack_2053_ = lean_ctor_get(v_state_2048_, 0);
v_scopedEntries_2054_ = lean_ctor_get(v_state_2048_, 1);
v_newEntries_2055_ = lean_ctor_get(v_state_2048_, 2);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_state_2048_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2057_ = v_state_2048_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_newEntries_2055_);
lean_inc(v_scopedEntries_2054_);
lean_inc(v_stateStack_2053_);
lean_dec(v_state_2048_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = l_Lean_stateStackModify___redArg(v_ext_2045_, v_stateStack_2053_, v_b_2046_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_scopedEntries_2054_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_newEntries_2055_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2061_);
v___x_2063_ = v___x_2051_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_importedEntries_2049_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_2068_, lean_object* v_env_2069_, lean_object* v_b_2070_){
_start:
{
lean_object* v_descr_2071_; lean_object* v_ext_2072_; lean_object* v_entryDecl_x3f_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v_declName_2079_; 
v_descr_2071_ = lean_ctor_get(v_ext_2068_, 0);
v_ext_2072_ = lean_ctor_get(v_ext_2068_, 1);
lean_inc_ref(v_ext_2072_);
v_entryDecl_x3f_2073_ = lean_ctor_get(v_descr_2071_, 7);
lean_inc(v_entryDecl_x3f_2073_);
lean_inc(v_b_2070_);
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2074_, 0, v_ext_2068_);
lean_closure_set(v___f_2074_, 1, v_b_2070_);
v___x_2075_ = lean_box(1);
v___x_2076_ = lean_box(0);
v___x_2077_ = 1;
if (lean_obj_tag(v_entryDecl_x3f_2073_) == 1)
{
lean_object* v_val_2085_; lean_object* v___x_2086_; 
v_val_2085_ = lean_ctor_get(v_entryDecl_x3f_2073_, 0);
lean_inc(v_val_2085_);
lean_dec_ref_known(v_entryDecl_x3f_2073_, 1);
v___x_2086_ = lean_apply_1(v_val_2085_, v_b_2070_);
v_declName_2079_ = v___x_2086_;
goto v___jp_2078_;
}
else
{
lean_dec(v_entryDecl_x3f_2073_);
lean_dec(v_b_2070_);
v_declName_2079_ = v___x_2076_;
goto v___jp_2078_;
}
v___jp_2078_:
{
lean_object* v_toEnvExtension_2080_; uint8_t v_logWrites_2081_; 
v_toEnvExtension_2080_ = lean_ctor_get(v_ext_2072_, 0);
lean_inc_ref(v_toEnvExtension_2080_);
lean_dec_ref(v_ext_2072_);
v_logWrites_2081_ = lean_ctor_get_uint8(v_toEnvExtension_2080_, sizeof(void*)*6);
if (v_logWrites_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_dec(v_declName_2079_);
v___x_2082_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2080_, v_env_2069_, v___f_2074_, v___x_2075_, v___x_2076_, v___x_2077_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_Lean_Environment_logDeclChange(v_env_2069_, v_declName_2079_);
v___x_2084_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2080_, v___x_2083_, v___f_2074_, v___x_2075_, v___x_2076_, v___x_2077_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_00_u03c3_2089_, lean_object* v_ext_2090_, lean_object* v_env_2091_, lean_object* v_b_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2090_, v_env_2091_, v_b_2092_);
return v___x_2093_;
}
}
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_2094_, lean_object* v_ext_2095_, lean_object* v_b_2096_, uint8_t v_kind_2097_, lean_object* v_namespaceName_2098_){
_start:
{
switch(v_kind_2097_)
{
case 0:
{
lean_object* v___x_2099_; 
lean_dec(v_namespaceName_2098_);
v___x_2099_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_2095_, v_env_2094_, v_b_2096_);
return v___x_2099_;
}
case 1:
{
lean_object* v___x_2100_; 
lean_dec(v_namespaceName_2098_);
v___x_2100_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2095_, v_env_2094_, v_b_2096_);
return v___x_2100_;
}
default: 
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2095_, v_env_2094_, v_namespaceName_2098_, v_b_2096_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_addCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2094_ = stack[0].m_obj;
lean_object* v_ext_2095_ = stack[1].m_obj;
lean_object* v_b_2096_ = stack[2].m_obj;
uint8_t v_kind_2097_ = stack[3].m_num;
lean_object* v_namespaceName_2098_ = stack[4].m_obj;
lean_object* v_res_2102_;
v_res_2102_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2094_, v_ext_2095_, v_b_2096_, v_kind_2097_, v_namespaceName_2098_);
stack->m_obj
 = v_res_2102_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_2103_, lean_object* v_ext_2104_, lean_object* v_b_2105_, lean_object* v_kind_2106_, lean_object* v_namespaceName_2107_){
_start:
{
uint8_t v_kind_boxed_2108_; lean_object* v_res_2109_; 
v_kind_boxed_2108_ = lean_unbox(v_kind_2106_);
v_res_2109_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2103_, v_ext_2104_, v_b_2105_, v_kind_boxed_2108_, v_namespaceName_2107_);
return v_res_2109_;
}
}
lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_00_u03c3_2112_, lean_object* v_env_2113_, lean_object* v_ext_2114_, lean_object* v_b_2115_, uint8_t v_kind_2116_, lean_object* v_namespaceName_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2113_, v_ext_2114_, v_b_2115_, v_kind_2116_, v_namespaceName_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_addCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2113_ = stack[3].m_obj;
lean_object* v_ext_2114_ = stack[4].m_obj;
lean_object* v_b_2115_ = stack[5].m_obj;
uint8_t v_kind_2116_ = stack[6].m_num;
lean_object* v_namespaceName_2117_ = stack[7].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l_Lean_ScopedEnvExtension_addCore(lean_box(0), lean_box(0), lean_box(0), v_env_2113_, v_ext_2114_, v_b_2115_, v_kind_2116_, v_namespaceName_2117_);
stack->m_obj
 = v_res_2119_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_00_u03c3_2122_, lean_object* v_env_2123_, lean_object* v_ext_2124_, lean_object* v_b_2125_, lean_object* v_kind_2126_, lean_object* v_namespaceName_2127_){
_start:
{
uint8_t v_kind_boxed_2128_; lean_object* v_res_2129_; 
v_kind_boxed_2128_ = lean_unbox(v_kind_2126_);
v_res_2129_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_2120_, v_00_u03b2_2121_, v_00_u03c3_2122_, v_env_2123_, v_ext_2124_, v_b_2125_, v_kind_boxed_2128_, v_namespaceName_2127_);
return v_res_2129_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_2130_, lean_object* v_b_2131_, uint8_t v_kind_2132_, lean_object* v_ns_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_2134_, v_ext_2130_, v_b_2131_, v_kind_2132_, v_ns_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2130_ = stack[0].m_obj;
lean_object* v_b_2131_ = stack[1].m_obj;
uint8_t v_kind_2132_ = stack[2].m_num;
lean_object* v_ns_2133_ = stack[3].m_obj;
lean_object* v_x_2134_ = stack[4].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_2130_, v_b_2131_, v_kind_2132_, v_ns_2133_, v_x_2134_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_2137_, lean_object* v_b_2138_, lean_object* v_kind_2139_, lean_object* v_ns_2140_, lean_object* v_x_2141_){
_start:
{
uint8_t v_kind_boxed_2142_; lean_object* v_res_2143_; 
v_kind_boxed_2142_ = lean_unbox(v_kind_2139_);
v_res_2143_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_2137_, v_b_2138_, v_kind_boxed_2142_, v_ns_2140_, v_x_2141_);
return v_res_2143_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_2144_, lean_object* v_ext_2145_, lean_object* v_b_2146_, uint8_t v_kind_2147_, lean_object* v_ns_2148_){
_start:
{
lean_object* v_modifyEnv_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; 
v_modifyEnv_2149_ = lean_ctor_get(v_inst_2144_, 1);
lean_inc(v_modifyEnv_2149_);
lean_dec_ref(v_inst_2144_);
v___x_2150_ = lean_box(v_kind_2147_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2151_, 0, v_ext_2145_);
lean_closure_set(v___f_2151_, 1, v_b_2146_);
lean_closure_set(v___f_2151_, 2, v___x_2150_);
lean_closure_set(v___f_2151_, 3, v_ns_2148_);
v___x_2152_ = lean_apply_1(v_modifyEnv_2149_, v___f_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2144_ = stack[0].m_obj;
lean_object* v_ext_2145_ = stack[1].m_obj;
lean_object* v_b_2146_ = stack[2].m_obj;
uint8_t v_kind_2147_ = stack[3].m_num;
lean_object* v_ns_2148_ = stack[4].m_obj;
lean_object* v_res_2153_;
v_res_2153_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_2144_, v_ext_2145_, v_b_2146_, v_kind_2147_, v_ns_2148_);
stack->m_obj
 = v_res_2153_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_2154_, lean_object* v_ext_2155_, lean_object* v_b_2156_, lean_object* v_kind_2157_, lean_object* v_ns_2158_){
_start:
{
uint8_t v_kind_boxed_2159_; lean_object* v_res_2160_; 
v_kind_boxed_2159_ = lean_unbox(v_kind_2157_);
v_res_2160_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_2154_, v_ext_2155_, v_b_2156_, v_kind_boxed_2159_, v_ns_2158_);
return v_res_2160_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_ext_2164_, lean_object* v_b_2165_, uint8_t v_kind_2166_){
_start:
{
lean_object* v_toBind_2167_; lean_object* v_getCurrNamespace_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; 
v_toBind_2167_ = lean_ctor_get(v_inst_2161_, 1);
lean_inc(v_toBind_2167_);
lean_dec_ref(v_inst_2161_);
v_getCurrNamespace_2168_ = lean_ctor_get(v_inst_2162_, 0);
lean_inc(v_getCurrNamespace_2168_);
lean_dec_ref(v_inst_2162_);
v___x_2169_ = lean_box(v_kind_2166_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2170_, 0, v_inst_2163_);
lean_closure_set(v___f_2170_, 1, v_ext_2164_);
lean_closure_set(v___f_2170_, 2, v_b_2165_);
lean_closure_set(v___f_2170_, 3, v___x_2169_);
v___x_2171_ = lean_apply_4(v_toBind_2167_, lean_box(0), lean_box(0), v_getCurrNamespace_2168_, v___f_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2161_ = stack[0].m_obj;
lean_object* v_inst_2162_ = stack[1].m_obj;
lean_object* v_inst_2163_ = stack[2].m_obj;
lean_object* v_ext_2164_ = stack[3].m_obj;
lean_object* v_b_2165_ = stack[4].m_obj;
uint8_t v_kind_2166_ = stack[5].m_num;
lean_object* v_res_2172_;
v_res_2172_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2161_, v_inst_2162_, v_inst_2163_, v_ext_2164_, v_b_2165_, v_kind_2166_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_ext_2176_, lean_object* v_b_2177_, lean_object* v_kind_2178_){
_start:
{
uint8_t v_kind_boxed_2179_; lean_object* v_res_2180_; 
v_kind_boxed_2179_ = lean_unbox(v_kind_2178_);
v_res_2180_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2173_, v_inst_2174_, v_inst_2175_, v_ext_2176_, v_b_2177_, v_kind_boxed_2179_);
return v_res_2180_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_2181_, lean_object* v_00_u03b1_2182_, lean_object* v_00_u03b2_2183_, lean_object* v_00_u03c3_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_ext_2188_, lean_object* v_b_2189_, uint8_t v_kind_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2185_, v_inst_2186_, v_inst_2187_, v_ext_2188_, v_b_2189_, v_kind_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2185_ = stack[4].m_obj;
lean_object* v_inst_2186_ = stack[5].m_obj;
lean_object* v_inst_2187_ = stack[6].m_obj;
lean_object* v_ext_2188_ = stack[7].m_obj;
lean_object* v_b_2189_ = stack[8].m_obj;
uint8_t v_kind_2190_ = stack[9].m_num;
lean_object* v_res_2192_;
v_res_2192_ = l_Lean_ScopedEnvExtension_add(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_2185_, v_inst_2186_, v_inst_2187_, v_ext_2188_, v_b_2189_, v_kind_2190_);
stack->m_obj
 = v_res_2192_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_2193_, lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_00_u03c3_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_ext_2200_, lean_object* v_b_2201_, lean_object* v_kind_2202_){
_start:
{
uint8_t v_kind_boxed_2203_; lean_object* v_res_2204_; 
v_kind_boxed_2203_ = lean_unbox(v_kind_2202_);
v_res_2204_ = l_Lean_ScopedEnvExtension_add(v_m_2193_, v_00_u03b1_2194_, v_00_u03b2_2195_, v_00_u03c3_2196_, v_inst_2197_, v_inst_2198_, v_inst_2199_, v_ext_2200_, v_b_2201_, v_kind_boxed_2203_);
return v_res_2204_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2208_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_2209_ = lean_unsigned_to_nat(16u);
v___x_2210_ = lean_unsigned_to_nat(285u);
v___x_2211_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_2212_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_2213_ = l_mkPanicMessageWithDecl(v___x_2212_, v___x_2211_, v___x_2210_, v___x_2209_, v___x_2208_);
return v___x_2213_;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_2214_, lean_object* v_ext_2215_, lean_object* v_env_2216_, lean_object* v_asyncMode_2217_, uint8_t v_genRecorded_2218_){
_start:
{
lean_object* v_ext_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_stateStack_2223_; 
v_ext_2219_ = lean_ctor_get(v_ext_2215_, 1);
v___x_2220_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2221_ = lean_box(0);
v___x_2222_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2220_, v_ext_2219_, v_env_2216_, v_asyncMode_2217_, v___x_2221_, v_genRecorded_2218_);
v_stateStack_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_stateStack_2223_);
lean_dec(v___x_2222_);
if (lean_obj_tag(v_stateStack_2223_) == 1)
{
lean_object* v_head_2224_; lean_object* v_state_2225_; 
v_head_2224_ = lean_ctor_get(v_stateStack_2223_, 0);
lean_inc(v_head_2224_);
lean_dec_ref_known(v_stateStack_2223_, 2);
v_state_2225_ = lean_ctor_get(v_head_2224_, 0);
lean_inc(v_state_2225_);
lean_dec(v_head_2224_);
return v_state_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v_stateStack_2223_);
v___x_2226_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_2227_ = l_panic___redArg(v_inst_2214_, v___x_2226_);
return v___x_2227_;
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_getState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2214_ = stack[0].m_obj;
lean_object* v_ext_2215_ = stack[1].m_obj;
lean_object* v_env_2216_ = stack[2].m_obj;
lean_object* v_asyncMode_2217_ = stack[3].m_obj;
uint8_t v_genRecorded_2218_ = stack[4].m_num;
lean_object* v_res_2228_;
v_res_2228_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2214_, v_ext_2215_, v_env_2216_, v_asyncMode_2217_, v_genRecorded_2218_);
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_2229_, lean_object* v_ext_2230_, lean_object* v_env_2231_, lean_object* v_asyncMode_2232_, lean_object* v_genRecorded_2233_){
_start:
{
uint8_t v_genRecorded_boxed_2234_; lean_object* v_res_2235_; 
v_genRecorded_boxed_2234_ = lean_unbox(v_genRecorded_2233_);
v_res_2235_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2229_, v_ext_2230_, v_env_2231_, v_asyncMode_2232_, v_genRecorded_boxed_2234_);
lean_dec(v_asyncMode_2232_);
lean_dec_ref(v_ext_2230_);
lean_dec(v_inst_2229_);
return v_res_2235_;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_2236_, lean_object* v_00_u03b1_2237_, lean_object* v_00_u03b2_2238_, lean_object* v_inst_2239_, lean_object* v_ext_2240_, lean_object* v_env_2241_, lean_object* v_asyncMode_2242_, uint8_t v_genRecorded_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2239_, v_ext_2240_, v_env_2241_, v_asyncMode_2242_, v_genRecorded_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_getState_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2239_ = stack[3].m_obj;
lean_object* v_ext_2240_ = stack[4].m_obj;
lean_object* v_env_2241_ = stack[5].m_obj;
lean_object* v_asyncMode_2242_ = stack[6].m_obj;
uint8_t v_genRecorded_2243_ = stack[7].m_num;
lean_object* v_res_2245_;
v_res_2245_ = l_Lean_ScopedEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), v_inst_2239_, v_ext_2240_, v_env_2241_, v_asyncMode_2242_, v_genRecorded_2243_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_2246_, lean_object* v_00_u03b1_2247_, lean_object* v_00_u03b2_2248_, lean_object* v_inst_2249_, lean_object* v_ext_2250_, lean_object* v_env_2251_, lean_object* v_asyncMode_2252_, lean_object* v_genRecorded_2253_){
_start:
{
uint8_t v_genRecorded_boxed_2254_; lean_object* v_res_2255_; 
v_genRecorded_boxed_2254_ = lean_unbox(v_genRecorded_2253_);
v_res_2255_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_2246_, v_00_u03b1_2247_, v_00_u03b2_2248_, v_inst_2249_, v_ext_2250_, v_env_2251_, v_asyncMode_2252_, v_genRecorded_boxed_2254_);
lean_dec(v_asyncMode_2252_);
lean_dec_ref(v_ext_2250_);
lean_dec(v_inst_2249_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v___y_2256_, lean_object* v_tail_2257_, lean_object* v_s_2258_){
_start:
{
lean_object* v_scopedEntries_2259_; lean_object* v_newEntries_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2268_; 
v_scopedEntries_2259_ = lean_ctor_get(v_s_2258_, 1);
v_newEntries_2260_ = lean_ctor_get(v_s_2258_, 2);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_s_2258_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v_s_2258_, 0);
lean_dec(v_unused_2269_);
v___x_2262_ = v_s_2258_;
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_newEntries_2260_);
lean_inc(v_scopedEntries_2259_);
lean_dec(v_s_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2256_);
lean_ctor_set(v___x_2264_, 1, v_tail_2257_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2264_);
v___x_2266_ = v___x_2262_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_scopedEntries_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_newEntries_2260_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(lean_object* v_ext_2270_, lean_object* v_as_2271_, size_t v_i_2272_, size_t v_stop_2273_, lean_object* v_b_2274_){
_start:
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_usize_dec_eq(v_i_2272_, v_stop_2273_);
if (v___x_2275_ == 0)
{
lean_object* v_descr_2276_; lean_object* v_addEntry_2277_; lean_object* v_state_2278_; lean_object* v_activeScopes_2279_; uint8_t v_delimitsLocal_2280_; uint8_t v_scopeChanged_2281_; lean_object* v_scopeChangedDecls_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2295_; 
v_descr_2276_ = lean_ctor_get(v_ext_2270_, 0);
v_addEntry_2277_ = lean_ctor_get(v_descr_2276_, 4);
v_state_2278_ = lean_ctor_get(v_b_2274_, 0);
v_activeScopes_2279_ = lean_ctor_get(v_b_2274_, 1);
v_delimitsLocal_2280_ = lean_ctor_get_uint8(v_b_2274_, sizeof(void*)*3);
v_scopeChanged_2281_ = lean_ctor_get_uint8(v_b_2274_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2282_ = lean_ctor_get(v_b_2274_, 2);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_b_2274_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2284_ = v_b_2274_;
v_isShared_2285_ = v_isSharedCheck_2295_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_scopeChangedDecls_2282_);
lean_inc(v_activeScopes_2279_);
lean_inc(v_state_2278_);
lean_dec(v_b_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2295_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2286_ = lean_array_uget_borrowed(v_as_2271_, v_i_2272_);
lean_inc(v_addEntry_2277_);
lean_inc(v___x_2286_);
v___x_2287_ = lean_apply_2(v_addEntry_2277_, v_state_2278_, v___x_2286_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2287_);
v___x_2289_ = v___x_2284_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_activeScopes_2279_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_scopeChangedDecls_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2294_, sizeof(void*)*3, v_delimitsLocal_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2294_, sizeof(void*)*3 + 1, v_scopeChanged_2281_);
v___x_2289_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; size_t v___x_2291_; size_t v___x_2292_; 
lean_inc(v___x_2286_);
lean_inc_ref(v_descr_2276_);
v___x_2290_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2276_, v___x_2289_, v___x_2286_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2272_, v___x_2291_);
v_i_2272_ = v___x_2292_;
v_b_2274_ = v___x_2290_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ext_2270_);
return v_b_2274_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2270_ = stack[0].m_obj;
lean_object* v_as_2271_ = stack[1].m_obj;
size_t v_i_2272_ = stack[2].m_num;
size_t v_stop_2273_ = stack[3].m_num;
lean_object* v_b_2274_ = stack[4].m_obj;
lean_object* v_res_2296_;
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2270_, v_as_2271_, v_i_2272_, v_stop_2273_, v_b_2274_);
stack->m_obj
 = v_res_2296_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg___boxed(lean_object* v_ext_2297_, lean_object* v_as_2298_, lean_object* v_i_2299_, lean_object* v_stop_2300_, lean_object* v_b_2301_){
_start:
{
size_t v_i_boxed_2302_; size_t v_stop_boxed_2303_; lean_object* v_res_2304_; 
v_i_boxed_2302_ = lean_unbox_usize(v_i_2299_);
lean_dec(v_i_2299_);
v_stop_boxed_2303_ = lean_unbox_usize(v_stop_2300_);
lean_dec(v_stop_2300_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2297_, v_as_2298_, v_i_boxed_2302_, v_stop_boxed_2303_, v_b_2301_);
lean_dec_ref(v_as_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(lean_object* v_ext_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
if (lean_obj_tag(v_x_2306_) == 0)
{
lean_object* v_cs_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_cs_2308_ = lean_ctor_get(v_x_2306_, 0);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_array_get_size(v_cs_2308_);
v___x_2311_ = lean_nat_dec_lt(v___x_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v_ext_2305_);
return v_x_2307_;
}
else
{
size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = lean_usize_of_nat(v___x_2310_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2305_, v_cs_2308_, v___x_2312_, v___x_2313_, v_x_2307_);
return v___x_2314_;
}
}
else
{
lean_object* v_vs_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_vs_2315_ = lean_ctor_get(v_x_2306_, 0);
v___x_2316_ = lean_unsigned_to_nat(0u);
v___x_2317_ = lean_array_get_size(v_vs_2315_);
v___x_2318_ = lean_nat_dec_lt(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_dec_ref(v_ext_2305_);
return v_x_2307_;
}
else
{
size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = lean_usize_of_nat(v___x_2317_);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2305_, v_vs_2315_, v___x_2319_, v___x_2320_, v_x_2307_);
return v___x_2321_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(lean_object* v_ext_2322_, lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; 
v___x_2328_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
lean_inc_ref(v_ext_2322_);
v___x_2329_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2322_, v___x_2328_, v_b_2326_);
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_add(v_i_2324_, v___x_2330_);
v_i_2324_ = v___x_2331_;
v_b_2326_ = v___x_2329_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2322_);
return v_b_2326_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2322_ = stack[0].m_obj;
lean_object* v_as_2323_ = stack[1].m_obj;
size_t v_i_2324_ = stack[2].m_num;
size_t v_stop_2325_ = stack[3].m_num;
lean_object* v_b_2326_ = stack[4].m_obj;
lean_object* v_res_2333_;
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2322_, v_as_2323_, v_i_2324_, v_stop_2325_, v_b_2326_);
stack->m_obj
 = v_res_2333_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ext_2334_, lean_object* v_as_2335_, lean_object* v_i_2336_, lean_object* v_stop_2337_, lean_object* v_b_2338_){
_start:
{
size_t v_i_boxed_2339_; size_t v_stop_boxed_2340_; lean_object* v_res_2341_; 
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_stop_boxed_2340_ = lean_unbox_usize(v_stop_2337_);
lean_dec(v_stop_2337_);
v_res_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2334_, v_as_2335_, v_i_boxed_2339_, v_stop_boxed_2340_, v_b_2338_);
lean_dec_ref(v_as_2335_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg___boxed(lean_object* v_ext_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2342_, v_x_2343_, v_x_2344_);
lean_dec_ref(v_x_2343_);
return v_res_2345_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2346_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(lean_object* v_ext_2347_, lean_object* v_x_2348_, size_t v_x_2349_, size_t v_x_2350_, lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2348_) == 0)
{
lean_object* v_cs_2352_; lean_object* v___x_2353_; size_t v___x_2354_; lean_object* v_j_2355_; lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_cs_2352_ = lean_ctor_get(v_x_2348_, 0);
v___x_2353_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2354_ = lean_usize_shift_right(v_x_2349_, v_x_2350_);
v_j_2355_ = lean_usize_to_nat(v___x_2354_);
v___x_2356_ = lean_array_get_borrowed(v___x_2353_, v_cs_2352_, v_j_2355_);
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_shift_left(v___x_2357_, v_x_2350_);
v___x_2359_ = lean_usize_sub(v___x_2358_, v___x_2357_);
v___x_2360_ = lean_usize_land(v_x_2349_, v___x_2359_);
v___x_2361_ = ((size_t)5ULL);
v___x_2362_ = lean_usize_sub(v_x_2350_, v___x_2361_);
lean_inc_ref(v_ext_2347_);
v___x_2363_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2347_, v___x_2356_, v___x_2360_, v___x_2362_, v_x_2351_);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_j_2355_, v___x_2364_);
lean_dec(v_j_2355_);
v___x_2366_ = lean_array_get_size(v_cs_2352_);
v___x_2367_ = lean_nat_dec_lt(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec(v___x_2365_);
lean_dec_ref(v_ext_2347_);
return v___x_2363_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_usize_of_nat(v___x_2365_);
lean_dec(v___x_2365_);
v___x_2369_ = lean_usize_of_nat(v___x_2366_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2347_, v_cs_2352_, v___x_2368_, v___x_2369_, v___x_2363_);
return v___x_2370_;
}
}
else
{
lean_object* v_vs_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_vs_2371_ = lean_ctor_get(v_x_2348_, 0);
v___x_2372_ = lean_usize_to_nat(v_x_2349_);
v___x_2373_ = lean_array_get_size(v_vs_2371_);
v___x_2374_ = lean_nat_dec_lt(v___x_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec(v___x_2372_);
lean_dec_ref(v_ext_2347_);
return v_x_2351_;
}
else
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_usize_of_nat(v___x_2372_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_usize_of_nat(v___x_2373_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2347_, v_vs_2371_, v___x_2375_, v___x_2376_, v_x_2351_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2347_ = stack[0].m_obj;
lean_object* v_x_2348_ = stack[1].m_obj;
size_t v_x_2349_ = stack[2].m_num;
size_t v_x_2350_ = stack[3].m_num;
lean_object* v_x_2351_ = stack[4].m_obj;
lean_object* v_res_2378_;
v_res_2378_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2347_, v_x_2348_, v_x_2349_, v_x_2350_, v_x_2351_);
stack->m_obj
 = v_res_2378_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
size_t v_x_2682__boxed_2384_; size_t v_x_2683__boxed_2385_; lean_object* v_res_2386_; 
v_x_2682__boxed_2384_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_x_2683__boxed_2385_ = lean_unbox_usize(v_x_2382_);
lean_dec(v_x_2382_);
v_res_2386_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2379_, v_x_2380_, v_x_2682__boxed_2384_, v_x_2683__boxed_2385_, v_x_2383_);
lean_dec_ref(v_x_2380_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(lean_object* v_ext_2387_, lean_object* v_t_2388_, lean_object* v_init_2389_, lean_object* v_start_2390_){
_start:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = lean_unsigned_to_nat(0u);
v___x_2392_ = lean_nat_dec_eq(v_start_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v_root_2393_; lean_object* v_tail_2394_; size_t v_shift_2395_; lean_object* v_tailOff_2396_; uint8_t v___x_2397_; 
v_root_2393_ = lean_ctor_get(v_t_2388_, 0);
v_tail_2394_ = lean_ctor_get(v_t_2388_, 1);
v_shift_2395_ = lean_ctor_get_usize(v_t_2388_, 4);
v_tailOff_2396_ = lean_ctor_get(v_t_2388_, 3);
v___x_2397_ = lean_nat_dec_le(v_tailOff_2396_, v_start_2390_);
if (v___x_2397_ == 0)
{
size_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2398_ = lean_usize_of_nat(v_start_2390_);
lean_inc_ref(v_ext_2387_);
v___x_2399_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2387_, v_root_2393_, v___x_2398_, v_shift_2395_, v_init_2389_);
v___x_2400_ = lean_array_get_size(v_tail_2394_);
v___x_2401_ = lean_nat_dec_lt(v___x_2391_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_dec_ref(v_ext_2387_);
return v___x_2399_;
}
else
{
size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((size_t)0ULL);
v___x_2403_ = lean_usize_of_nat(v___x_2400_);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2387_, v_tail_2394_, v___x_2402_, v___x_2403_, v___x_2399_);
return v___x_2404_;
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2405_ = lean_nat_sub(v_start_2390_, v_tailOff_2396_);
v___x_2406_ = lean_array_get_size(v_tail_2394_);
v___x_2407_ = lean_nat_dec_lt(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v___x_2405_);
lean_dec_ref(v_ext_2387_);
return v_init_2389_;
}
else
{
size_t v___x_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_usize_of_nat(v___x_2405_);
lean_dec(v___x_2405_);
v___x_2409_ = lean_usize_of_nat(v___x_2406_);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2387_, v_tail_2394_, v___x_2408_, v___x_2409_, v_init_2389_);
return v___x_2410_;
}
}
}
else
{
lean_object* v_root_2411_; lean_object* v_tail_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_root_2411_ = lean_ctor_get(v_t_2388_, 0);
v_tail_2412_ = lean_ctor_get(v_t_2388_, 1);
lean_inc_ref(v_ext_2387_);
v___x_2413_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2387_, v_root_2411_, v_init_2389_);
v___x_2414_ = lean_array_get_size(v_tail_2412_);
v___x_2415_ = lean_nat_dec_lt(v___x_2391_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_dec_ref(v_ext_2387_);
return v___x_2413_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = lean_usize_of_nat(v___x_2414_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2387_, v_tail_2412_, v___x_2416_, v___x_2417_, v___x_2413_);
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg___boxed(lean_object* v_ext_2419_, lean_object* v_t_2420_, lean_object* v_init_2421_, lean_object* v_start_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2419_, v_t_2420_, v_init_2421_, v_start_2422_);
lean_dec(v_start_2422_);
lean_dec_ref(v_t_2420_);
return v_res_2423_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_val_2424_, lean_object* v_as_2425_, size_t v_i_2426_, size_t v_stop_2427_, lean_object* v_b_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_eq(v_i_2426_, v_stop_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; 
v___x_2430_ = lean_array_uget_borrowed(v_as_2425_, v_i_2426_);
lean_inc_ref(v_val_2424_);
lean_inc(v___x_2430_);
v___x_2431_ = lean_apply_1(v_val_2424_, v___x_2430_);
v___x_2432_ = lean_array_push(v_b_2428_, v___x_2431_);
v___x_2433_ = ((size_t)1ULL);
v___x_2434_ = lean_usize_add(v_i_2426_, v___x_2433_);
v_i_2426_ = v___x_2434_;
v_b_2428_ = v___x_2432_;
goto _start;
}
else
{
lean_dec_ref(v_val_2424_);
return v_b_2428_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2424_ = stack[0].m_obj;
lean_object* v_as_2425_ = stack[1].m_obj;
size_t v_i_2426_ = stack[2].m_num;
size_t v_stop_2427_ = stack[3].m_num;
lean_object* v_b_2428_ = stack[4].m_obj;
lean_object* v_res_2436_;
v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2424_, v_as_2425_, v_i_2426_, v_stop_2427_, v_b_2428_);
stack->m_obj
 = v_res_2436_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_val_2437_, lean_object* v_as_2438_, lean_object* v_i_2439_, lean_object* v_stop_2440_, lean_object* v_b_2441_){
_start:
{
size_t v_i_boxed_2442_; size_t v_stop_boxed_2443_; lean_object* v_res_2444_; 
v_i_boxed_2442_ = lean_unbox_usize(v_i_2439_);
lean_dec(v_i_2439_);
v_stop_boxed_2443_ = lean_unbox_usize(v_stop_2440_);
lean_dec(v_stop_2440_);
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2437_, v_as_2438_, v_i_boxed_2442_, v_stop_boxed_2443_, v_b_2441_);
lean_dec_ref(v_as_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object* v_val_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_cs_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v_cs_2448_ = lean_ctor_get(v_x_2446_, 0);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_array_get_size(v_cs_2448_);
v___x_2451_ = lean_nat_dec_lt(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v_val_2445_);
return v_x_2447_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2450_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2445_, v_cs_2448_, v___x_2452_, v___x_2453_, v_x_2447_);
return v___x_2454_;
}
}
else
{
lean_object* v_vs_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_vs_2455_ = lean_ctor_get(v_x_2446_, 0);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_array_get_size(v_vs_2455_);
v___x_2458_ = lean_nat_dec_lt(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_val_2445_);
return v_x_2447_;
}
else
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((size_t)0ULL);
v___x_2460_ = lean_usize_of_nat(v___x_2457_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2445_, v_vs_2455_, v___x_2459_, v___x_2460_, v_x_2447_);
return v___x_2461_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_val_2462_, lean_object* v_as_2463_, size_t v_i_2464_, size_t v_stop_2465_, lean_object* v_b_2466_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_usize_dec_eq(v_i_2464_, v_stop_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; 
v___x_2468_ = lean_array_uget_borrowed(v_as_2463_, v_i_2464_);
lean_inc_ref(v_val_2462_);
v___x_2469_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2462_, v___x_2468_, v_b_2466_);
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2464_, v___x_2470_);
v_i_2464_ = v___x_2471_;
v_b_2466_ = v___x_2469_;
goto _start;
}
else
{
lean_dec_ref(v_val_2462_);
return v_b_2466_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2462_ = stack[0].m_obj;
lean_object* v_as_2463_ = stack[1].m_obj;
size_t v_i_2464_ = stack[2].m_num;
size_t v_stop_2465_ = stack[3].m_num;
lean_object* v_b_2466_ = stack[4].m_obj;
lean_object* v_res_2473_;
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2462_, v_as_2463_, v_i_2464_, v_stop_2465_, v_b_2466_);
stack->m_obj
 = v_res_2473_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_val_2474_, lean_object* v_as_2475_, lean_object* v_i_2476_, lean_object* v_stop_2477_, lean_object* v_b_2478_){
_start:
{
size_t v_i_boxed_2479_; size_t v_stop_boxed_2480_; lean_object* v_res_2481_; 
v_i_boxed_2479_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_stop_boxed_2480_ = lean_unbox_usize(v_stop_2477_);
lean_dec(v_stop_2477_);
v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2474_, v_as_2475_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2478_);
lean_dec_ref(v_as_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object* v_val_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2482_, v_x_2483_, v_x_2484_);
lean_dec_ref(v_x_2483_);
return v_res_2485_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_val_2486_, lean_object* v_x_2487_, size_t v_x_2488_, size_t v_x_2489_, lean_object* v_x_2490_){
_start:
{
if (lean_obj_tag(v_x_2487_) == 0)
{
lean_object* v_cs_2491_; lean_object* v___x_2492_; size_t v___x_2493_; lean_object* v_j_2494_; lean_object* v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_cs_2491_ = lean_ctor_get(v_x_2487_, 0);
v___x_2492_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2493_ = lean_usize_shift_right(v_x_2488_, v_x_2489_);
v_j_2494_ = lean_usize_to_nat(v___x_2493_);
v___x_2495_ = lean_array_get_borrowed(v___x_2492_, v_cs_2491_, v_j_2494_);
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_shift_left(v___x_2496_, v_x_2489_);
v___x_2498_ = lean_usize_sub(v___x_2497_, v___x_2496_);
v___x_2499_ = lean_usize_land(v_x_2488_, v___x_2498_);
v___x_2500_ = ((size_t)5ULL);
v___x_2501_ = lean_usize_sub(v_x_2489_, v___x_2500_);
lean_inc_ref(v_val_2486_);
v___x_2502_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2486_, v___x_2495_, v___x_2499_, v___x_2501_, v_x_2490_);
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_add(v_j_2494_, v___x_2503_);
lean_dec(v_j_2494_);
v___x_2505_ = lean_array_get_size(v_cs_2491_);
v___x_2506_ = lean_nat_dec_lt(v___x_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_dec(v___x_2504_);
lean_dec_ref(v_val_2486_);
return v___x_2502_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_usize_of_nat(v___x_2504_);
lean_dec(v___x_2504_);
v___x_2508_ = lean_usize_of_nat(v___x_2505_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2486_, v_cs_2491_, v___x_2507_, v___x_2508_, v___x_2502_);
return v___x_2509_;
}
}
else
{
lean_object* v_vs_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_vs_2510_ = lean_ctor_get(v_x_2487_, 0);
v___x_2511_ = lean_usize_to_nat(v_x_2488_);
v___x_2512_ = lean_array_get_size(v_vs_2510_);
v___x_2513_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_dec(v___x_2511_);
lean_dec_ref(v_val_2486_);
return v_x_2490_;
}
else
{
size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_usize_of_nat(v___x_2511_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_usize_of_nat(v___x_2512_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2486_, v_vs_2510_, v___x_2514_, v___x_2515_, v_x_2490_);
return v___x_2516_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2486_ = stack[0].m_obj;
lean_object* v_x_2487_ = stack[1].m_obj;
size_t v_x_2488_ = stack[2].m_num;
size_t v_x_2489_ = stack[3].m_num;
lean_object* v_x_2490_ = stack[4].m_obj;
lean_object* v_res_2517_;
v_res_2517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2486_, v_x_2487_, v_x_2488_, v_x_2489_, v_x_2490_);
stack->m_obj
 = v_res_2517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_val_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
size_t v_x_2953__boxed_2523_; size_t v_x_2954__boxed_2524_; lean_object* v_res_2525_; 
v_x_2953__boxed_2523_ = lean_unbox_usize(v_x_2520_);
lean_dec(v_x_2520_);
v_x_2954__boxed_2524_ = lean_unbox_usize(v_x_2521_);
lean_dec(v_x_2521_);
v_res_2525_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2518_, v_x_2519_, v_x_2953__boxed_2523_, v_x_2954__boxed_2524_, v_x_2522_);
lean_dec_ref(v_x_2519_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_val_2526_, lean_object* v_t_2527_, lean_object* v_init_2528_, lean_object* v_start_2529_){
_start:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = lean_nat_dec_eq(v_start_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v_root_2532_; lean_object* v_tail_2533_; size_t v_shift_2534_; lean_object* v_tailOff_2535_; uint8_t v___x_2536_; 
v_root_2532_ = lean_ctor_get(v_t_2527_, 0);
v_tail_2533_ = lean_ctor_get(v_t_2527_, 1);
v_shift_2534_ = lean_ctor_get_usize(v_t_2527_, 4);
v_tailOff_2535_ = lean_ctor_get(v_t_2527_, 3);
v___x_2536_ = lean_nat_dec_le(v_tailOff_2535_, v_start_2529_);
if (v___x_2536_ == 0)
{
size_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2537_ = lean_usize_of_nat(v_start_2529_);
lean_inc_ref(v_val_2526_);
v___x_2538_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2526_, v_root_2532_, v___x_2537_, v_shift_2534_, v_init_2528_);
v___x_2539_ = lean_array_get_size(v_tail_2533_);
v___x_2540_ = lean_nat_dec_lt(v___x_2530_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_dec_ref(v_val_2526_);
return v___x_2538_;
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2539_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2526_, v_tail_2533_, v___x_2541_, v___x_2542_, v___x_2538_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_nat_sub(v_start_2529_, v_tailOff_2535_);
v___x_2545_ = lean_array_get_size(v_tail_2533_);
v___x_2546_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec(v___x_2544_);
lean_dec_ref(v_val_2526_);
return v_init_2528_;
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_usize_of_nat(v___x_2544_);
lean_dec(v___x_2544_);
v___x_2548_ = lean_usize_of_nat(v___x_2545_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2526_, v_tail_2533_, v___x_2547_, v___x_2548_, v_init_2528_);
return v___x_2549_;
}
}
}
else
{
lean_object* v_root_2550_; lean_object* v_tail_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_root_2550_ = lean_ctor_get(v_t_2527_, 0);
v_tail_2551_ = lean_ctor_get(v_t_2527_, 1);
lean_inc_ref(v_val_2526_);
v___x_2552_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2526_, v_root_2550_, v_init_2528_);
v___x_2553_ = lean_array_get_size(v_tail_2551_);
v___x_2554_ = lean_nat_dec_lt(v___x_2530_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_dec_ref(v_val_2526_);
return v___x_2552_;
}
else
{
size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = lean_usize_of_nat(v___x_2553_);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2526_, v_tail_2551_, v___x_2555_, v___x_2556_, v___x_2552_);
return v___x_2557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_val_2558_, lean_object* v_t_2559_, lean_object* v_init_2560_, lean_object* v_start_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2558_, v_t_2559_, v_init_2560_, v_start_2561_);
lean_dec(v_start_2561_);
lean_dec_ref(v_t_2559_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2563_, lean_object* v_env_2564_, lean_object* v_namespaceName_2565_){
_start:
{
lean_object* v_descr_2566_; lean_object* v_ext_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v_s_2572_; lean_object* v_stateStack_2573_; 
v_descr_2566_ = lean_ctor_get(v_ext_2563_, 0);
v_ext_2567_ = lean_ctor_get(v_ext_2563_, 1);
v___x_2568_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2569_ = lean_box(1);
v___x_2570_ = lean_box(0);
v___x_2571_ = 0;
lean_inc_ref(v_env_2564_);
v_s_2572_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2568_, v_ext_2567_, v_env_2564_, v___x_2569_, v___x_2570_, v___x_2571_);
v_stateStack_2573_ = lean_ctor_get(v_s_2572_, 0);
lean_inc(v_stateStack_2573_);
if (lean_obj_tag(v_stateStack_2573_) == 1)
{
lean_object* v_head_2574_; lean_object* v_scopedEntries_2575_; lean_object* v_tail_2576_; lean_object* v_state_2577_; lean_object* v_activeScopes_2578_; uint8_t v_delimitsLocal_2579_; uint8_t v_scopeChanged_2580_; lean_object* v_scopeChangedDecls_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2616_; 
v_head_2574_ = lean_ctor_get(v_stateStack_2573_, 0);
lean_inc(v_head_2574_);
v_scopedEntries_2575_ = lean_ctor_get(v_s_2572_, 1);
lean_inc_ref(v_scopedEntries_2575_);
lean_dec(v_s_2572_);
v_tail_2576_ = lean_ctor_get(v_stateStack_2573_, 1);
lean_inc(v_tail_2576_);
lean_dec_ref_known(v_stateStack_2573_, 2);
v_state_2577_ = lean_ctor_get(v_head_2574_, 0);
v_activeScopes_2578_ = lean_ctor_get(v_head_2574_, 1);
v_delimitsLocal_2579_ = lean_ctor_get_uint8(v_head_2574_, sizeof(void*)*3);
v_scopeChanged_2580_ = lean_ctor_get_uint8(v_head_2574_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2581_ = lean_ctor_get(v_head_2574_, 2);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_head_2574_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2583_ = v_head_2574_;
v_isShared_2584_ = v_isSharedCheck_2616_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_scopeChangedDecls_2581_);
lean_inc(v_activeScopes_2578_);
lean_inc(v_state_2577_);
lean_dec(v_head_2574_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2616_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_NameSet_contains(v_activeScopes_2578_, v_namespaceName_2565_);
if (v___x_2585_ == 0)
{
lean_object* v_activeScopes_2586_; lean_object* v_bs_x3f_2587_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2595_; lean_object* v___y_2598_; 
lean_inc(v_namespaceName_2565_);
v_activeScopes_2586_ = l_Lean_NameSet_insert(v_activeScopes_2578_, v_namespaceName_2565_);
v_bs_x3f_2587_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2575_, v_namespaceName_2565_);
lean_dec(v_namespaceName_2565_);
lean_dec_ref(v_scopedEntries_2575_);
if (lean_obj_tag(v_bs_x3f_2587_) == 1)
{
lean_object* v_val_2606_; uint8_t v___x_2607_; lean_object* v___x_2609_; 
v_val_2606_ = lean_ctor_get(v_bs_x3f_2587_, 0);
v___x_2607_ = 1;
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 1, v_activeScopes_2586_);
v___x_2609_ = v___x_2583_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_state_2577_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_activeScopes_2586_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v_scopeChangedDecls_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*3 + 1, v_scopeChanged_2580_);
v___x_2609_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*3, v___x_2607_);
v___x_2610_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ext_2563_);
v___x_2611_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2563_, v_val_2606_, v___x_2609_, v___x_2610_);
v___y_2598_ = v___x_2611_;
goto v___jp_2597_;
}
}
else
{
lean_object* v___x_2614_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 1, v_activeScopes_2586_);
v___x_2614_ = v___x_2583_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_state_2577_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_activeScopes_2586_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_scopeChangedDecls_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*3, v_delimitsLocal_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*3 + 1, v_scopeChanged_2580_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
v___y_2598_ = v___x_2614_;
goto v___jp_2597_;
}
}
v___jp_2588_:
{
if (lean_obj_tag(v_bs_x3f_2587_) == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2563_, v_env_2564_, v___x_2585_, v___y_2589_, v___y_2590_);
lean_dec_ref(v___y_2590_);
return v___x_2591_;
}
else
{
uint8_t v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref_known(v_bs_x3f_2587_, 1);
v___x_2592_ = 1;
v___x_2593_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2563_, v_env_2564_, v___x_2592_, v___y_2589_, v___y_2590_);
lean_dec_ref(v___y_2590_);
return v___x_2593_;
}
}
v___jp_2594_:
{
lean_object* v___x_2596_; 
v___x_2596_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___y_2589_ = v___y_2595_;
v___y_2590_ = v___x_2596_;
goto v___jp_2588_;
}
v___jp_2597_:
{
lean_object* v___f_2599_; 
v___f_2599_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2599_, 0, v___y_2598_);
lean_closure_set(v___f_2599_, 1, v_tail_2576_);
if (lean_obj_tag(v_bs_x3f_2587_) == 1)
{
lean_object* v_entryDecl_x3f_2600_; 
v_entryDecl_x3f_2600_ = lean_ctor_get(v_descr_2566_, 7);
if (lean_obj_tag(v_entryDecl_x3f_2600_) == 1)
{
lean_object* v_val_2601_; lean_object* v_val_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_val_2601_ = lean_ctor_get(v_bs_x3f_2587_, 0);
v_val_2602_ = lean_ctor_get(v_entryDecl_x3f_2600_, 0);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
lean_inc(v_val_2602_);
v___x_2605_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2602_, v_val_2601_, v___x_2604_, v___x_2603_);
v___y_2589_ = v___f_2599_;
v___y_2590_ = v___x_2605_;
goto v___jp_2588_;
}
else
{
v___y_2595_ = v___f_2599_;
goto v___jp_2594_;
}
}
else
{
v___y_2595_ = v___f_2599_;
goto v___jp_2594_;
}
}
}
else
{
lean_del_object(v___x_2583_);
lean_dec_ref(v_scopeChangedDecls_2581_);
lean_dec(v_activeScopes_2578_);
lean_dec(v_state_2577_);
lean_dec(v_tail_2576_);
lean_dec_ref(v_scopedEntries_2575_);
lean_dec(v_namespaceName_2565_);
lean_dec_ref(v_ext_2563_);
return v_env_2564_;
}
}
}
else
{
lean_dec(v_stateStack_2573_);
lean_dec(v_s_2572_);
lean_dec(v_namespaceName_2565_);
lean_dec_ref(v_ext_2563_);
return v_env_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2617_, lean_object* v_00_u03b2_2618_, lean_object* v_00_u03c3_2619_, lean_object* v_ext_2620_, lean_object* v_env_2621_, lean_object* v_namespaceName_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2620_, v_env_2621_, v_namespaceName_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2624_, lean_object* v_val_2625_, lean_object* v_t_2626_, lean_object* v_init_2627_, lean_object* v_start_2628_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2625_, v_t_2626_, v_init_2627_, v_start_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2630_, lean_object* v_val_2631_, lean_object* v_t_2632_, lean_object* v_init_2633_, lean_object* v_start_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2630_, v_val_2631_, v_t_2632_, v_init_2633_, v_start_2634_);
lean_dec(v_start_2634_);
lean_dec_ref(v_t_2632_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(lean_object* v_00_u03b2_2636_, lean_object* v_00_u03c3_2637_, lean_object* v_00_u03b1_2638_, lean_object* v_ext_2639_, lean_object* v_t_2640_, lean_object* v_init_2641_, lean_object* v_start_2642_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2639_, v_t_2640_, v_init_2641_, v_start_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___boxed(lean_object* v_00_u03b2_2644_, lean_object* v_00_u03c3_2645_, lean_object* v_00_u03b1_2646_, lean_object* v_ext_2647_, lean_object* v_t_2648_, lean_object* v_init_2649_, lean_object* v_start_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(v_00_u03b2_2644_, v_00_u03c3_2645_, v_00_u03b1_2646_, v_ext_2647_, v_t_2648_, v_init_2649_, v_start_2650_);
lean_dec(v_start_2650_);
lean_dec_ref(v_t_2648_);
return v_res_2651_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2652_, lean_object* v_val_2653_, lean_object* v_x_2654_, size_t v_x_2655_, size_t v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2653_, v_x_2654_, v_x_2655_, v_x_2656_, v_x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2653_ = stack[1].m_obj;
lean_object* v_x_2654_ = stack[2].m_obj;
size_t v_x_2655_ = stack[3].m_num;
size_t v_x_2656_ = stack[4].m_num;
lean_object* v_x_2657_ = stack[5].m_obj;
lean_object* v_res_2659_;
v_res_2659_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_box(0), v_val_2653_, v_x_2654_, v_x_2655_, v_x_2656_, v_x_2657_);
stack->m_obj
 = v_res_2659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2660_, lean_object* v_val_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_){
_start:
{
size_t v_x_3259__boxed_2666_; size_t v_x_3260__boxed_2667_; lean_object* v_res_2668_; 
v_x_3259__boxed_2666_ = lean_unbox_usize(v_x_2663_);
lean_dec(v_x_2663_);
v_x_3260__boxed_2667_ = lean_unbox_usize(v_x_2664_);
lean_dec(v_x_2664_);
v_res_2668_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2660_, v_val_2661_, v_x_2662_, v_x_3259__boxed_2666_, v_x_3260__boxed_2667_, v_x_2665_);
lean_dec_ref(v_x_2662_);
return v_res_2668_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2669_, lean_object* v_val_2670_, lean_object* v_as_2671_, size_t v_i_2672_, size_t v_stop_2673_, lean_object* v_b_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2670_, v_as_2671_, v_i_2672_, v_stop_2673_, v_b_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2670_ = stack[1].m_obj;
lean_object* v_as_2671_ = stack[2].m_obj;
size_t v_i_2672_ = stack[3].m_num;
size_t v_stop_2673_ = stack[4].m_num;
lean_object* v_b_2674_ = stack[5].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_box(0), v_val_2670_, v_as_2671_, v_i_2672_, v_stop_2673_, v_b_2674_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_val_2678_, lean_object* v_as_2679_, lean_object* v_i_2680_, lean_object* v_stop_2681_, lean_object* v_b_2682_){
_start:
{
size_t v_i_boxed_2683_; size_t v_stop_boxed_2684_; lean_object* v_res_2685_; 
v_i_boxed_2683_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_stop_boxed_2684_ = lean_unbox_usize(v_stop_2681_);
lean_dec(v_stop_2681_);
v_res_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2677_, v_val_2678_, v_as_2679_, v_i_boxed_2683_, v_stop_boxed_2684_, v_b_2682_);
lean_dec_ref(v_as_2679_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object* v_00_u03b2_2686_, lean_object* v_val_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2687_, v_x_2688_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2691_, lean_object* v_val_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(v_00_u03b2_2691_, v_val_2692_, v_x_2693_, v_x_2694_);
lean_dec_ref(v_x_2693_);
return v_res_2695_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_object* v_00_u03b2_2696_, lean_object* v_00_u03c3_2697_, lean_object* v_00_u03b1_2698_, lean_object* v_ext_2699_, lean_object* v_x_2700_, size_t v_x_2701_, size_t v_x_2702_, lean_object* v_x_2703_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2699_, v_x_2700_, v_x_2701_, v_x_2702_, v_x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2699_ = stack[3].m_obj;
lean_object* v_x_2700_ = stack[4].m_obj;
size_t v_x_2701_ = stack[5].m_num;
size_t v_x_2702_ = stack[6].m_num;
lean_object* v_x_2703_ = stack[7].m_obj;
lean_object* v_res_2705_;
v_res_2705_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_box(0), lean_box(0), lean_box(0), v_ext_2699_, v_x_2700_, v_x_2701_, v_x_2702_, v_x_2703_);
stack->m_obj
 = v_res_2705_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2706_, lean_object* v_00_u03c3_2707_, lean_object* v_00_u03b1_2708_, lean_object* v_ext_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_){
_start:
{
size_t v_x_3312__boxed_2714_; size_t v_x_3313__boxed_2715_; lean_object* v_res_2716_; 
v_x_3312__boxed_2714_ = lean_unbox_usize(v_x_2711_);
lean_dec(v_x_2711_);
v_x_3313__boxed_2715_ = lean_unbox_usize(v_x_2712_);
lean_dec(v_x_2712_);
v_res_2716_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(v_00_u03b2_2706_, v_00_u03c3_2707_, v_00_u03b1_2708_, v_ext_2709_, v_x_2710_, v_x_3312__boxed_2714_, v_x_3313__boxed_2715_, v_x_2713_);
lean_dec_ref(v_x_2710_);
return v_res_2716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_object* v_00_u03b2_2717_, lean_object* v_00_u03c3_2718_, lean_object* v_00_u03b1_2719_, lean_object* v_ext_2720_, lean_object* v_as_2721_, size_t v_i_2722_, size_t v_stop_2723_, lean_object* v_b_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2720_, v_as_2721_, v_i_2722_, v_stop_2723_, v_b_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2720_ = stack[3].m_obj;
lean_object* v_as_2721_ = stack[4].m_obj;
size_t v_i_2722_ = stack[5].m_num;
size_t v_stop_2723_ = stack[6].m_num;
lean_object* v_b_2724_ = stack[7].m_obj;
lean_object* v_res_2726_;
v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_box(0), lean_box(0), lean_box(0), v_ext_2720_, v_as_2721_, v_i_2722_, v_stop_2723_, v_b_2724_);
stack->m_obj
 = v_res_2726_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2727_, lean_object* v_00_u03c3_2728_, lean_object* v_00_u03b1_2729_, lean_object* v_ext_2730_, lean_object* v_as_2731_, lean_object* v_i_2732_, lean_object* v_stop_2733_, lean_object* v_b_2734_){
_start:
{
size_t v_i_boxed_2735_; size_t v_stop_boxed_2736_; lean_object* v_res_2737_; 
v_i_boxed_2735_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_stop_boxed_2736_ = lean_unbox_usize(v_stop_2733_);
lean_dec(v_stop_2733_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(v_00_u03b2_2727_, v_00_u03c3_2728_, v_00_u03b1_2729_, v_ext_2730_, v_as_2731_, v_i_boxed_2735_, v_stop_boxed_2736_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(lean_object* v_00_u03b2_2738_, lean_object* v_00_u03c3_2739_, lean_object* v_00_u03b1_2740_, lean_object* v_ext_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2741_, v_x_2742_, v_x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2745_, lean_object* v_00_u03c3_2746_, lean_object* v_00_u03b1_2747_, lean_object* v_ext_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(v_00_u03b2_2745_, v_00_u03c3_2746_, v_00_u03b1_2747_, v_ext_2748_, v_x_2749_, v_x_2750_);
lean_dec_ref(v_x_2749_);
return v_res_2751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2752_, lean_object* v_val_2753_, lean_object* v_as_2754_, size_t v_i_2755_, size_t v_stop_2756_, lean_object* v_b_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2753_, v_as_2754_, v_i_2755_, v_stop_2756_, v_b_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2753_ = stack[1].m_obj;
lean_object* v_as_2754_ = stack[2].m_obj;
size_t v_i_2755_ = stack[3].m_num;
size_t v_stop_2756_ = stack[4].m_num;
lean_object* v_b_2757_ = stack[5].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_box(0), v_val_2753_, v_as_2754_, v_i_2755_, v_stop_2756_, v_b_2757_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2760_, lean_object* v_val_2761_, lean_object* v_as_2762_, lean_object* v_i_2763_, lean_object* v_stop_2764_, lean_object* v_b_2765_){
_start:
{
size_t v_i_boxed_2766_; size_t v_stop_boxed_2767_; lean_object* v_res_2768_; 
v_i_boxed_2766_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_stop_boxed_2767_ = lean_unbox_usize(v_stop_2764_);
lean_dec(v_stop_2764_);
v_res_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2760_, v_val_2761_, v_as_2762_, v_i_boxed_2766_, v_stop_boxed_2767_, v_b_2765_);
lean_dec_ref(v_as_2762_);
return v_res_2768_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_2769_, lean_object* v_00_u03c3_2770_, lean_object* v_00_u03b1_2771_, lean_object* v_ext_2772_, lean_object* v_as_2773_, size_t v_i_2774_, size_t v_stop_2775_, lean_object* v_b_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2772_, v_as_2773_, v_i_2774_, v_stop_2775_, v_b_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2772_ = stack[3].m_obj;
lean_object* v_as_2773_ = stack[4].m_obj;
size_t v_i_2774_ = stack[5].m_num;
size_t v_stop_2775_ = stack[6].m_num;
lean_object* v_b_2776_ = stack[7].m_obj;
lean_object* v_res_2778_;
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_box(0), lean_box(0), lean_box(0), v_ext_2772_, v_as_2773_, v_i_2774_, v_stop_2775_, v_b_2776_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2779_, lean_object* v_00_u03c3_2780_, lean_object* v_00_u03b1_2781_, lean_object* v_ext_2782_, lean_object* v_as_2783_, lean_object* v_i_2784_, lean_object* v_stop_2785_, lean_object* v_b_2786_){
_start:
{
size_t v_i_boxed_2787_; size_t v_stop_boxed_2788_; lean_object* v_res_2789_; 
v_i_boxed_2787_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_stop_boxed_2788_ = lean_unbox_usize(v_stop_2785_);
lean_dec(v_stop_2785_);
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(v_00_u03b2_2779_, v_00_u03c3_2780_, v_00_u03b1_2781_, v_ext_2782_, v_as_2783_, v_i_boxed_2787_, v_stop_boxed_2788_, v_b_2786_);
lean_dec_ref(v_as_2783_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2790_, lean_object* v_descr_2791_, lean_object* v_ps_2792_){
_start:
{
lean_object* v_state_2793_; lean_object* v_stateStack_2794_; 
v_state_2793_ = lean_ctor_get(v_ps_2792_, 1);
lean_inc(v_state_2793_);
v_stateStack_2794_ = lean_ctor_get(v_state_2793_, 0);
lean_inc(v_stateStack_2794_);
if (lean_obj_tag(v_stateStack_2794_) == 1)
{
lean_object* v_head_2795_; lean_object* v_importedEntries_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2838_; 
v_head_2795_ = lean_ctor_get(v_stateStack_2794_, 0);
lean_inc(v_head_2795_);
v_importedEntries_2796_ = lean_ctor_get(v_ps_2792_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_ps_2792_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v_ps_2792_, 1);
lean_dec(v_unused_2839_);
v___x_2798_ = v_ps_2792_;
v_isShared_2799_ = v_isSharedCheck_2838_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_importedEntries_2796_);
lean_dec(v_ps_2792_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2838_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v_scopedEntries_2800_; lean_object* v_newEntries_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2836_; 
v_scopedEntries_2800_ = lean_ctor_get(v_state_2793_, 1);
v_newEntries_2801_ = lean_ctor_get(v_state_2793_, 2);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_state_2793_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v_state_2793_, 0);
lean_dec(v_unused_2837_);
v___x_2803_ = v_state_2793_;
v_isShared_2804_ = v_isSharedCheck_2836_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_newEntries_2801_);
lean_inc(v_scopedEntries_2800_);
lean_dec(v_state_2793_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2836_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v_tail_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2834_; 
v_tail_2805_ = lean_ctor_get(v_stateStack_2794_, 1);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_stateStack_2794_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v_stateStack_2794_, 0);
lean_dec(v_unused_2835_);
v___x_2807_ = v_stateStack_2794_;
v_isShared_2808_ = v_isSharedCheck_2834_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_tail_2805_);
lean_dec(v_stateStack_2794_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2834_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_state_2809_; lean_object* v_activeScopes_2810_; uint8_t v_delimitsLocal_2811_; uint8_t v_scopeChanged_2812_; lean_object* v_scopeChangedDecls_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2833_; 
v_state_2809_ = lean_ctor_get(v_head_2795_, 0);
v_activeScopes_2810_ = lean_ctor_get(v_head_2795_, 1);
v_delimitsLocal_2811_ = lean_ctor_get_uint8(v_head_2795_, sizeof(void*)*3);
v_scopeChanged_2812_ = lean_ctor_get_uint8(v_head_2795_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2813_ = lean_ctor_get(v_head_2795_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_head_2795_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2815_ = v_head_2795_;
v_isShared_2816_ = v_isSharedCheck_2833_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_scopeChangedDecls_2813_);
lean_inc(v_activeScopes_2810_);
lean_inc(v_state_2809_);
lean_dec(v_head_2795_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2833_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
uint8_t v___y_2818_; 
if (v_scopeChanged_2812_ == 0)
{
uint8_t v___x_2832_; 
v___x_2832_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_2791_);
v___y_2818_ = v___x_2832_;
goto v___jp_2817_;
}
else
{
v___y_2818_ = v_scopeChanged_2812_;
goto v___jp_2817_;
}
v___jp_2817_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_apply_1(v_f_2790_, v_state_2809_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2819_);
v___x_2821_ = v___x_2815_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_activeScopes_2810_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_scopeChangedDecls_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2831_, sizeof(void*)*3, v_delimitsLocal_2811_);
v___x_2821_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*3 + 1, v___y_2818_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2821_);
v___x_2823_ = v___x_2807_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_tail_2805_);
v___x_2823_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2823_);
v___x_2825_ = v___x_2803_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_scopedEntries_2800_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_newEntries_2801_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 1, v___x_2825_);
v___x_2827_ = v___x_2798_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_importedEntries_2796_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_importedEntries_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_stateStack_2794_);
lean_dec(v_f_2790_);
v_importedEntries_2840_ = lean_ctor_get(v_ps_2792_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_ps_2792_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_ps_2792_, 1);
lean_dec(v_unused_2848_);
v___x_2842_ = v_ps_2792_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_importedEntries_2840_);
lean_dec(v_ps_2792_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_importedEntries_2840_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_state_2793_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object* v_f_2849_, lean_object* v_descr_2850_, lean_object* v_ps_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(v_f_2849_, v_descr_2850_, v_ps_2851_);
lean_dec_ref(v_descr_2850_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2853_, lean_object* v_env_2854_, lean_object* v_f_2855_){
_start:
{
lean_object* v_ext_2856_; lean_object* v_toEnvExtension_2857_; lean_object* v_descr_2858_; lean_object* v_asyncMode_2859_; uint8_t v_logWrites_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_ext_2856_ = lean_ctor_get(v_ext_2853_, 1);
v_toEnvExtension_2857_ = lean_ctor_get(v_ext_2856_, 0);
lean_inc_ref(v_toEnvExtension_2857_);
v_descr_2858_ = lean_ctor_get(v_ext_2853_, 0);
lean_inc_ref(v_descr_2858_);
lean_dec_ref(v_ext_2853_);
v_asyncMode_2859_ = lean_ctor_get(v_toEnvExtension_2857_, 2);
lean_inc(v_asyncMode_2859_);
v_logWrites_2860_ = lean_ctor_get_uint8(v_toEnvExtension_2857_, sizeof(void*)*6);
v___f_2861_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2861_, 0, v_f_2855_);
lean_closure_set(v___f_2861_, 1, v_descr_2858_);
v___x_2862_ = lean_box(0);
v___x_2863_ = 1;
if (v_logWrites_2860_ == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2857_, v_env_2854_, v___f_2861_, v_asyncMode_2859_, v___x_2862_, v___x_2863_);
lean_dec(v_asyncMode_2859_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_inc_ref(v_toEnvExtension_2857_);
v___x_2865_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2857_, v_env_2854_);
lean_dec_ref(v_env_2854_);
v___x_2866_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2857_, v___x_2865_, v___f_2861_, v_asyncMode_2859_, v___x_2862_, v___x_2863_);
lean_dec(v_asyncMode_2859_);
return v___x_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2867_, lean_object* v_00_u03b2_2868_, lean_object* v_00_u03c3_2869_, lean_object* v_ext_2870_, lean_object* v_env_2871_, lean_object* v_f_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2870_, v_env_2871_, v_f_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2874_, lean_object* v_____s_2875_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_apply_2(v_toPure_2874_, lean_box(0), v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2878_, lean_object* v_toPure_2879_, lean_object* v_r_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
v___x_2882_ = lean_apply_2(v_toPure_2879_, lean_box(0), v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2883_, lean_object* v_toBind_2884_, lean_object* v___f_2885_, lean_object* v_a_2886_, lean_object* v_x_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_modifyEnv_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_modifyEnv_2889_ = lean_ctor_get(v_inst_2883_, 1);
lean_inc(v_modifyEnv_2889_);
lean_dec_ref(v_inst_2883_);
v___x_2890_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2890_, 0, lean_box(0));
lean_closure_set(v___x_2890_, 1, lean_box(0));
lean_closure_set(v___x_2890_, 2, lean_box(0));
lean_closure_set(v___x_2890_, 3, v_a_2886_);
v___x_2891_ = lean_apply_1(v_modifyEnv_2889_, v___x_2890_);
v___x_2892_ = lean_apply_4(v_toBind_2884_, lean_box(0), lean_box(0), v___x_2891_, v___f_2885_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2893_, lean_object* v_inst_2894_, lean_object* v_toBind_2895_, lean_object* v_inst_2896_, lean_object* v___f_2897_, lean_object* v_____do__lift_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___f_2900_; lean_object* v___f_2901_; size_t v_sz_2902_; size_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2899_ = lean_box(0);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2900_, 0, v___x_2899_);
lean_closure_set(v___f_2900_, 1, v_toPure_2893_);
lean_inc(v_toBind_2895_);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2901_, 0, v_inst_2894_);
lean_closure_set(v___f_2901_, 1, v_toBind_2895_);
lean_closure_set(v___f_2901_, 2, v___f_2900_);
v_sz_2902_ = lean_array_size(v_____do__lift_2898_);
v___x_2903_ = ((size_t)0ULL);
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2896_, v_____do__lift_2898_, v___f_2901_, v_sz_2902_, v___x_2903_, v___x_2899_);
v___x_2905_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2904_, v___f_2897_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = l_Lean_scopedEnvExtensionsRef;
v___x_2907_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2907_, 0, lean_box(0));
lean_closure_set(v___x_2907_, 1, lean_box(0));
lean_closure_set(v___x_2907_, 2, v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_){
_start:
{
lean_object* v_toApplicative_2911_; lean_object* v_toBind_2912_; lean_object* v_toPure_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; 
v_toApplicative_2911_ = lean_ctor_get(v_inst_2908_, 0);
v_toBind_2912_ = lean_ctor_get(v_inst_2908_, 1);
lean_inc_n(v_toBind_2912_, 2);
v_toPure_2913_ = lean_ctor_get(v_toApplicative_2911_, 1);
lean_inc_n(v_toPure_2913_, 2);
v___x_2914_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2915_ = lean_apply_2(v_inst_2910_, lean_box(0), v___x_2914_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2916_, 0, v_toPure_2913_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2917_, 0, v_toPure_2913_);
lean_closure_set(v___f_2917_, 1, v_inst_2909_);
lean_closure_set(v___f_2917_, 2, v_toBind_2912_);
lean_closure_set(v___f_2917_, 3, v_inst_2908_);
lean_closure_set(v___f_2917_, 4, v___f_2916_);
v___x_2918_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v___x_2915_, v___f_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_pushScope___redArg(v_inst_2920_, v_inst_2921_, v_inst_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2924_, lean_object* v_toBind_2925_, lean_object* v___f_2926_, lean_object* v_a_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_modifyEnv_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_modifyEnv_2930_ = lean_ctor_get(v_inst_2924_, 1);
lean_inc(v_modifyEnv_2930_);
lean_dec_ref(v_inst_2924_);
v___x_2931_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2931_, 0, lean_box(0));
lean_closure_set(v___x_2931_, 1, lean_box(0));
lean_closure_set(v___x_2931_, 2, lean_box(0));
lean_closure_set(v___x_2931_, 3, v_a_2927_);
v___x_2932_ = lean_apply_1(v_modifyEnv_2930_, v___x_2931_);
v___x_2933_ = lean_apply_4(v_toBind_2925_, lean_box(0), lean_box(0), v___x_2932_, v___f_2926_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2934_, lean_object* v_inst_2935_, lean_object* v_toBind_2936_, lean_object* v_inst_2937_, lean_object* v___f_2938_, lean_object* v_____do__lift_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; size_t v_sz_2943_; size_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2940_ = lean_box(0);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2941_, 0, v___x_2940_);
lean_closure_set(v___f_2941_, 1, v_toPure_2934_);
lean_inc(v_toBind_2936_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2942_, 0, v_inst_2935_);
lean_closure_set(v___f_2942_, 1, v_toBind_2936_);
lean_closure_set(v___f_2942_, 2, v___f_2941_);
v_sz_2943_ = lean_array_size(v_____do__lift_2939_);
v___x_2944_ = ((size_t)0ULL);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2937_, v_____do__lift_2939_, v___f_2942_, v_sz_2943_, v___x_2944_, v___x_2940_);
v___x_2946_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v___x_2945_, v___f_2938_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_){
_start:
{
lean_object* v_toApplicative_2950_; lean_object* v_toBind_2951_; lean_object* v_toPure_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___x_2957_; 
v_toApplicative_2950_ = lean_ctor_get(v_inst_2947_, 0);
v_toBind_2951_ = lean_ctor_get(v_inst_2947_, 1);
lean_inc_n(v_toBind_2951_, 2);
v_toPure_2952_ = lean_ctor_get(v_toApplicative_2950_, 1);
lean_inc_n(v_toPure_2952_, 2);
v___x_2953_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2954_ = lean_apply_2(v_inst_2949_, lean_box(0), v___x_2953_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2955_, 0, v_toPure_2952_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2956_, 0, v_toPure_2952_);
lean_closure_set(v___f_2956_, 1, v_inst_2948_);
lean_closure_set(v___f_2956_, 2, v_toBind_2951_);
lean_closure_set(v___f_2956_, 3, v_inst_2947_);
lean_closure_set(v___f_2956_, 4, v___f_2955_);
v___x_2957_ = lean_apply_4(v_toBind_2951_, lean_box(0), lean_box(0), v___x_2954_, v___f_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_popScope___redArg(v_inst_2959_, v_inst_2960_, v_inst_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2963_, lean_object* v_depth_2964_, lean_object* v_x_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2963_, v_x_2965_, v_depth_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2967_, lean_object* v_depth_2968_, lean_object* v_toBind_2969_, lean_object* v___f_2970_, lean_object* v_a_2971_, lean_object* v_x_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_modifyEnv_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_modifyEnv_2974_ = lean_ctor_get(v_inst_2967_, 1);
lean_inc(v_modifyEnv_2974_);
lean_dec_ref(v_inst_2967_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2975_, 0, v_a_2971_);
lean_closure_set(v___f_2975_, 1, v_depth_2968_);
v___x_2976_ = lean_apply_1(v_modifyEnv_2974_, v___f_2975_);
v___x_2977_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2976_, v___f_2970_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2978_, lean_object* v_inst_2979_, lean_object* v_depth_2980_, lean_object* v_toBind_2981_, lean_object* v_inst_2982_, lean_object* v___f_2983_, lean_object* v_____do__lift_2984_){
_start:
{
lean_object* v___x_2985_; lean_object* v___f_2986_; lean_object* v___f_2987_; size_t v_sz_2988_; size_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2985_ = lean_box(0);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2986_, 0, v___x_2985_);
lean_closure_set(v___f_2986_, 1, v_toPure_2978_);
lean_inc(v_toBind_2981_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2987_, 0, v_inst_2979_);
lean_closure_set(v___f_2987_, 1, v_depth_2980_);
lean_closure_set(v___f_2987_, 2, v_toBind_2981_);
lean_closure_set(v___f_2987_, 3, v___f_2986_);
v_sz_2988_ = lean_array_size(v_____do__lift_2984_);
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2982_, v_____do__lift_2984_, v___f_2987_, v_sz_2988_, v___x_2989_, v___x_2985_);
v___x_2991_ = lean_apply_4(v_toBind_2981_, lean_box(0), lean_box(0), v___x_2990_, v___f_2983_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_depth_2995_){
_start:
{
lean_object* v_toApplicative_2996_; lean_object* v_toBind_2997_; lean_object* v_toPure_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___f_3002_; lean_object* v___x_3003_; 
v_toApplicative_2996_ = lean_ctor_get(v_inst_2992_, 0);
v_toBind_2997_ = lean_ctor_get(v_inst_2992_, 1);
lean_inc_n(v_toBind_2997_, 2);
v_toPure_2998_ = lean_ctor_get(v_toApplicative_2996_, 1);
lean_inc_n(v_toPure_2998_, 2);
v___x_2999_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_3000_ = lean_apply_2(v_inst_2994_, lean_box(0), v___x_2999_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3001_, 0, v_toPure_2998_);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3002_, 0, v_toPure_2998_);
lean_closure_set(v___f_3002_, 1, v_inst_2993_);
lean_closure_set(v___f_3002_, 2, v_depth_2995_);
lean_closure_set(v___f_3002_, 3, v_toBind_2997_);
lean_closure_set(v___f_3002_, 4, v_inst_2992_);
lean_closure_set(v___f_3002_, 5, v___f_3001_);
v___x_3003_ = lean_apply_4(v_toBind_2997_, lean_box(0), lean_box(0), v___x_3000_, v___f_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_depth_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_setDelimitsLocal___redArg(v_inst_3005_, v_inst_3006_, v_inst_3007_, v_depth_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_3010_, lean_object* v_namespaceName_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_3010_, v_x_3012_, v_namespaceName_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_3014_, lean_object* v_namespaceName_3015_, lean_object* v_toBind_3016_, lean_object* v___f_3017_, lean_object* v_a_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_modifyEnv_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_modifyEnv_3021_ = lean_ctor_get(v_inst_3014_, 1);
lean_inc(v_modifyEnv_3021_);
lean_dec_ref(v_inst_3014_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3022_, 0, v_a_3018_);
lean_closure_set(v___f_3022_, 1, v_namespaceName_3015_);
v___x_3023_ = lean_apply_1(v_modifyEnv_3021_, v___f_3022_);
v___x_3024_ = lean_apply_4(v_toBind_3016_, lean_box(0), lean_box(0), v___x_3023_, v___f_3017_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_3025_, lean_object* v_inst_3026_, lean_object* v_namespaceName_3027_, lean_object* v_toBind_3028_, lean_object* v_inst_3029_, lean_object* v___f_3030_, lean_object* v_____do__lift_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; size_t v_sz_3035_; size_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3032_ = lean_box(0);
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3033_, 0, v___x_3032_);
lean_closure_set(v___f_3033_, 1, v_toPure_3025_);
lean_inc(v_toBind_3028_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_3034_, 0, v_inst_3026_);
lean_closure_set(v___f_3034_, 1, v_namespaceName_3027_);
lean_closure_set(v___f_3034_, 2, v_toBind_3028_);
lean_closure_set(v___f_3034_, 3, v___f_3033_);
v_sz_3035_ = lean_array_size(v_____do__lift_3031_);
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3029_, v_____do__lift_3031_, v___f_3034_, v_sz_3035_, v___x_3036_, v___x_3032_);
v___x_3038_ = lean_apply_4(v_toBind_3028_, lean_box(0), lean_box(0), v___x_3037_, v___f_3030_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_namespaceName_3042_){
_start:
{
lean_object* v_toApplicative_3043_; lean_object* v_toBind_3044_; lean_object* v_toPure_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; 
v_toApplicative_3043_ = lean_ctor_get(v_inst_3039_, 0);
v_toBind_3044_ = lean_ctor_get(v_inst_3039_, 1);
lean_inc_n(v_toBind_3044_, 2);
v_toPure_3045_ = lean_ctor_get(v_toApplicative_3043_, 1);
lean_inc_n(v_toPure_3045_, 2);
v___x_3046_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_3047_ = lean_apply_2(v_inst_3041_, lean_box(0), v___x_3046_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3048_, 0, v_toPure_3045_);
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3049_, 0, v_toPure_3045_);
lean_closure_set(v___f_3049_, 1, v_inst_3040_);
lean_closure_set(v___f_3049_, 2, v_namespaceName_3042_);
lean_closure_set(v___f_3049_, 3, v_toBind_3044_);
lean_closure_set(v___f_3049_, 4, v_inst_3039_);
lean_closure_set(v___f_3049_, 5, v___f_3048_);
v___x_3050_ = lean_apply_4(v_toBind_3044_, lean_box(0), lean_box(0), v___x_3047_, v___f_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_namespaceName_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_activateScoped___redArg(v_inst_3052_, v_inst_3053_, v_inst_3054_, v_namespaceName_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_3058_){
_start:
{
lean_inc(v___y_3058_);
return v___y_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_3059_);
lean_dec(v___y_3059_);
return v_res_3060_;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_3061_, lean_object* v_a_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_a_3062_);
return v___x_3065_;
}
}
LEAN_EXPORT void l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3061_ = stack[0].m_obj;
lean_object* v_a_3062_ = stack[1].m_obj;
lean_object* v___y_3063_ = stack[2].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_3061_, v_a_3062_, v___y_3063_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_3067_, lean_object* v_a_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_3067_, v_a_3068_, v___y_3069_);
lean_dec_ref(v___y_3069_);
lean_dec(v_x_3067_);
return v_res_3071_;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_initial_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT void l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_initial_3072_ = stack[0].m_obj;
lean_object* v_res_3075_;
v_res_3075_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_3072_);
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_3076_);
return v_res_3078_;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_3081_){
_start:
{
lean_object* v_name_3083_; lean_object* v_addEntry_3084_; lean_object* v_initial_3085_; lean_object* v_finalizeImport_3086_; lean_object* v_exportEntry_x3f_3087_; uint8_t v_trackGen_3088_; uint8_t v_logWrites_3089_; lean_object* v_entryDecl_x3f_3090_; lean_object* v___f_3091_; lean_object* v___f_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_name_3083_ = lean_ctor_get(v_descr_3081_, 0);
lean_inc(v_name_3083_);
v_addEntry_3084_ = lean_ctor_get(v_descr_3081_, 1);
lean_inc(v_addEntry_3084_);
v_initial_3085_ = lean_ctor_get(v_descr_3081_, 2);
lean_inc(v_initial_3085_);
v_finalizeImport_3086_ = lean_ctor_get(v_descr_3081_, 3);
lean_inc(v_finalizeImport_3086_);
v_exportEntry_x3f_3087_ = lean_ctor_get(v_descr_3081_, 4);
lean_inc_ref(v_exportEntry_x3f_3087_);
v_trackGen_3088_ = lean_ctor_get_uint8(v_descr_3081_, sizeof(void*)*6);
v_logWrites_3089_ = lean_ctor_get_uint8(v_descr_3081_, sizeof(void*)*6 + 1);
v_entryDecl_x3f_3090_ = lean_ctor_get(v_descr_3081_, 5);
lean_inc(v_entryDecl_x3f_3090_);
lean_dec_ref(v_descr_3081_);
v___f_3091_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_3092_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3093_, 0, v_initial_3085_);
v___x_3094_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3094_, 0, v_name_3083_);
lean_ctor_set(v___x_3094_, 1, v___f_3093_);
lean_ctor_set(v___x_3094_, 2, v___f_3092_);
lean_ctor_set(v___x_3094_, 3, v___f_3091_);
lean_ctor_set(v___x_3094_, 4, v_addEntry_3084_);
lean_ctor_set(v___x_3094_, 5, v_finalizeImport_3086_);
lean_ctor_set(v___x_3094_, 6, v_exportEntry_x3f_3087_);
lean_ctor_set(v___x_3094_, 7, v_entryDecl_x3f_3090_);
lean_ctor_set_uint8(v___x_3094_, sizeof(void*)*8, v_trackGen_3088_);
lean_ctor_set_uint8(v___x_3094_, sizeof(void*)*8 + 1, v_logWrites_3089_);
v___x_3095_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT void l_Lean_registerSimpleScopedEnvExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_3081_ = stack[0].m_obj;
lean_object* v_res_3096_;
v_res_3096_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3081_);
stack->m_obj
 = v_res_3096_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3097_);
return v_res_3099_;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_3100_, lean_object* v_00_u03c3_3101_, lean_object* v_descr_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT void l_Lean_registerSimpleScopedEnvExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_descr_3102_ = stack[2].m_obj;
lean_object* v_res_3105_;
v_res_3105_ = l_Lean_registerSimpleScopedEnvExtension(lean_box(0), lean_box(0), v_descr_3102_);
stack->m_obj
 = v_res_3105_;
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_00_u03c3_3107_, lean_object* v_descr_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_3106_, v_00_u03c3_3107_, v_descr_3108_);
return v_res_3110_;
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
