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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
return v_res_66_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_object* v_00_u03b2_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg(){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg___boxed(lean_object* v___dummy_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___redArg();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* v_a_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___closed__0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v_res_82_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_00_u03c3_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg(){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack___redArg();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_123_ = l_Lean_mkAtom(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_125_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_136_ = l_Lean_mkAtom(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_138_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_139_ = lean_array_push(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_141_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_142_ = lean_box(2);
v___x_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_145_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_148_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_149_ = lean_box(2);
v___x_150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_147_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_152_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_153_ = lean_array_push(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_155_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_156_ = lean_box(2);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_154_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_159_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_162_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_166_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_169_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(lean_object* v_descr_173_){
_start:
{
uint8_t v_trackGen_174_; 
v_trackGen_174_ = lean_ctor_get_uint8(v_descr_173_, sizeof(void*)*8);
if (v_trackGen_174_ == 0)
{
uint8_t v_logWrites_175_; 
v_logWrites_175_ = lean_ctor_get_uint8(v_descr_173_, sizeof(void*)*8 + 1);
return v_logWrites_175_;
}
else
{
return v_trackGen_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg___boxed(lean_object* v_descr_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_176_);
lean_dec_ref(v_descr_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_00_u03c3_181_, lean_object* v_descr_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___boxed(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_00_u03c3_186_, lean_object* v_descr_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes(v_00_u03b1_184_, v_00_u03b2_185_, v_00_u03c3_186_, v_descr_187_);
lean_dec_ref(v_descr_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object* v_descr_190_, lean_object* v_s_191_, lean_object* v_b_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_190_);
if (v___x_193_ == 0)
{
lean_dec(v_b_192_);
lean_dec_ref(v_descr_190_);
return v_s_191_;
}
else
{
lean_object* v_entryDecl_x3f_194_; 
v_entryDecl_x3f_194_ = lean_ctor_get(v_descr_190_, 7);
lean_inc(v_entryDecl_x3f_194_);
lean_dec_ref(v_descr_190_);
if (lean_obj_tag(v_entryDecl_x3f_194_) == 0)
{
lean_object* v_state_195_; lean_object* v_activeScopes_196_; uint8_t v_delimitsLocal_197_; lean_object* v_scopeChangedDecls_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_b_192_);
v_state_195_ = lean_ctor_get(v_s_191_, 0);
v_activeScopes_196_ = lean_ctor_get(v_s_191_, 1);
v_delimitsLocal_197_ = lean_ctor_get_uint8(v_s_191_, sizeof(void*)*3);
v_scopeChangedDecls_198_ = lean_ctor_get(v_s_191_, 2);
v_isSharedCheck_205_ = !lean_is_exclusive(v_s_191_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v_s_191_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_scopeChangedDecls_198_);
lean_inc(v_activeScopes_196_);
lean_inc(v_state_195_);
lean_dec(v_s_191_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_state_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_activeScopes_196_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_scopeChangedDecls_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*3, v_delimitsLocal_197_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3 + 1, v___x_193_);
return v___x_203_;
}
}
}
else
{
lean_object* v_state_206_; lean_object* v_activeScopes_207_; uint8_t v_delimitsLocal_208_; lean_object* v_scopeChangedDecls_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_219_; 
v_state_206_ = lean_ctor_get(v_s_191_, 0);
v_activeScopes_207_ = lean_ctor_get(v_s_191_, 1);
v_delimitsLocal_208_ = lean_ctor_get_uint8(v_s_191_, sizeof(void*)*3);
v_scopeChangedDecls_209_ = lean_ctor_get(v_s_191_, 2);
v_isSharedCheck_219_ = !lean_is_exclusive(v_s_191_);
if (v_isSharedCheck_219_ == 0)
{
v___x_211_ = v_s_191_;
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_scopeChangedDecls_209_);
lean_inc(v_activeScopes_207_);
lean_inc(v_state_206_);
lean_dec(v_s_191_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_val_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v_val_213_ = lean_ctor_get(v_entryDecl_x3f_194_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_entryDecl_x3f_194_, 1);
v___x_214_ = lean_apply_1(v_val_213_, v_b_192_);
v___x_215_ = lean_array_push(v_scopeChangedDecls_209_, v___x_214_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 2, v___x_215_);
v___x_217_ = v___x_211_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_state_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_activeScopes_207_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v___x_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*3, v_delimitsLocal_208_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*3 + 1, v___x_193_);
return v___x_217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_00_u03c3_222_, lean_object* v_descr_223_, lean_object* v_s_224_, lean_object* v_b_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_223_, v_s_224_, v_b_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_236_, v___y_237_, v___y_238_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v_x_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_241_, lean_object* v_x_242_){
_start:
{
lean_inc(v_inst_241_);
return v_inst_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec(v_inst_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_246_, lean_object* v_x_247_){
_start:
{
lean_inc(v_s_246_);
return v_s_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_248_, v_x_249_);
lean_dec(v_x_249_);
lean_dec(v_s_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_a_252_);
lean_inc_ref_n(v___x_253_, 2);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_255_, v_a_256_);
lean_dec_ref(v_x_255_);
return v_res_257_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = l_instInhabitedError;
v___x_262_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_262_, 0, lean_box(0));
lean_closure_set(v___x_262_, 1, lean_box(0));
lean_closure_set(v___x_262_, 2, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___f_265_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_266_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_266_, 0, v_inst_264_);
v___f_267_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_268_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_269_ = lean_box(0);
v___x_270_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_271_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_272_ = 0;
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_274_, 0, v___x_269_);
lean_ctor_set(v___x_274_, 1, v___x_270_);
lean_ctor_set(v___x_274_, 2, v___f_265_);
lean_ctor_set(v___x_274_, 3, v___f_266_);
lean_ctor_set(v___x_274_, 4, v___f_267_);
lean_ctor_set(v___x_274_, 5, v___x_271_);
lean_ctor_set(v___x_274_, 6, v___f_268_);
lean_ctor_set(v___x_274_, 7, v___x_273_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*8, v___x_272_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*8 + 1, v___x_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_00_u03c3_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_282_){
_start:
{
lean_object* v_mkInitial_284_; lean_object* v___x_285_; 
v_mkInitial_284_ = lean_ctor_get(v_descr_282_, 1);
lean_inc_ref(v_mkInitial_284_);
lean_dec_ref(v_descr_282_);
v___x_285_ = lean_apply_1(v_mkInitial_284_, lean_box(0));
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_302_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_302_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_302_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_302_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; uint8_t v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_290_ = l_Lean_NameSet_empty;
v___x_291_ = 1;
v___x_292_ = 0;
v___x_293_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_294_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_294_, 0, v_a_286_);
lean_ctor_set(v___x_294_, 1, v___x_290_);
lean_ctor_set(v___x_294_, 2, v___x_293_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*3, v___x_291_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*3 + 1, v___x_292_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_ctor_set(v___x_298_, 2, v___x_295_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_298_);
v___x_300_ = v___x_288_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_285_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_285_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_00_u03c3_316_, lean_object* v_descr_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_00_u03c3_322_, lean_object* v_descr_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_320_, v_00_u03b2_321_, v_00_u03c3_322_, v_descr_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
lean_object* v_key_329_; lean_object* v_value_330_; lean_object* v_tail_331_; uint8_t v___x_332_; 
v_key_329_ = lean_ctor_get(v_x_327_, 0);
v_value_330_ = lean_ctor_get(v_x_327_, 1);
v_tail_331_ = lean_ctor_get(v_x_327_, 2);
v___x_332_ = lean_name_eq(v_key_329_, v_a_326_);
if (v___x_332_ == 0)
{
v_x_327_ = v_tail_331_;
goto _start;
}
else
{
lean_object* v___x_334_; 
lean_inc(v_value_330_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_value_330_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_335_, v_x_336_);
lean_dec(v_x_336_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_buckets_340_; lean_object* v___x_341_; uint64_t v___y_343_; 
v_buckets_340_ = lean_ctor_get(v_m_338_, 1);
v___x_341_ = lean_array_get_size(v_buckets_340_);
if (lean_obj_tag(v_a_339_) == 0)
{
uint64_t v___x_357_; 
v___x_357_ = 1723ULL;
v___y_343_ = v___x_357_;
goto v___jp_342_;
}
else
{
uint64_t v_hash_358_; 
v_hash_358_ = lean_ctor_get_uint64(v_a_339_, sizeof(void*)*2);
v___y_343_ = v_hash_358_;
goto v___jp_342_;
}
v___jp_342_:
{
uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v_fold_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_344_ = 32ULL;
v___x_345_ = lean_uint64_shift_right(v___y_343_, v___x_344_);
v_fold_346_ = lean_uint64_xor(v___y_343_, v___x_345_);
v___x_347_ = 16ULL;
v___x_348_ = lean_uint64_shift_right(v_fold_346_, v___x_347_);
v___x_349_ = lean_uint64_xor(v_fold_346_, v___x_348_);
v___x_350_ = lean_uint64_to_usize(v___x_349_);
v___x_351_ = lean_usize_of_nat(v___x_341_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_sub(v___x_351_, v___x_352_);
v___x_354_ = lean_usize_land(v___x_350_, v___x_353_);
v___x_355_ = lean_array_uget_borrowed(v_buckets_340_, v___x_354_);
v___x_356_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_339_, v___x_355_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_m_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_i_364_, lean_object* v_k_365_){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_array_get_size(v_keys_362_);
v___x_367_ = lean_nat_dec_lt(v_i_364_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_i_364_);
v___x_368_ = lean_box(0);
return v___x_368_;
}
else
{
lean_object* v_k_x27_369_; uint8_t v___x_370_; 
v_k_x27_369_ = lean_array_fget_borrowed(v_keys_362_, v_i_364_);
v___x_370_ = lean_name_eq(v_k_365_, v_k_x27_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_i_364_, v___x_371_);
lean_dec(v_i_364_);
v_i_364_ = v___x_372_;
goto _start;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_array_fget_borrowed(v_vals_363_, v_i_364_);
lean_dec(v_i_364_);
lean_inc(v___x_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_i_378_, lean_object* v_k_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_376_, v_vals_377_, v_i_378_, v_k_379_);
lean_dec(v_k_379_);
lean_dec_ref(v_vals_377_);
lean_dec_ref(v_keys_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_381_, size_t v_x_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_es_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v_j_388_; lean_object* v___x_389_; 
v_es_384_ = lean_ctor_get(v_x_381_, 0);
v___x_385_ = lean_box(2);
v___x_386_ = ((size_t)31ULL);
v___x_387_ = lean_usize_land(v_x_382_, v___x_386_);
v_j_388_ = lean_usize_to_nat(v___x_387_);
v___x_389_ = lean_array_get_borrowed(v___x_385_, v_es_384_, v_j_388_);
lean_dec(v_j_388_);
switch(lean_obj_tag(v___x_389_))
{
case 0:
{
lean_object* v_key_390_; lean_object* v_val_391_; uint8_t v___x_392_; 
v_key_390_ = lean_ctor_get(v___x_389_, 0);
v_val_391_ = lean_ctor_get(v___x_389_, 1);
v___x_392_ = lean_name_eq(v_x_383_, v_key_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v___x_394_; 
lean_inc(v_val_391_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_val_391_);
return v___x_394_;
}
}
case 1:
{
lean_object* v_node_395_; size_t v___x_396_; size_t v___x_397_; 
v_node_395_ = lean_ctor_get(v___x_389_, 0);
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_usize_shift_right(v_x_382_, v___x_396_);
v_x_381_ = v_node_395_;
v_x_382_ = v___x_397_;
goto _start;
}
default: 
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
}
else
{
lean_object* v_ks_400_; lean_object* v_vs_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_ks_400_ = lean_ctor_get(v_x_381_, 0);
v_vs_401_ = lean_ctor_get(v_x_381_, 1);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_400_, v_vs_401_, v___x_402_, v_x_383_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
size_t v_x_1059__boxed_407_; lean_object* v_res_408_; 
v_x_1059__boxed_407_ = lean_unbox_usize(v_x_405_);
lean_dec(v_x_405_);
v_res_408_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_404_, v_x_1059__boxed_407_, v_x_406_);
lean_dec(v_x_406_);
lean_dec_ref(v_x_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
uint64_t v___y_412_; 
if (lean_obj_tag(v_x_410_) == 0)
{
uint64_t v___x_415_; 
v___x_415_ = 1723ULL;
v___y_412_ = v___x_415_;
goto v___jp_411_;
}
else
{
uint64_t v_hash_416_; 
v_hash_416_ = lean_ctor_get_uint64(v_x_410_, sizeof(void*)*2);
v___y_412_ = v_hash_416_;
goto v___jp_411_;
}
v___jp_411_:
{
size_t v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_uint64_to_usize(v___y_412_);
v___x_414_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_409_, v___x_413_, v_x_410_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_x_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_stage_u2081_422_; 
v_stage_u2081_422_ = lean_ctor_get_uint8(v_x_420_, sizeof(void*)*2);
if (v_stage_u2081_422_ == 0)
{
lean_object* v_map_u2081_423_; lean_object* v_map_u2082_424_; lean_object* v___x_425_; 
v_map_u2081_423_ = lean_ctor_get(v_x_420_, 0);
v_map_u2082_424_ = lean_ctor_get(v_x_420_, 1);
v___x_425_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_424_, v_x_421_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_423_, v_x_421_);
return v___x_426_;
}
else
{
return v___x_425_;
}
}
else
{
lean_object* v_map_u2081_427_; lean_object* v___x_428_; 
v_map_u2081_427_ = lean_ctor_get(v_x_420_, 0);
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_427_, v_x_421_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_x_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_dec(v_b_433_);
lean_dec(v_a_432_);
return v_x_434_;
}
else
{
lean_object* v_key_435_; lean_object* v_value_436_; lean_object* v_tail_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_449_; 
v_key_435_ = lean_ctor_get(v_x_434_, 0);
v_value_436_ = lean_ctor_get(v_x_434_, 1);
v_tail_437_ = lean_ctor_get(v_x_434_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_449_ == 0)
{
v___x_439_ = v_x_434_;
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_tail_437_);
lean_inc(v_value_436_);
lean_inc(v_key_435_);
lean_dec(v_x_434_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = lean_name_eq(v_key_435_, v_a_432_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_432_, v_b_433_, v_tail_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 2, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_key_435_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_value_436_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v_value_436_);
lean_dec(v_key_435_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_b_433_);
lean_ctor_set(v___x_439_, 0, v_a_432_);
v___x_447_ = v___x_439_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_432_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_b_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_tail_437_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
return v_x_450_;
}
else
{
lean_object* v_key_452_; lean_object* v_value_453_; lean_object* v_tail_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_480_; 
v_key_452_ = lean_ctor_get(v_x_451_, 0);
v_value_453_ = lean_ctor_get(v_x_451_, 1);
v_tail_454_ = lean_ctor_get(v_x_451_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_480_ == 0)
{
v___x_456_ = v_x_451_;
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_tail_454_);
lean_inc(v_value_453_);
lean_inc(v_key_452_);
lean_dec(v_x_451_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_480_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; uint64_t v___y_460_; 
v___x_458_ = lean_array_get_size(v_x_450_);
if (lean_obj_tag(v_key_452_) == 0)
{
uint64_t v___x_478_; 
v___x_478_ = 1723ULL;
v___y_460_ = v___x_478_;
goto v___jp_459_;
}
else
{
uint64_t v_hash_479_; 
v_hash_479_ = lean_ctor_get_uint64(v_key_452_, sizeof(void*)*2);
v___y_460_ = v_hash_479_;
goto v___jp_459_;
}
v___jp_459_:
{
uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v_fold_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_461_ = 32ULL;
v___x_462_ = lean_uint64_shift_right(v___y_460_, v___x_461_);
v_fold_463_ = lean_uint64_xor(v___y_460_, v___x_462_);
v___x_464_ = 16ULL;
v___x_465_ = lean_uint64_shift_right(v_fold_463_, v___x_464_);
v___x_466_ = lean_uint64_xor(v_fold_463_, v___x_465_);
v___x_467_ = lean_uint64_to_usize(v___x_466_);
v___x_468_ = lean_usize_of_nat(v___x_458_);
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_sub(v___x_468_, v___x_469_);
v___x_471_ = lean_usize_land(v___x_467_, v___x_470_);
v___x_472_ = lean_array_uget_borrowed(v_x_450_, v___x_471_);
lean_inc(v___x_472_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 2, v___x_472_);
v___x_474_ = v___x_456_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_key_452_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_value_453_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v___x_472_);
v___x_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_array_uset(v_x_450_, v___x_471_, v___x_474_);
v_x_450_ = v___x_475_;
v_x_451_ = v_tail_454_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_481_, lean_object* v_source_482_, lean_object* v_target_483_){
_start:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_array_get_size(v_source_482_);
v___x_485_ = lean_nat_dec_lt(v_i_481_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_source_482_);
lean_dec(v_i_481_);
return v_target_483_;
}
else
{
lean_object* v_es_486_; lean_object* v___x_487_; lean_object* v_source_488_; lean_object* v_target_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_es_486_ = lean_array_fget(v_source_482_, v_i_481_);
v___x_487_ = lean_box(0);
v_source_488_ = lean_array_fset(v_source_482_, v_i_481_, v___x_487_);
v_target_489_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_483_, v_es_486_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_481_, v___x_490_);
lean_dec(v_i_481_);
v_i_481_ = v___x_491_;
v_source_482_ = v_source_488_;
v_target_483_ = v_target_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_nbuckets_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_494_ = lean_array_get_size(v_data_493_);
v___x_495_ = lean_unsigned_to_nat(2u);
v_nbuckets_496_ = lean_nat_mul(v___x_494_, v___x_495_);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_box(0);
v___x_499_ = lean_mk_array(v_nbuckets_496_, v___x_498_);
v___x_500_ = lean_array_propagate_mark(v_data_493_, v___x_499_);
v___x_501_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_497_, v_data_493_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
uint8_t v___x_504_; 
v___x_504_ = 0;
return v___x_504_;
}
else
{
lean_object* v_key_505_; lean_object* v_tail_506_; uint8_t v___x_507_; 
v_key_505_ = lean_ctor_get(v_x_503_, 0);
v_tail_506_ = lean_ctor_get(v_x_503_, 2);
v___x_507_ = lean_name_eq(v_key_505_, v_a_502_);
if (v___x_507_ == 0)
{
v_x_503_ = v_tail_506_;
goto _start;
}
else
{
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec(v_a_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_b_515_){
_start:
{
lean_object* v_size_516_; lean_object* v_buckets_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_563_; 
v_size_516_ = lean_ctor_get(v_m_513_, 0);
v_buckets_517_ = lean_ctor_get(v_m_513_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_m_513_);
if (v_isSharedCheck_563_ == 0)
{
v___x_519_ = v_m_513_;
v_isShared_520_ = v_isSharedCheck_563_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_buckets_517_);
lean_inc(v_size_516_);
lean_dec(v_m_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_563_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; uint64_t v___y_523_; 
v___x_521_ = lean_array_get_size(v_buckets_517_);
if (lean_obj_tag(v_a_514_) == 0)
{
uint64_t v___x_561_; 
v___x_561_ = 1723ULL;
v___y_523_ = v___x_561_;
goto v___jp_522_;
}
else
{
uint64_t v_hash_562_; 
v_hash_562_ = lean_ctor_get_uint64(v_a_514_, sizeof(void*)*2);
v___y_523_ = v_hash_562_;
goto v___jp_522_;
}
v___jp_522_:
{
uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v_fold_526_; uint64_t v___x_527_; uint64_t v___x_528_; uint64_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v_bkt_535_; uint8_t v___x_536_; 
v___x_524_ = 32ULL;
v___x_525_ = lean_uint64_shift_right(v___y_523_, v___x_524_);
v_fold_526_ = lean_uint64_xor(v___y_523_, v___x_525_);
v___x_527_ = 16ULL;
v___x_528_ = lean_uint64_shift_right(v_fold_526_, v___x_527_);
v___x_529_ = lean_uint64_xor(v_fold_526_, v___x_528_);
v___x_530_ = lean_uint64_to_usize(v___x_529_);
v___x_531_ = lean_usize_of_nat(v___x_521_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_sub(v___x_531_, v___x_532_);
v___x_534_ = lean_usize_land(v___x_530_, v___x_533_);
v_bkt_535_ = lean_array_uget_borrowed(v_buckets_517_, v___x_534_);
v___x_536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_514_, v_bkt_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v_size_x27_538_; lean_object* v___x_539_; lean_object* v_buckets_x27_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v_size_x27_538_ = lean_nat_add(v_size_516_, v___x_537_);
lean_dec(v_size_516_);
lean_inc(v_bkt_535_);
v___x_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_539_, 0, v_a_514_);
lean_ctor_set(v___x_539_, 1, v_b_515_);
lean_ctor_set(v___x_539_, 2, v_bkt_535_);
v_buckets_x27_540_ = lean_array_uset(v_buckets_517_, v___x_534_, v___x_539_);
v___x_541_ = lean_unsigned_to_nat(4u);
v___x_542_ = lean_nat_mul(v_size_x27_538_, v___x_541_);
v___x_543_ = lean_unsigned_to_nat(3u);
v___x_544_ = lean_nat_div(v___x_542_, v___x_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_array_get_size(v_buckets_x27_540_);
v___x_546_ = lean_nat_dec_le(v___x_544_, v___x_545_);
lean_dec(v___x_544_);
if (v___x_546_ == 0)
{
lean_object* v_val_547_; lean_object* v___x_549_; 
v_val_547_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_540_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_val_547_);
lean_ctor_set(v___x_519_, 0, v_size_x27_538_);
v___x_549_ = v___x_519_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_size_x27_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_val_547_);
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
lean_object* v___x_552_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_buckets_x27_540_);
lean_ctor_set(v___x_519_, 0, v_size_x27_538_);
v___x_552_ = v___x_519_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_size_x27_538_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_buckets_x27_540_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v___x_554_; lean_object* v_buckets_x27_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_inc(v_bkt_535_);
v___x_554_ = lean_box(0);
v_buckets_x27_555_ = lean_array_uset(v_buckets_517_, v___x_534_, v___x_554_);
v___x_556_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_514_, v_b_515_, v_bkt_535_);
v___x_557_ = lean_array_uset(v_buckets_x27_555_, v___x_534_, v___x_556_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_557_);
v___x_559_ = v___x_519_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_size_516_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_ks_568_; lean_object* v_vs_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_593_; 
v_ks_568_ = lean_ctor_get(v_x_564_, 0);
v_vs_569_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_593_ == 0)
{
v___x_571_ = v_x_564_;
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_vs_569_);
lean_inc(v_ks_568_);
lean_dec(v_x_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_ks_568_);
v___x_574_ = lean_nat_dec_lt(v_x_565_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec(v_x_565_);
v___x_575_ = lean_array_push(v_ks_568_, v_x_566_);
v___x_576_ = lean_array_push(v_vs_569_, v_x_567_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_576_);
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_578_ = v___x_571_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v_k_x27_580_; uint8_t v___x_581_; 
v_k_x27_580_ = lean_array_fget_borrowed(v_ks_568_, v_x_565_);
v___x_581_ = lean_name_eq(v_x_566_, v_k_x27_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_583_; 
if (v_isShared_572_ == 0)
{
v___x_583_ = v___x_571_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_ks_568_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_vs_569_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_add(v_x_565_, v___x_584_);
lean_dec(v_x_565_);
v_x_564_ = v___x_583_;
v_x_565_ = v___x_585_;
goto _start;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_array_fset(v_ks_568_, v_x_565_, v_x_566_);
v___x_589_ = lean_array_fset(v_vs_569_, v_x_565_, v_x_567_);
lean_dec(v_x_565_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_589_);
lean_ctor_set(v___x_571_, 0, v___x_588_);
v___x_591_ = v___x_571_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_594_, lean_object* v_k_595_, lean_object* v_v_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_594_, v___x_597_, v_k_595_, v_v_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_600_, size_t v_x_601_, size_t v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v_es_605_; size_t v___x_606_; size_t v___x_607_; lean_object* v_j_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_es_605_ = lean_ctor_get(v_x_600_, 0);
v___x_606_ = ((size_t)31ULL);
v___x_607_ = lean_usize_land(v_x_601_, v___x_606_);
v_j_608_ = lean_usize_to_nat(v___x_607_);
v___x_609_ = lean_array_get_size(v_es_605_);
v___x_610_ = lean_nat_dec_lt(v_j_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec(v_j_608_);
lean_dec(v_x_604_);
lean_dec(v_x_603_);
return v_x_600_;
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_649_; 
lean_inc_ref(v_es_605_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_x_600_, 0);
lean_dec(v_unused_650_);
v___x_612_ = v_x_600_;
v_isShared_613_ = v_isSharedCheck_649_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_x_600_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_649_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_v_614_; lean_object* v___x_615_; lean_object* v_xs_x27_616_; lean_object* v___y_618_; 
v_v_614_ = lean_array_fget(v_es_605_, v_j_608_);
v___x_615_ = lean_box(0);
v_xs_x27_616_ = lean_array_fset(v_es_605_, v_j_608_, v___x_615_);
switch(lean_obj_tag(v_v_614_))
{
case 0:
{
lean_object* v_key_623_; lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_634_; 
v_key_623_ = lean_ctor_get(v_v_614_, 0);
v_val_624_ = lean_ctor_get(v_v_614_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_v_614_);
if (v_isSharedCheck_634_ == 0)
{
v___x_626_ = v_v_614_;
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_inc(v_key_623_);
lean_dec(v_v_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; 
v___x_628_ = lean_name_eq(v_x_603_, v_key_623_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_del_object(v___x_626_);
v___x_629_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_623_, v_val_624_, v_x_603_, v_x_604_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___y_618_ = v___x_630_;
goto v___jp_617_;
}
else
{
lean_object* v___x_632_; 
lean_dec(v_val_624_);
lean_dec(v_key_623_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_x_604_);
lean_ctor_set(v___x_626_, 0, v_x_603_);
v___x_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_x_603_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_x_604_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
v___y_618_ = v___x_632_;
goto v___jp_617_;
}
}
}
}
case 1:
{
lean_object* v_node_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_node_635_ = lean_ctor_get(v_v_614_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_v_614_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v_v_614_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_node_635_);
lean_dec(v_v_614_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_639_ = ((size_t)5ULL);
v___x_640_ = lean_usize_shift_right(v_x_601_, v___x_639_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_x_602_, v___x_641_);
v___x_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_635_, v___x_640_, v___x_642_, v_x_603_, v_x_604_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_643_);
v___x_645_ = v___x_637_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v___y_618_ = v___x_645_;
goto v___jp_617_;
}
}
}
default: 
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_x_603_);
lean_ctor_set(v___x_648_, 1, v_x_604_);
v___y_618_ = v___x_648_;
goto v___jp_617_;
}
}
v___jp_617_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_array_fset(v_xs_x27_616_, v_j_608_, v___y_618_);
lean_dec(v_j_608_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_619_);
v___x_621_ = v___x_612_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
else
{
lean_object* v_ks_651_; lean_object* v_vs_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_670_; 
v_ks_651_ = lean_ctor_get(v_x_600_, 0);
v_vs_652_ = lean_ctor_get(v_x_600_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_670_ == 0)
{
v___x_654_ = v_x_600_;
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_vs_652_);
lean_inc(v_ks_651_);
lean_dec(v_x_600_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_ks_651_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_vs_652_);
v___x_657_ = v_reuseFailAlloc_669_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v_newNode_658_; size_t v___x_659_; uint8_t v___x_660_; 
v_newNode_658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_657_, v_x_603_, v_x_604_);
v___x_659_ = ((size_t)7ULL);
v___x_660_ = lean_usize_dec_le(v___x_659_, v_x_602_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_658_);
v___x_662_ = lean_unsigned_to_nat(4u);
v___x_663_ = lean_nat_dec_lt(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
if (v___x_663_ == 0)
{
lean_object* v_ks_664_; lean_object* v_vs_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_ks_664_ = lean_ctor_get(v_newNode_658_, 0);
lean_inc_ref(v_ks_664_);
v_vs_665_ = lean_ctor_get(v_newNode_658_, 1);
lean_inc_ref(v_vs_665_);
lean_dec_ref(v_newNode_658_);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_602_, v_ks_664_, v_vs_665_, v___x_666_, v___x_667_);
lean_dec_ref(v_vs_665_);
lean_dec_ref(v_ks_664_);
return v___x_668_;
}
else
{
return v_newNode_658_;
}
}
else
{
return v_newNode_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_671_, lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_i_674_, lean_object* v_entries_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_array_get_size(v_keys_672_);
v___x_677_ = lean_nat_dec_lt(v_i_674_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec(v_i_674_);
return v_entries_675_;
}
else
{
lean_object* v_k_678_; lean_object* v_v_679_; uint64_t v___y_681_; 
v_k_678_ = lean_array_fget_borrowed(v_keys_672_, v_i_674_);
v_v_679_ = lean_array_fget_borrowed(v_vals_673_, v_i_674_);
if (lean_obj_tag(v_k_678_) == 0)
{
uint64_t v___x_692_; 
v___x_692_ = 1723ULL;
v___y_681_ = v___x_692_;
goto v___jp_680_;
}
else
{
uint64_t v_hash_693_; 
v_hash_693_ = lean_ctor_get_uint64(v_k_678_, sizeof(void*)*2);
v___y_681_ = v_hash_693_;
goto v___jp_680_;
}
v___jp_680_:
{
size_t v_h_682_; size_t v___x_683_; lean_object* v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v_h_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_h_682_ = lean_uint64_to_usize(v___y_681_);
v___x_683_ = ((size_t)5ULL);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_sub(v_depth_671_, v___x_685_);
v___x_687_ = lean_usize_mul(v___x_683_, v___x_686_);
v_h_688_ = lean_usize_shift_right(v_h_682_, v___x_687_);
v___x_689_ = lean_nat_add(v_i_674_, v___x_684_);
lean_dec(v_i_674_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
v___x_690_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_675_, v_h_688_, v_depth_671_, v_k_678_, v_v_679_);
v_i_674_ = v___x_689_;
v_entries_675_ = v___x_690_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_694_, lean_object* v_keys_695_, lean_object* v_vals_696_, lean_object* v_i_697_, lean_object* v_entries_698_){
_start:
{
size_t v_depth_boxed_699_; lean_object* v_res_700_; 
v_depth_boxed_699_ = lean_unbox_usize(v_depth_694_);
lean_dec(v_depth_694_);
v_res_700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_699_, v_keys_695_, v_vals_696_, v_i_697_, v_entries_698_);
lean_dec_ref(v_vals_696_);
lean_dec_ref(v_keys_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
size_t v_x_1435__boxed_706_; size_t v_x_1436__boxed_707_; lean_object* v_res_708_; 
v_x_1435__boxed_706_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_x_1436__boxed_707_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_res_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_701_, v_x_1435__boxed_706_, v_x_1436__boxed_707_, v_x_704_, v_x_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
uint64_t v___y_713_; 
if (lean_obj_tag(v_x_710_) == 0)
{
uint64_t v___x_717_; 
v___x_717_ = 1723ULL;
v___y_713_ = v___x_717_;
goto v___jp_712_;
}
else
{
uint64_t v_hash_718_; 
v_hash_718_ = lean_ctor_get_uint64(v_x_710_, sizeof(void*)*2);
v___y_713_ = v_hash_718_;
goto v___jp_712_;
}
v___jp_712_:
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_uint64_to_usize(v___y_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_709_, v___x_714_, v___x_715_, v_x_710_, v_x_711_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
uint8_t v_stage_u2081_722_; 
v_stage_u2081_722_ = lean_ctor_get_uint8(v_x_719_, sizeof(void*)*2);
if (v_stage_u2081_722_ == 0)
{
lean_object* v_map_u2081_723_; lean_object* v_map_u2082_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_map_u2081_723_ = lean_ctor_get(v_x_719_, 0);
v_map_u2082_724_ = lean_ctor_get(v_x_719_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v_x_719_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_map_u2082_724_);
lean_inc(v_map_u2081_723_);
lean_dec(v_x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_724_, v_x_720_, v_x_721_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_map_u2081_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_731_, sizeof(void*)*2, v_stage_u2081_722_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_map_u2081_733_; lean_object* v_map_u2082_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_map_u2081_733_ = lean_ctor_get(v_x_719_, 0);
v_map_u2082_734_ = lean_ctor_get(v_x_719_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_719_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v_x_719_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_map_u2082_734_);
lean_inc(v_map_u2081_733_);
lean_dec(v_x_719_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_733_, v_x_720_, v_x_721_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_map_u2082_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_741_, sizeof(void*)*2, v_stage_u2081_722_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(32u);
v___x_744_ = lean_mk_empty_array_with_capacity(v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_746_ = ((size_t)5ULL);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_unsigned_to_nat(32u);
v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
v___x_750_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_751_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_747_);
lean_ctor_set(v___x_751_, 3, v___x_747_);
lean_ctor_set_usize(v___x_751_, 4, v___x_746_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_752_, lean_object* v_ns_753_, lean_object* v_b_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_752_, v_ns_753_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_757_ = l_Lean_PersistentArray_push___redArg(v___x_756_, v_b_754_);
v___x_758_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_752_, v_ns_753_, v___x_757_);
return v___x_758_;
}
else
{
lean_object* v_val_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_val_759_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_755_, 1);
v___x_760_ = l_Lean_PersistentArray_push___redArg(v_val_759_, v_b_754_);
v___x_761_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_752_, v_ns_753_, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_762_, lean_object* v_scopedEntries_763_, lean_object* v_ns_764_, lean_object* v_b_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_763_, v_ns_764_, v_b_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_771_, v_x_772_, v_x_773_);
lean_dec(v_x_773_);
lean_dec_ref(v_x_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_776_, v_x_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_784_, v_x_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec_ref(v_x_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_789_, v_a_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_792_, lean_object* v_m_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_792_, v_m_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_m_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_797_, v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_801_, lean_object* v_m_802_, lean_object* v_a_803_, lean_object* v_b_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_802_, v_a_803_, v_b_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, size_t v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_807_, v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_1736__boxed_815_; lean_object* v_res_816_; 
v_x_1736__boxed_815_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_res_816_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_811_, v_x_812_, v_x_1736__boxed_815_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_x_812_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_817_, lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_821_, lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_821_, v_a_822_, v_x_823_);
lean_dec(v_x_823_);
lean_dec(v_a_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, size_t v_x_827_, size_t v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_826_, v_x_827_, v_x_828_, v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
size_t v_x_1752__boxed_838_; size_t v_x_1753__boxed_839_; lean_object* v_res_840_; 
v_x_1752__boxed_838_ = lean_unbox_usize(v_x_834_);
lean_dec(v_x_834_);
v_x_1753__boxed_839_ = lean_unbox_usize(v_x_835_);
lean_dec(v_x_835_);
v_res_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_832_, v_x_833_, v_x_1752__boxed_838_, v_x_1753__boxed_839_, v_x_836_, v_x_837_);
return v_res_840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_841_, lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_845_, lean_object* v_a_846_, lean_object* v_x_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_845_, v_a_846_, v_x_847_);
lean_dec(v_x_847_);
lean_dec(v_a_846_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_850_, lean_object* v_data_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_853_, lean_object* v_a_854_, lean_object* v_b_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_854_, v_b_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_858_, lean_object* v_keys_859_, lean_object* v_vals_860_, lean_object* v_heq_861_, lean_object* v_i_862_, lean_object* v_k_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_859_, v_vals_860_, v_i_862_, v_k_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_865_, lean_object* v_keys_866_, lean_object* v_vals_867_, lean_object* v_heq_868_, lean_object* v_i_869_, lean_object* v_k_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_865_, v_keys_866_, v_vals_867_, v_heq_868_, v_i_869_, v_k_870_);
lean_dec(v_k_870_);
lean_dec_ref(v_vals_867_);
lean_dec_ref(v_keys_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_872_, lean_object* v_n_873_, lean_object* v_k_874_, lean_object* v_v_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_873_, v_k_874_, v_v_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_877_, size_t v_depth_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_heq_881_, lean_object* v_i_882_, lean_object* v_entries_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_878_, v_keys_879_, v_vals_880_, v_i_882_, v_entries_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_885_, lean_object* v_depth_886_, lean_object* v_keys_887_, lean_object* v_vals_888_, lean_object* v_heq_889_, lean_object* v_i_890_, lean_object* v_entries_891_){
_start:
{
size_t v_depth_boxed_892_; lean_object* v_res_893_; 
v_depth_boxed_892_ = lean_unbox_usize(v_depth_886_);
lean_dec(v_depth_886_);
v_res_893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_885_, v_depth_boxed_892_, v_keys_887_, v_vals_888_, v_heq_889_, v_i_890_, v_entries_891_);
lean_dec_ref(v_vals_888_);
lean_dec_ref(v_keys_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_894_, lean_object* v_i_895_, lean_object* v_source_896_, lean_object* v_target_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_895_, v_source_896_, v_target_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_900_, v_x_901_, v_x_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_909_, lean_object* v_as_910_, size_t v_sz_911_, size_t v_i_912_, lean_object* v_b_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_a_917_; uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_912_, v_sz_911_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec_ref(v_descr_909_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_913_);
return v___x_922_;
}
else
{
lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_963_; 
v_fst_923_ = lean_ctor_get(v_b_913_, 0);
v_snd_924_ = lean_ctor_get(v_b_913_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_b_913_);
if (v_isSharedCheck_963_ == 0)
{
v___x_926_ = v_b_913_;
v_isShared_927_ = v_isSharedCheck_963_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_inc(v_fst_923_);
lean_dec(v_b_913_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_963_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_a_928_; 
v_a_928_ = lean_array_uget_borrowed(v_as_910_, v_i_912_);
if (lean_obj_tag(v_a_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_ofOLeanEntry_930_; lean_object* v_addEntry_931_; lean_object* v___x_932_; 
v_a_929_ = lean_ctor_get(v_a_928_, 0);
v_ofOLeanEntry_930_ = lean_ctor_get(v_descr_909_, 2);
v_addEntry_931_ = lean_ctor_get(v_descr_909_, 4);
lean_inc_ref(v_ofOLeanEntry_930_);
lean_inc_ref(v___y_914_);
lean_inc(v_a_929_);
lean_inc(v_fst_923_);
v___x_932_ = lean_apply_4(v_ofOLeanEntry_930_, v_fst_923_, v_a_929_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
lean_inc(v_addEntry_931_);
v___x_934_ = lean_apply_2(v_addEntry_931_, v_fst_923_, v_a_933_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_934_);
v___x_936_ = v___x_926_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_snd_924_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v_a_917_ = v___x_936_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_del_object(v___x_926_);
lean_dec(v_snd_924_);
lean_dec(v_fst_923_);
lean_dec_ref(v_descr_909_);
v_a_938_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_932_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_932_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v_ofOLeanEntry_948_; lean_object* v___x_949_; 
v_a_946_ = lean_ctor_get(v_a_928_, 0);
v_a_947_ = lean_ctor_get(v_a_928_, 1);
v_ofOLeanEntry_948_ = lean_ctor_get(v_descr_909_, 2);
lean_inc_ref(v_ofOLeanEntry_948_);
lean_inc_ref(v___y_914_);
lean_inc(v_a_947_);
lean_inc(v_fst_923_);
v___x_949_ = lean_apply_4(v_ofOLeanEntry_948_, v_fst_923_, v_a_947_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
lean_inc(v_a_946_);
v___x_951_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_snd_924_, v_a_946_, v_a_950_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_951_);
v___x_953_ = v___x_926_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_fst_923_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_917_ = v___x_953_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_926_);
lean_dec(v_snd_924_);
lean_dec(v_fst_923_);
lean_dec_ref(v_descr_909_);
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
}
}
v___jp_916_:
{
size_t v___x_918_; size_t v___x_919_; 
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_912_, v___x_918_);
v_i_912_ = v___x_919_;
v_b_913_ = v_a_917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_964_, lean_object* v_as_965_, lean_object* v_sz_966_, lean_object* v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
size_t v_sz_boxed_971_; size_t v_i_boxed_972_; lean_object* v_res_973_; 
v_sz_boxed_971_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_972_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_964_, v_as_965_, v_sz_boxed_971_, v_i_boxed_972_, v_b_968_, v___y_969_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_as_965_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_974_, lean_object* v_as_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_b_978_, lean_object* v___y_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v_descr_974_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_b_978_);
return v___x_982_;
}
else
{
lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1008_; 
v_fst_983_ = lean_ctor_get(v_b_978_, 0);
v_snd_984_ = lean_ctor_get(v_b_978_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_b_978_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_986_ = v_b_978_;
v_isShared_987_ = v_isSharedCheck_1008_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_b_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1008_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_a_988_; lean_object* v___x_990_; 
v_a_988_ = lean_array_uget_borrowed(v_as_975_, v_i_977_);
if (v_isShared_987_ == 0)
{
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_fst_983_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_snd_984_);
v___x_990_ = v_reuseFailAlloc_1007_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; 
v_sz_991_ = lean_array_size(v_a_988_);
v___x_992_ = ((size_t)0ULL);
lean_inc_ref(v_descr_974_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_974_, v_a_988_, v_sz_991_, v___x_992_, v___x_990_, v___y_979_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v_fst_995_; lean_object* v_snd_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1006_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v_fst_995_ = lean_ctor_get(v_a_994_, 0);
v_snd_996_ = lean_ctor_get(v_a_994_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_998_ = v_a_994_;
v_isShared_999_ = v_isSharedCheck_1006_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snd_996_);
lean_inc(v_fst_995_);
lean_dec(v_a_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1006_;
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
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_fst_995_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_snd_996_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_977_, v___x_1002_);
v_i_977_ = v___x_1003_;
v_b_978_ = v___x_1001_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_descr_974_);
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_1009_, lean_object* v_as_1010_, lean_object* v_sz_1011_, lean_object* v_i_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
size_t v_sz_boxed_1016_; size_t v_i_boxed_1017_; lean_object* v_res_1018_; 
v_sz_boxed_1016_ = lean_unbox_usize(v_sz_1011_);
lean_dec(v_sz_1011_);
v_i_boxed_1017_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1009_, v_as_1010_, v_sz_boxed_1016_, v_i_boxed_1017_, v_b_1013_, v___y_1014_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v_as_1010_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_1019_, lean_object* v_as_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_mkInitial_1023_; lean_object* v_finalizeImport_1024_; lean_object* v___x_1025_; 
v_mkInitial_1023_ = lean_ctor_get(v_descr_1019_, 1);
v_finalizeImport_1024_ = lean_ctor_get(v_descr_1019_, 5);
lean_inc(v_finalizeImport_1024_);
lean_inc_ref(v_mkInitial_1023_);
v___x_1025_ = lean_apply_1(v_mkInitial_1023_, lean_box(0));
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; size_t v_sz_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = 1;
v___x_1028_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1026_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v_sz_1030_ = lean_array_size(v_as_1020_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1019_, v_as_1020_, v_sz_1030_, v___x_1031_, v___x_1029_, v_a_1021_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1056_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1056_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1056_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1055_; 
v_fst_1037_ = lean_ctor_get(v_a_1033_, 0);
v_snd_1038_ = lean_ctor_get(v_a_1033_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1040_ = v_a_1033_;
v_isShared_1041_ = v_isSharedCheck_1055_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_a_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1055_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1042_ = lean_apply_1(v_finalizeImport_1024_, v_fst_1037_);
v___x_1043_ = l_Lean_NameSet_empty;
v___x_1044_ = 0;
v___x_1045_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1046_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1046_, 0, v___x_1042_);
lean_ctor_set(v___x_1046_, 1, v___x_1043_);
lean_ctor_set(v___x_1046_, 2, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*3, v___x_1027_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*3 + 1, v___x_1044_);
v___x_1047_ = lean_box(0);
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 1);
lean_ctor_set(v___x_1040_, 1, v___x_1047_);
lean_ctor_set(v___x_1040_, 0, v___x_1046_);
v___x_1049_ = v___x_1040_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_snd_1038_);
lean_ctor_set(v___x_1050_, 2, v___x_1047_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1050_);
v___x_1052_ = v___x_1035_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_finalizeImport_1024_);
v_a_1057_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1032_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1032_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_finalizeImport_1024_);
lean_dec_ref(v_descr_1019_);
v_a_1065_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1025_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1025_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1073_, lean_object* v_as_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1073_, v_as_1074_, v_a_1075_);
lean_dec_ref(v_a_1075_);
lean_dec_ref(v_as_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_00_u03c3_1080_, lean_object* v_descr_1081_, lean_object* v_as_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1081_, v_as_1082_, v_a_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_00_u03c3_1088_, lean_object* v_descr_1089_, lean_object* v_as_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1086_, v_00_u03b2_1087_, v_00_u03c3_1088_, v_descr_1089_, v_as_1090_, v_a_1091_);
lean_dec_ref(v_a_1091_);
lean_dec_ref(v_as_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03c3_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_descr_1097_, lean_object* v_as_1098_, size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1097_, v_as_1098_, v_sz_1099_, v_i_1100_, v_b_1101_, v___y_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1105_, lean_object* v_00_u03c3_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_descr_1108_, lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_sz_boxed_1115_; size_t v_i_boxed_1116_; lean_object* v_res_1117_; 
v_sz_boxed_1115_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1116_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1105_, v_00_u03c3_1106_, v_00_u03b2_1107_, v_descr_1108_, v_as_1109_, v_sz_boxed_1115_, v_i_boxed_1116_, v_b_1112_, v___y_1113_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03c3_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_descr_1121_, lean_object* v_as_1122_, size_t v_sz_1123_, size_t v_i_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1121_, v_as_1122_, v_sz_1123_, v_i_1124_, v_b_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03c3_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_descr_1132_, lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1129_, v_00_u03c3_1130_, v_00_u03b2_1131_, v_descr_1132_, v_as_1133_, v_sz_boxed_1139_, v_i_boxed_1140_, v_b_1136_, v___y_1137_);
lean_dec_ref(v___y_1137_);
lean_dec_ref(v_as_1133_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1142_, lean_object* v_descr_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
if (lean_obj_tag(v_a_1145_) == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_descr_1143_);
v___x_1147_ = l_List_reverse___redArg(v_a_1146_);
return v___x_1147_;
}
else
{
lean_object* v_head_1148_; lean_object* v_tail_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1178_; 
v_head_1148_ = lean_ctor_get(v_a_1145_, 0);
v_tail_1149_ = lean_ctor_get(v_a_1145_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1151_ = v_a_1145_;
v_isShared_1152_ = v_isSharedCheck_1178_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_tail_1149_);
lean_inc(v_head_1148_);
lean_dec(v_a_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1178_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___y_1154_; lean_object* v_state_1159_; lean_object* v_activeScopes_1160_; uint8_t v_delimitsLocal_1161_; uint8_t v_scopeChanged_1162_; lean_object* v_scopeChangedDecls_1163_; uint8_t v___x_1164_; 
v_state_1159_ = lean_ctor_get(v_head_1148_, 0);
v_activeScopes_1160_ = lean_ctor_get(v_head_1148_, 1);
v_delimitsLocal_1161_ = lean_ctor_get_uint8(v_head_1148_, sizeof(void*)*3);
v_scopeChanged_1162_ = lean_ctor_get_uint8(v_head_1148_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1163_ = lean_ctor_get(v_head_1148_, 2);
v___x_1164_ = l_Lean_NameSet_contains(v_activeScopes_1160_, v_a_1142_);
if (v___x_1164_ == 0)
{
v___y_1154_ = v_head_1148_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1174_; 
lean_inc_ref(v_scopeChangedDecls_1163_);
lean_inc(v_activeScopes_1160_);
lean_inc(v_state_1159_);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_head_1148_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1175_ = lean_ctor_get(v_head_1148_, 2);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_head_1148_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_head_1148_, 0);
lean_dec(v_unused_1177_);
v___x_1166_ = v_head_1148_;
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v_head_1148_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_addEntry_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v_addEntry_1168_ = lean_ctor_get(v_descr_1143_, 4);
lean_inc(v_addEntry_1168_);
lean_inc(v_a_1144_);
v___x_1169_ = lean_apply_2(v_addEntry_1168_, v_state_1159_, v_a_1144_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1169_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_activeScopes_1160_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_scopeChangedDecls_1163_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3, v_delimitsLocal_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*3 + 1, v_scopeChanged_1162_);
v___x_1171_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
lean_inc(v_a_1144_);
lean_inc_ref(v_descr_1143_);
v___x_1172_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1143_, v___x_1171_, v_a_1144_);
v___y_1154_ = v___x_1172_;
goto v___jp_1153_;
}
}
}
v___jp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_a_1146_);
lean_ctor_set(v___x_1151_, 0, v___y_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___y_1154_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_a_1146_);
v___x_1156_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
v_a_1145_ = v_tail_1149_;
v_a_1146_ = v___x_1156_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1179_, lean_object* v_descr_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1179_, v_descr_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_object* v___x_1189_; 
lean_dec(v_a_1186_);
lean_dec_ref(v_descr_1185_);
v___x_1189_ = l_List_reverse___redArg(v_a_1188_);
return v___x_1189_;
}
else
{
lean_object* v_head_1190_; lean_object* v_tail_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1213_; 
v_head_1190_ = lean_ctor_get(v_a_1187_, 0);
v_tail_1191_ = lean_ctor_get(v_a_1187_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1187_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1193_ = v_a_1187_;
v_isShared_1194_ = v_isSharedCheck_1213_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_tail_1191_);
lean_inc(v_head_1190_);
lean_dec(v_a_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1213_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_addEntry_1195_; lean_object* v_state_1196_; lean_object* v_activeScopes_1197_; uint8_t v_delimitsLocal_1198_; uint8_t v_scopeChanged_1199_; lean_object* v_scopeChangedDecls_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1212_; 
v_addEntry_1195_ = lean_ctor_get(v_descr_1185_, 4);
v_state_1196_ = lean_ctor_get(v_head_1190_, 0);
v_activeScopes_1197_ = lean_ctor_get(v_head_1190_, 1);
v_delimitsLocal_1198_ = lean_ctor_get_uint8(v_head_1190_, sizeof(void*)*3);
v_scopeChanged_1199_ = lean_ctor_get_uint8(v_head_1190_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1200_ = lean_ctor_get(v_head_1190_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_head_1190_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1202_ = v_head_1190_;
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_scopeChangedDecls_1200_);
lean_inc(v_activeScopes_1197_);
lean_inc(v_state_1196_);
lean_dec(v_head_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_inc(v_addEntry_1195_);
lean_inc(v_a_1186_);
v___x_1204_ = lean_apply_2(v_addEntry_1195_, v_state_1196_, v_a_1186_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_activeScopes_1197_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_scopeChangedDecls_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*3, v_delimitsLocal_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*3 + 1, v_scopeChanged_1199_);
v___x_1206_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_a_1188_);
lean_ctor_set(v___x_1193_, 0, v___x_1206_);
v___x_1208_ = v___x_1193_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_a_1188_);
v___x_1208_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v_a_1187_ = v_tail_1191_;
v_a_1188_ = v___x_1208_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1214_, lean_object* v_s_1215_, lean_object* v_e_1216_){
_start:
{
if (lean_obj_tag(v_e_1216_) == 0)
{
lean_object* v_stateStack_1217_; lean_object* v_scopedEntries_1218_; lean_object* v_newEntries_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1239_; 
v_stateStack_1217_ = lean_ctor_get(v_s_1215_, 0);
v_scopedEntries_1218_ = lean_ctor_get(v_s_1215_, 1);
v_newEntries_1219_ = lean_ctor_get(v_s_1215_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_s_1215_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1221_ = v_s_1215_;
v_isShared_1222_ = v_isSharedCheck_1239_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_newEntries_1219_);
lean_inc(v_scopedEntries_1218_);
lean_inc(v_stateStack_1217_);
lean_dec(v_s_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1239_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1238_; 
v_a_1223_ = lean_ctor_get(v_e_1216_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_e_1216_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1225_ = v_e_1216_;
v_isShared_1226_ = v_isSharedCheck_1238_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v_e_1216_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1238_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_toOLeanEntry_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_toOLeanEntry_1227_ = lean_ctor_get(v_descr_1214_, 3);
lean_inc(v_toOLeanEntry_1227_);
v___x_1228_ = lean_box(0);
lean_inc(v_a_1223_);
v___x_1229_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1214_, v_a_1223_, v_stateStack_1217_, v___x_1228_);
v___x_1230_ = lean_apply_1(v_toOLeanEntry_1227_, v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1230_);
v___x_1232_ = v___x_1225_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v_newEntries_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v___x_1233_);
lean_ctor_set(v___x_1221_, 0, v___x_1229_);
v___x_1235_ = v___x_1221_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_scopedEntries_1218_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1240_; lean_object* v_scopedEntries_1241_; lean_object* v_newEntries_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1264_; 
v_stateStack_1240_ = lean_ctor_get(v_s_1215_, 0);
v_scopedEntries_1241_ = lean_ctor_get(v_s_1215_, 1);
v_newEntries_1242_ = lean_ctor_get(v_s_1215_, 2);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_s_1215_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1244_ = v_s_1215_;
v_isShared_1245_ = v_isSharedCheck_1264_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_newEntries_1242_);
lean_inc(v_scopedEntries_1241_);
lean_inc(v_stateStack_1240_);
lean_dec(v_s_1215_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1264_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_a_1246_; lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1263_; 
v_a_1246_ = lean_ctor_get(v_e_1216_, 0);
v_a_1247_ = lean_ctor_get(v_e_1216_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_e_1216_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1249_ = v_e_1216_;
v_isShared_1250_ = v_isSharedCheck_1263_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_inc(v_a_1246_);
lean_dec(v_e_1216_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1263_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_toOLeanEntry_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_toOLeanEntry_1251_ = lean_ctor_get(v_descr_1214_, 3);
lean_inc(v_toOLeanEntry_1251_);
v___x_1252_ = lean_box(0);
lean_inc_n(v_a_1247_, 2);
v___x_1253_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1246_, v_descr_1214_, v_a_1247_, v_stateStack_1240_, v___x_1252_);
lean_inc(v_a_1246_);
v___x_1254_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1241_, v_a_1246_, v_a_1247_);
v___x_1255_ = lean_apply_1(v_toOLeanEntry_1251_, v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1255_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1246_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_newEntries_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 2, v___x_1258_);
lean_ctor_set(v___x_1244_, 1, v___x_1254_);
lean_ctor_set(v___x_1244_, 0, v___x_1253_);
v___x_1260_ = v___x_1244_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1265_, lean_object* v_00_u03b2_1266_, lean_object* v_00_u03c3_1267_, lean_object* v_descr_1268_, lean_object* v_s_1269_, lean_object* v_e_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1268_, v_s_1269_, v_e_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_00_u03b1_1274_, lean_object* v_descr_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1280_, lean_object* v_a_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_00_u03b1_1283_, lean_object* v_descr_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1281_, v_descr_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1289_, lean_object* v_a_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_00_u03b1_1292_, lean_object* v_descr_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1289_, v_a_1290_, v_00_u03b2_1291_, v_00_u03b1_1292_, v_descr_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1290_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1298_, lean_object* v_env_1299_, lean_object* v_as_1300_, size_t v_sz_1301_, size_t v_i_1302_, lean_object* v_b_1303_){
_start:
{
lean_object* v_a_1305_; uint8_t v___x_1309_; 
v___x_1309_ = lean_usize_dec_lt(v_i_1302_, v_sz_1301_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_env_1299_);
lean_dec_ref(v_descr_1298_);
return v_b_1303_;
}
else
{
lean_object* v_snd_1310_; lean_object* v_fst_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1411_; 
v_snd_1310_ = lean_ctor_get(v_b_1303_, 1);
v_fst_1311_ = lean_ctor_get(v_b_1303_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_b_1303_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1313_ = v_b_1303_;
v_isShared_1314_ = v_isSharedCheck_1411_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1310_);
lean_inc(v_fst_1311_);
lean_dec(v_b_1303_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1411_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_fst_1315_; lean_object* v_snd_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1410_; 
v_fst_1315_ = lean_ctor_get(v_snd_1310_, 0);
v_snd_1316_ = lean_ctor_get(v_snd_1310_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_snd_1310_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1318_ = v_snd_1310_;
v_isShared_1319_ = v_isSharedCheck_1410_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snd_1316_);
lean_inc(v_fst_1315_);
lean_dec(v_snd_1310_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1410_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_array_uget(v_as_1300_, v_i_1302_);
if (lean_obj_tag(v_a_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1370_; 
v_a_1321_ = lean_ctor_get(v_a_1320_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1323_ = v_a_1320_;
v_isShared_1324_ = v_isSharedCheck_1370_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v_a_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1370_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_exportEntry_x3f_1325_; lean_object* v___x_1326_; lean_object* v_exported_1327_; lean_object* v_server_1328_; lean_object* v_private_1329_; lean_object* v___y_1331_; lean_object* v_server_1332_; lean_object* v_exported_1351_; 
v_exportEntry_x3f_1325_ = lean_ctor_get(v_descr_1298_, 6);
lean_inc_ref(v_exportEntry_x3f_1325_);
lean_inc_ref(v_env_1299_);
v___x_1326_ = lean_apply_2(v_exportEntry_x3f_1325_, v_env_1299_, v_a_1321_);
v_exported_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_exported_1327_);
v_server_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_server_1328_);
v_private_1329_ = lean_ctor_get(v___x_1326_, 2);
lean_inc(v_private_1329_);
lean_dec_ref(v___x_1326_);
if (lean_obj_tag(v_exported_1327_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_val_1361_ = lean_ctor_get(v_exported_1327_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_exported_1327_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v_exported_1327_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v_exported_1327_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 0);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_val_1361_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_array_push(v_fst_1311_, v___x_1366_);
v_exported_1351_ = v___x_1367_;
goto v___jp_1350_;
}
}
}
else
{
lean_dec(v_exported_1327_);
v_exported_1351_ = v_fst_1311_;
goto v___jp_1350_;
}
v___jp_1330_:
{
if (lean_obj_tag(v_private_1329_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
v_val_1333_ = lean_ctor_get(v_private_1329_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_private_1329_, 1);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_val_1333_);
v___x_1335_ = v___x_1323_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_array_push(v_snd_1316_, v___x_1335_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1336_);
lean_ctor_set(v___x_1318_, 0, v_server_1332_);
v___x_1338_ = v___x_1318_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_server_1332_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1338_);
lean_ctor_set(v___x_1313_, 0, v___y_1331_);
v___x_1340_ = v___x_1313_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___y_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v_a_1305_ = v___x_1340_;
goto v___jp_1304_;
}
}
}
}
else
{
lean_object* v___x_1345_; 
lean_dec(v_private_1329_);
lean_del_object(v___x_1323_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_server_1332_);
v___x_1345_ = v___x_1318_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_server_1332_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1316_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1345_);
lean_ctor_set(v___x_1313_, 0, v___y_1331_);
v___x_1347_ = v___x_1313_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___y_1331_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v_a_1305_ = v___x_1347_;
goto v___jp_1304_;
}
}
}
}
v___jp_1350_:
{
if (lean_obj_tag(v_server_1328_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_val_1352_ = lean_ctor_get(v_server_1328_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_server_1328_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v_server_1328_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v_server_1328_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 0);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1352_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_array_push(v_fst_1315_, v___x_1357_);
v___y_1331_ = v_exported_1351_;
v_server_1332_ = v___x_1358_;
goto v___jp_1330_;
}
}
}
else
{
lean_dec(v_server_1328_);
v___y_1331_ = v_exported_1351_;
v_server_1332_ = v_fst_1315_;
goto v___jp_1330_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1409_; 
v_a_1371_ = lean_ctor_get(v_a_1320_, 0);
v_a_1372_ = lean_ctor_get(v_a_1320_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1374_ = v_a_1320_;
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_inc(v_a_1371_);
lean_dec(v_a_1320_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_exportEntry_x3f_1376_; lean_object* v___x_1377_; lean_object* v_exported_1378_; lean_object* v_server_1379_; lean_object* v_private_1380_; lean_object* v___y_1382_; lean_object* v_server_1383_; lean_object* v_exported_1402_; 
v_exportEntry_x3f_1376_ = lean_ctor_get(v_descr_1298_, 6);
lean_inc_ref(v_exportEntry_x3f_1376_);
lean_inc_ref(v_env_1299_);
v___x_1377_ = lean_apply_2(v_exportEntry_x3f_1376_, v_env_1299_, v_a_1372_);
v_exported_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_exported_1378_);
v_server_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_server_1379_);
v_private_1380_ = lean_ctor_get(v___x_1377_, 2);
lean_inc(v_private_1380_);
lean_dec_ref(v___x_1377_);
if (lean_obj_tag(v_exported_1378_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_val_1406_ = lean_ctor_get(v_exported_1378_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v_exported_1378_, 1);
lean_inc(v_a_1371_);
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_a_1371_);
lean_ctor_set(v___x_1407_, 1, v_val_1406_);
v___x_1408_ = lean_array_push(v_fst_1311_, v___x_1407_);
v_exported_1402_ = v___x_1408_;
goto v___jp_1401_;
}
else
{
lean_dec(v_exported_1378_);
v_exported_1402_ = v_fst_1311_;
goto v___jp_1401_;
}
v___jp_1381_:
{
if (lean_obj_tag(v_private_1380_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; 
v_val_1384_ = lean_ctor_get(v_private_1380_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v_private_1380_, 1);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_val_1384_);
v___x_1386_ = v___x_1374_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_val_1384_);
v___x_1386_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_array_push(v_snd_1316_, v___x_1386_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1387_);
lean_ctor_set(v___x_1318_, 0, v_server_1383_);
v___x_1389_ = v___x_1318_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_server_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1389_);
lean_ctor_set(v___x_1313_, 0, v___y_1382_);
v___x_1391_ = v___x_1313_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___y_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v_a_1305_ = v___x_1391_;
goto v___jp_1304_;
}
}
}
}
else
{
lean_object* v___x_1396_; 
lean_dec(v_private_1380_);
lean_del_object(v___x_1374_);
lean_dec(v_a_1371_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_server_1383_);
v___x_1396_ = v___x_1318_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_server_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_snd_1316_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1396_);
lean_ctor_set(v___x_1313_, 0, v___y_1382_);
v___x_1398_ = v___x_1313_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___y_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v_a_1305_ = v___x_1398_;
goto v___jp_1304_;
}
}
}
}
v___jp_1401_:
{
if (lean_obj_tag(v_server_1379_) == 1)
{
lean_object* v_val_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_val_1403_ = lean_ctor_get(v_server_1379_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v_server_1379_, 1);
lean_inc(v_a_1371_);
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_a_1371_);
lean_ctor_set(v___x_1404_, 1, v_val_1403_);
v___x_1405_ = lean_array_push(v_fst_1315_, v___x_1404_);
v___y_1382_ = v_exported_1402_;
v_server_1383_ = v___x_1405_;
goto v___jp_1381_;
}
else
{
lean_dec(v_server_1379_);
v___y_1382_ = v_exported_1402_;
v_server_1383_ = v_fst_1315_;
goto v___jp_1381_;
}
}
}
}
}
}
}
v___jp_1304_:
{
size_t v___x_1306_; size_t v___x_1307_; 
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_add(v_i_1302_, v___x_1306_);
v_i_1302_ = v___x_1307_;
v_b_1303_ = v_a_1305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1412_, lean_object* v_env_1413_, lean_object* v_as_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_b_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1412_, v_env_1413_, v_as_1414_, v_sz_boxed_1418_, v_i_boxed_1419_, v_b_1417_);
lean_dec_ref(v_as_1414_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1428_, lean_object* v_env_1429_, lean_object* v_s_1430_){
_start:
{
lean_object* v_newEntries_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1448_; 
v_newEntries_1431_ = lean_ctor_get(v_s_1430_, 2);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_s_1430_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_s_1430_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_s_1430_, 0);
lean_dec(v_unused_1450_);
v___x_1433_ = v_s_1430_;
v_isShared_1434_ = v_isSharedCheck_1448_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_newEntries_1431_);
lean_dec(v_s_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1448_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; size_t v_sz_1438_; size_t v___x_1439_; lean_object* v___x_1440_; lean_object* v_snd_1441_; lean_object* v_fst_1442_; lean_object* v_fst_1443_; lean_object* v_snd_1444_; lean_object* v___x_1446_; 
v___x_1435_ = lean_array_mk(v_newEntries_1431_);
v___x_1436_ = l_Array_reverse___redArg(v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1438_ = lean_array_size(v___x_1436_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1428_, v_env_1429_, v___x_1436_, v_sz_1438_, v___x_1439_, v___x_1437_);
lean_dec_ref(v___x_1436_);
v_snd_1441_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_snd_1441_);
v_fst_1442_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_fst_1442_);
lean_dec_ref(v___x_1440_);
v_fst_1443_ = lean_ctor_get(v_snd_1441_, 0);
lean_inc(v_fst_1443_);
v_snd_1444_ = lean_ctor_get(v_snd_1441_, 1);
lean_inc(v_snd_1444_);
lean_dec(v_snd_1441_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 2, v_snd_1444_);
lean_ctor_set(v___x_1433_, 1, v_fst_1443_);
lean_ctor_set(v___x_1433_, 0, v_fst_1442_);
v___x_1446_ = v___x_1433_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fst_1442_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_fst_1443_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_snd_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_00_u03c3_1453_, lean_object* v_descr_1454_, lean_object* v_env_1455_, lean_object* v_s_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1454_, v_env_1455_, v_s_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1458_, lean_object* v_00_u03b2_1459_, lean_object* v_00_u03c3_1460_, lean_object* v_descr_1461_, lean_object* v_env_1462_, lean_object* v_as_1463_, size_t v_sz_1464_, size_t v_i_1465_, lean_object* v_b_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1461_, v_env_1462_, v_as_1463_, v_sz_1464_, v_i_1465_, v_b_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_00_u03c3_1470_, lean_object* v_descr_1471_, lean_object* v_env_1472_, lean_object* v_as_1473_, lean_object* v_sz_1474_, lean_object* v_i_1475_, lean_object* v_b_1476_){
_start:
{
size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1474_);
lean_dec(v_sz_1474_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1468_, v_00_u03b2_1469_, v_00_u03c3_1470_, v_descr_1471_, v_env_1472_, v_as_1473_, v_sz_boxed_1477_, v_i_boxed_1478_, v_b_1476_);
lean_dec_ref(v_as_1473_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1485_, v___y_1486_);
lean_dec_ref(v___y_1486_);
lean_dec_ref(v_x_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1489_, lean_object* v_x_1490_){
_start:
{
lean_inc_ref(v_s_1489_);
return v_s_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1491_, v_x_1492_);
lean_dec_ref(v_x_1492_);
lean_dec_ref(v_s_1491_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1499_, v_x_1500_);
lean_dec_ref(v_x_1500_);
lean_dec_ref(v_x_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_box(0);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1504_);
lean_dec_ref(v_x_1504_);
return v_res_1505_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___f_1511_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1512_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1513_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1514_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1517_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
lean_ctor_set(v___x_1517_, 2, v___f_1514_);
lean_ctor_set(v___x_1517_, 3, v___f_1513_);
lean_ctor_set(v___x_1517_, 4, v___f_1512_);
lean_ctor_set(v___x_1517_, 5, v___f_1511_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1518_){
_start:
{
lean_object* v___f_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___f_1519_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1520_, 0, v_inst_1518_);
v___f_1521_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1522_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1525_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1526_ = 0;
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1528_, 0, v___x_1523_);
lean_ctor_set(v___x_1528_, 1, v___x_1524_);
lean_ctor_set(v___x_1528_, 2, v___f_1519_);
lean_ctor_set(v___x_1528_, 3, v___f_1520_);
lean_ctor_set(v___x_1528_, 4, v___f_1521_);
lean_ctor_set(v___x_1528_, 5, v___x_1525_);
lean_ctor_set(v___x_1528_, 6, v___f_1522_);
lean_ctor_set(v___x_1528_, 7, v___x_1527_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*8, v___x_1526_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*8 + 1, v___x_1526_);
v___x_1529_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_00_u03c3_1533_, lean_object* v_inst_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1538_, lean_object* v_inst_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1547_ = lean_st_mk_ref(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_x_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_x_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_x_1553_);
lean_dec_ref(v_x_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1558_){
_start:
{
lean_object* v_newEntries_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_newEntries_1559_ = lean_ctor_get(v_s_1558_, 2);
v___x_1560_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1561_ = l_List_lengthTR___redArg(v_newEntries_1559_);
v___x_1562_ = l_Nat_reprFast(v___x_1561_);
v___x_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1560_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1565_);
lean_dec_ref(v_s_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1571_){
_start:
{
lean_object* v_name_1573_; uint8_t v_trackGen_1574_; uint8_t v_logWrites_1575_; lean_object* v_entryDecl_x3f_1576_; lean_object* v___f_1577_; lean_object* v___f_1578_; 
v_name_1573_ = lean_ctor_get(v_descr_1571_, 0);
v_trackGen_1574_ = lean_ctor_get_uint8(v_descr_1571_, sizeof(void*)*8);
v_logWrites_1575_ = lean_ctor_get_uint8(v_descr_1571_, sizeof(void*)*8 + 1);
v_entryDecl_x3f_1576_ = lean_ctor_get(v_descr_1571_, 7);
v___f_1577_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1578_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
if (v_logWrites_1575_ == 0)
{
goto v___jp_1579_;
}
else
{
if (lean_obj_tag(v_entryDecl_x3f_1576_) == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v_name_1573_);
lean_dec_ref(v_descr_1571_);
v___x_1610_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2));
v___x_1611_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1573_, v_logWrites_1575_);
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3));
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
v___x_1615_ = lean_mk_io_user_error(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
else
{
goto v___jp_1579_;
}
}
v___jp_1579_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_inc_ref_n(v_descr_1571_, 4);
v___x_1580_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1580_, 0, lean_box(0));
lean_closure_set(v___x_1580_, 1, lean_box(0));
lean_closure_set(v___x_1580_, 2, lean_box(0));
lean_closure_set(v___x_1580_, 3, v_descr_1571_);
v___x_1581_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1581_, 0, lean_box(0));
lean_closure_set(v___x_1581_, 1, lean_box(0));
lean_closure_set(v___x_1581_, 2, lean_box(0));
lean_closure_set(v___x_1581_, 3, v_descr_1571_);
v___x_1582_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1582_, 0, lean_box(0));
lean_closure_set(v___x_1582_, 1, lean_box(0));
lean_closure_set(v___x_1582_, 2, lean_box(0));
lean_closure_set(v___x_1582_, 3, v_descr_1571_);
v___x_1583_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1583_, 0, lean_box(0));
lean_closure_set(v___x_1583_, 1, lean_box(0));
lean_closure_set(v___x_1583_, 2, lean_box(0));
lean_closure_set(v___x_1583_, 3, v_descr_1571_);
v___x_1584_ = lean_box(2);
v___x_1585_ = lean_box(0);
lean_inc(v_name_1573_);
v___x_1586_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1586_, 0, v_name_1573_);
lean_ctor_set(v___x_1586_, 1, v___x_1580_);
lean_ctor_set(v___x_1586_, 2, v___x_1581_);
lean_ctor_set(v___x_1586_, 3, v___x_1582_);
lean_ctor_set(v___x_1586_, 4, v___x_1583_);
lean_ctor_set(v___x_1586_, 5, v___f_1578_);
lean_ctor_set(v___x_1586_, 6, v___x_1584_);
lean_ctor_set(v___x_1586_, 7, v___x_1585_);
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*8, v_trackGen_1574_);
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*8 + 1, v_logWrites_1575_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___f_1577_);
v___x_1588_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1601_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1601_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1601_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v_descr_1571_);
lean_ctor_set(v___x_1593_, 1, v_a_1589_);
v___x_1594_ = l_Lean_scopedEnvExtensionsRef;
v___x_1595_ = lean_st_ref_take(v___x_1594_);
lean_inc_ref(v___x_1593_);
v___x_1596_ = lean_array_push(v___x_1595_, v___x_1593_);
v___x_1597_ = lean_st_ref_put(v___x_1594_, v___x_1596_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1599_ = v___x_1591_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1593_);
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
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_descr_1571_);
v_a_1602_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1588_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1588_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_00_u03c3_1622_, lean_object* v_descr_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_00_u03c3_1628_, lean_object* v_descr_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1626_, v_00_u03b2_1627_, v_00_u03c3_1628_, v_descr_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0(lean_object* v_f_1632_, lean_object* v_ps_1633_){
_start:
{
lean_object* v_importedEntries_1634_; lean_object* v_state_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
v_importedEntries_1634_ = lean_ctor_get(v_ps_1633_, 0);
v_state_1635_ = lean_ctor_get(v_ps_1633_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_ps_1633_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1637_ = v_ps_1633_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_state_1635_);
lean_inc(v_importedEntries_1634_);
lean_dec(v_ps_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_apply_1(v_f_1632_, v_state_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 1, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_importedEntries_1634_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(lean_object* v_as_1644_, size_t v_i_1645_, size_t v_stop_1646_, lean_object* v_b_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_eq(v_i_1645_, v_stop_1646_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; 
v___x_1649_ = lean_array_uget_borrowed(v_as_1644_, v_i_1645_);
lean_inc(v___x_1649_);
v___x_1650_ = l_Lean_Environment_logDeclChange(v_b_1647_, v___x_1649_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1645_, v___x_1651_);
v_i_1645_ = v___x_1652_;
v_b_1647_ = v___x_1650_;
goto _start;
}
else
{
return v_b_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0___boxed(lean_object* v_as_1654_, lean_object* v_i_1655_, lean_object* v_stop_1656_, lean_object* v_b_1657_){
_start:
{
size_t v_i_boxed_1658_; size_t v_stop_boxed_1659_; lean_object* v_res_1660_; 
v_i_boxed_1658_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_stop_boxed_1659_ = lean_unbox_usize(v_stop_1656_);
lean_dec(v_stop_1656_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_as_1654_, v_i_boxed_1658_, v_stop_boxed_1659_, v_b_1657_);
lean_dec_ref(v_as_1654_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(lean_object* v_ext_1661_, lean_object* v_env_1662_, uint8_t v_changed_1663_, lean_object* v_f_1664_, lean_object* v_changedDecls_1665_){
_start:
{
lean_object* v___f_1666_; uint8_t v___y_1668_; lean_object* v___y_1669_; 
v___f_1666_ = lean_alloc_closure((void*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1666_, 0, v_f_1664_);
if (v_changed_1663_ == 0)
{
v___y_1668_ = v_changed_1663_;
v___y_1669_ = v_env_1662_;
goto v___jp_1667_;
}
else
{
lean_object* v_descr_1675_; uint8_t v___x_1676_; 
v_descr_1675_ = lean_ctor_get(v_ext_1661_, 0);
v___x_1676_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_1675_);
if (v___x_1676_ == 0)
{
v___y_1668_ = v___x_1676_;
v___y_1669_ = v_env_1662_;
goto v___jp_1667_;
}
else
{
uint8_t v_logWrites_1677_; 
v_logWrites_1677_ = lean_ctor_get_uint8(v_descr_1675_, sizeof(void*)*8 + 1);
if (v_logWrites_1677_ == 0)
{
v___y_1668_ = v___x_1676_;
v___y_1669_ = v_env_1662_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_array_get_size(v_changedDecls_1665_);
v___x_1680_ = lean_nat_dec_lt(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
v___y_1668_ = v___x_1676_;
v___y_1669_ = v_env_1662_;
goto v___jp_1667_;
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = lean_usize_of_nat(v___x_1679_);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1665_, v___x_1681_, v___x_1682_, v_env_1662_);
v___y_1668_ = v___x_1676_;
v___y_1669_ = v___x_1683_;
goto v___jp_1667_;
}
}
}
}
v___jp_1667_:
{
lean_object* v_ext_1670_; lean_object* v_toEnvExtension_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_ext_1670_ = lean_ctor_get(v_ext_1661_, 1);
lean_inc_ref(v_ext_1670_);
lean_dec_ref(v_ext_1661_);
v_toEnvExtension_1671_ = lean_ctor_get(v_ext_1670_, 0);
lean_inc_ref(v_toEnvExtension_1671_);
lean_dec_ref(v_ext_1670_);
v___x_1672_ = lean_box(1);
v___x_1673_ = lean_box(0);
v___x_1674_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1671_, v___y_1669_, v___f_1666_, v___x_1672_, v___x_1673_, v___y_1668_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___boxed(lean_object* v_ext_1684_, lean_object* v_env_1685_, lean_object* v_changed_1686_, lean_object* v_f_1687_, lean_object* v_changedDecls_1688_){
_start:
{
uint8_t v_changed_boxed_1689_; lean_object* v_res_1690_; 
v_changed_boxed_1689_ = lean_unbox(v_changed_1686_);
v_res_1690_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1684_, v_env_1685_, v_changed_boxed_1689_, v_f_1687_, v_changedDecls_1688_);
lean_dec_ref(v_changedDecls_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_00_u03c3_1693_, lean_object* v_ext_1694_, lean_object* v_env_1695_, uint8_t v_changed_1696_, lean_object* v_f_1697_, lean_object* v_changedDecls_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1694_, v_env_1695_, v_changed_1696_, v_f_1697_, v_changedDecls_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_00_u03c3_1702_, lean_object* v_ext_1703_, lean_object* v_env_1704_, lean_object* v_changed_1705_, lean_object* v_f_1706_, lean_object* v_changedDecls_1707_){
_start:
{
uint8_t v_changed_boxed_1708_; lean_object* v_res_1709_; 
v_changed_boxed_1708_ = lean_unbox(v_changed_1705_);
v_res_1709_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(v_00_u03b1_1700_, v_00_u03b2_1701_, v_00_u03c3_1702_, v_ext_1703_, v_env_1704_, v_changed_boxed_1708_, v_f_1706_, v_changedDecls_1707_);
lean_dec_ref(v_changedDecls_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(uint8_t v___x_1710_, lean_object* v_s_1711_){
_start:
{
lean_object* v_stateStack_1712_; 
v_stateStack_1712_ = lean_ctor_get(v_s_1711_, 0);
if (lean_obj_tag(v_stateStack_1712_) == 0)
{
return v_s_1711_;
}
else
{
lean_object* v_head_1713_; lean_object* v_scopedEntries_1714_; lean_object* v_newEntries_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1735_; 
lean_inc_ref(v_stateStack_1712_);
v_head_1713_ = lean_ctor_get(v_stateStack_1712_, 0);
lean_inc(v_head_1713_);
v_scopedEntries_1714_ = lean_ctor_get(v_s_1711_, 1);
v_newEntries_1715_ = lean_ctor_get(v_s_1711_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_s_1711_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_s_1711_, 0);
lean_dec(v_unused_1736_);
v___x_1717_ = v_s_1711_;
v_isShared_1718_ = v_isSharedCheck_1735_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_newEntries_1715_);
lean_inc(v_scopedEntries_1714_);
lean_dec(v_s_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1735_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_state_1719_; lean_object* v_activeScopes_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1733_; 
v_state_1719_ = lean_ctor_get(v_head_1713_, 0);
v_activeScopes_1720_ = lean_ctor_get(v_head_1713_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_head_1713_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_head_1713_, 2);
lean_dec(v_unused_1734_);
v___x_1722_ = v_head_1713_;
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_activeScopes_1720_);
lean_inc(v_state_1719_);
lean_dec(v_head_1713_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = 1;
v___x_1725_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 2, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_state_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_activeScopes_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*3, v___x_1724_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*3 + 1, v___x_1710_);
v___x_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
lean_ctor_set(v___x_1728_, 1, v_stateStack_1712_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1728_);
v___x_1730_ = v___x_1717_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_scopedEntries_1714_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_newEntries_1715_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed(lean_object* v___x_1737_, lean_object* v_s_1738_){
_start:
{
uint8_t v___x_59__boxed_1739_; lean_object* v_res_1740_; 
v___x_59__boxed_1739_ = lean_unbox(v___x_1737_);
v_res_1740_ = l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(v___x_59__boxed_1739_, v_s_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1744_, lean_object* v_env_1745_){
_start:
{
uint8_t v___x_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = 0;
v___f_1747_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1748_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1749_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1744_, v_env_1745_, v___x_1746_, v___f_1747_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1750_, lean_object* v_00_u03b2_1751_, lean_object* v_00_u03c3_1752_, lean_object* v_ext_1753_, lean_object* v_env_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1753_, v_env_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_tail_1756_, lean_object* v_s_1757_){
_start:
{
lean_object* v_scopedEntries_1758_; lean_object* v_newEntries_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_scopedEntries_1758_ = lean_ctor_get(v_s_1757_, 1);
v_newEntries_1759_ = lean_ctor_get(v_s_1757_, 2);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_s_1757_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v_s_1757_, 0);
lean_dec(v_unused_1767_);
v___x_1761_ = v_s_1757_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_newEntries_1759_);
lean_inc(v_scopedEntries_1758_);
lean_dec(v_s_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_tail_1756_);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_tail_1756_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_scopedEntries_1758_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_newEntries_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1768_, lean_object* v_env_1769_){
_start:
{
lean_object* v_ext_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v_stateStack_1776_; 
v_ext_1770_ = lean_ctor_get(v_ext_1768_, 1);
v___x_1771_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1772_ = lean_box(1);
v___x_1773_ = lean_box(0);
v___x_1774_ = 0;
lean_inc_ref(v_env_1769_);
v___x_1775_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1771_, v_ext_1770_, v_env_1769_, v___x_1772_, v___x_1773_, v___x_1774_);
v_stateStack_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_stateStack_1776_);
lean_dec(v___x_1775_);
if (lean_obj_tag(v_stateStack_1776_) == 1)
{
lean_object* v_tail_1777_; 
v_tail_1777_ = lean_ctor_get(v_stateStack_1776_, 1);
lean_inc(v_tail_1777_);
if (lean_obj_tag(v_tail_1777_) == 1)
{
lean_object* v_head_1778_; uint8_t v_scopeChanged_1779_; lean_object* v_scopeChangedDecls_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; 
v_head_1778_ = lean_ctor_get(v_stateStack_1776_, 0);
lean_inc(v_head_1778_);
lean_dec_ref_known(v_stateStack_1776_, 2);
v_scopeChanged_1779_ = lean_ctor_get_uint8(v_head_1778_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1780_ = lean_ctor_get(v_head_1778_, 2);
lean_inc_ref(v_scopeChangedDecls_1780_);
lean_dec(v_head_1778_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1781_, 0, v_tail_1777_);
v___x_1782_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1768_, v_env_1769_, v_scopeChanged_1779_, v___f_1781_, v_scopeChangedDecls_1780_);
lean_dec_ref(v_scopeChangedDecls_1780_);
return v___x_1782_;
}
else
{
lean_dec_ref_known(v_stateStack_1776_, 2);
lean_dec(v_tail_1777_);
lean_dec_ref(v_ext_1768_);
return v_env_1769_;
}
}
else
{
lean_dec(v_stateStack_1776_);
lean_dec_ref(v_ext_1768_);
return v_env_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_00_u03c3_1785_, lean_object* v_ext_1786_, lean_object* v_env_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1786_, v_env_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_zero_1791_; uint8_t v_isZero_1792_; 
v_zero_1791_ = lean_unsigned_to_nat(0u);
v_isZero_1792_ = lean_nat_dec_eq(v_a_1789_, v_zero_1791_);
if (v_isZero_1792_ == 1)
{
return v_a_1790_;
}
else
{
if (lean_obj_tag(v_a_1790_) == 0)
{
return v_a_1790_;
}
else
{
lean_object* v_head_1793_; lean_object* v_tail_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1815_; 
v_head_1793_ = lean_ctor_get(v_a_1790_, 0);
v_tail_1794_ = lean_ctor_get(v_a_1790_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1796_ = v_a_1790_;
v_isShared_1797_ = v_isSharedCheck_1815_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_tail_1794_);
lean_inc(v_head_1793_);
lean_dec(v_a_1790_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1815_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_state_1798_; lean_object* v_activeScopes_1799_; uint8_t v_scopeChanged_1800_; lean_object* v_scopeChangedDecls_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1814_; 
v_state_1798_ = lean_ctor_get(v_head_1793_, 0);
v_activeScopes_1799_ = lean_ctor_get(v_head_1793_, 1);
v_scopeChanged_1800_ = lean_ctor_get_uint8(v_head_1793_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1801_ = lean_ctor_get(v_head_1793_, 2);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_head_1793_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1803_ = v_head_1793_;
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_scopeChangedDecls_1801_);
lean_inc(v_activeScopes_1799_);
lean_inc(v_state_1798_);
lean_dec(v_head_1793_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_one_1805_; lean_object* v_n_1806_; lean_object* v___x_1808_; 
v_one_1805_ = lean_unsigned_to_nat(1u);
v_n_1806_ = lean_nat_sub(v_a_1789_, v_one_1805_);
if (v_isShared_1804_ == 0)
{
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_state_1798_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_activeScopes_1799_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_scopeChangedDecls_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*3 + 1, v_scopeChanged_1800_);
v___x_1808_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*3, v_isZero_1792_);
v___x_1809_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1806_, v_tail_1794_);
lean_dec(v_n_1806_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1809_);
lean_ctor_set(v___x_1796_, 0, v___x_1808_);
v___x_1811_ = v___x_1796_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1816_, v_a_1817_);
lean_dec(v_a_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1820_, v_a_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1823_, v_a_1824_, v_a_1825_);
lean_dec(v_a_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1827_, lean_object* v_s_1828_){
_start:
{
lean_object* v_stateStack_1829_; lean_object* v_scopedEntries_1830_; lean_object* v_newEntries_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
v_stateStack_1829_ = lean_ctor_get(v_s_1828_, 0);
v_scopedEntries_1830_ = lean_ctor_get(v_s_1828_, 1);
v_newEntries_1831_ = lean_ctor_get(v_s_1828_, 2);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_s_1828_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v_s_1828_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_newEntries_1831_);
lean_inc(v_scopedEntries_1830_);
lean_inc(v_stateStack_1829_);
lean_dec(v_s_1828_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1827_, v_stateStack_1829_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_scopedEntries_1830_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_newEntries_1831_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1840_, lean_object* v_s_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1840_, v_s_1841_);
lean_dec(v_depth_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1843_, lean_object* v_env_1844_, lean_object* v_depth_1845_){
_start:
{
lean_object* v___f_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1846_, 0, v_depth_1845_);
v___x_1847_ = 0;
v___x_1848_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1849_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1843_, v_env_1844_, v___x_1847_, v___f_1846_, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_00_u03c3_1852_, lean_object* v_ext_1853_, lean_object* v_env_1854_, lean_object* v_depth_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1853_, v_env_1854_, v_depth_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg(lean_object* v_ext_1859_, lean_object* v_b_1860_){
_start:
{
lean_object* v_descr_1861_; lean_object* v_entryDecl_x3f_1862_; 
v_descr_1861_ = lean_ctor_get(v_ext_1859_, 0);
lean_inc_ref(v_descr_1861_);
lean_dec_ref(v_ext_1859_);
v_entryDecl_x3f_1862_ = lean_ctor_get(v_descr_1861_, 7);
lean_inc(v_entryDecl_x3f_1862_);
lean_dec_ref(v_descr_1861_);
if (lean_obj_tag(v_entryDecl_x3f_1862_) == 1)
{
lean_object* v_val_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_val_1863_ = lean_ctor_get(v_entryDecl_x3f_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_entryDecl_x3f_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v_entryDecl_x3f_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_val_1863_);
lean_dec(v_entryDecl_x3f_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_apply_1(v_val_1863_, v_b_1860_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v___x_1872_; 
lean_dec(v_entryDecl_x3f_1862_);
lean_dec(v_b_1860_);
v___x_1872_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog(lean_object* v_00_u03b1_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_00_u03c3_1875_, lean_object* v_ext_1876_, lean_object* v_b_1877_){
_start:
{
lean_object* v_descr_1878_; lean_object* v_entryDecl_x3f_1879_; 
v_descr_1878_ = lean_ctor_get(v_ext_1876_, 0);
lean_inc_ref(v_descr_1878_);
lean_dec_ref(v_ext_1876_);
v_entryDecl_x3f_1879_ = lean_ctor_get(v_descr_1878_, 7);
lean_inc(v_entryDecl_x3f_1879_);
lean_dec_ref(v_descr_1878_);
if (lean_obj_tag(v_entryDecl_x3f_1879_) == 1)
{
lean_object* v_val_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1888_; 
v_val_1880_ = lean_ctor_get(v_entryDecl_x3f_1879_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_entryDecl_x3f_1879_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1882_ = v_entryDecl_x3f_1879_;
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_val_1880_);
lean_dec(v_entryDecl_x3f_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_apply_1(v_val_1880_, v_b_1877_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1884_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v___x_1889_; 
lean_dec(v_entryDecl_x3f_1879_);
lean_dec(v_b_1877_);
v___x_1889_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0(lean_object* v_addEntryFn_1890_, lean_object* v___x_1891_, lean_object* v_s_1892_){
_start:
{
lean_object* v_importedEntries_1893_; lean_object* v_state_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_importedEntries_1893_ = lean_ctor_get(v_s_1892_, 0);
v_state_1894_ = lean_ctor_get(v_s_1892_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_s_1892_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v_s_1892_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_state_1894_);
lean_inc(v_importedEntries_1893_);
lean_dec(v_s_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_state_1898_; lean_object* v___x_1900_; 
v_state_1898_ = lean_apply_2(v_addEntryFn_1890_, v_state_1894_, v___x_1891_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v_state_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_importedEntries_1893_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_state_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1903_, lean_object* v_env_1904_, lean_object* v_b_1905_){
_start:
{
lean_object* v_ext_1906_; lean_object* v_toEnvExtension_1907_; lean_object* v_descr_1908_; lean_object* v_addEntryFn_1909_; lean_object* v_asyncMode_1910_; uint8_t v_logWrites_1911_; lean_object* v_entryDecl_x3f_1912_; lean_object* v___x_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v_declName_1917_; 
v_ext_1906_ = lean_ctor_get(v_ext_1903_, 1);
lean_inc_ref(v_ext_1906_);
v_toEnvExtension_1907_ = lean_ctor_get(v_ext_1906_, 0);
lean_inc_ref(v_toEnvExtension_1907_);
v_descr_1908_ = lean_ctor_get(v_ext_1903_, 0);
lean_inc_ref(v_descr_1908_);
lean_dec_ref(v_ext_1903_);
v_addEntryFn_1909_ = lean_ctor_get(v_ext_1906_, 3);
lean_inc(v_addEntryFn_1909_);
lean_dec_ref(v_ext_1906_);
v_asyncMode_1910_ = lean_ctor_get(v_toEnvExtension_1907_, 2);
lean_inc(v_asyncMode_1910_);
v_logWrites_1911_ = lean_ctor_get_uint8(v_toEnvExtension_1907_, sizeof(void*)*6);
v_entryDecl_x3f_1912_ = lean_ctor_get(v_descr_1908_, 7);
lean_inc(v_entryDecl_x3f_1912_);
lean_dec_ref(v_descr_1908_);
lean_inc(v_b_1905_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1905_);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1914_, 0, v_addEntryFn_1909_);
lean_closure_set(v___f_1914_, 1, v___x_1913_);
v___x_1915_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1912_) == 1)
{
lean_object* v_val_1922_; lean_object* v___x_1923_; 
v_val_1922_ = lean_ctor_get(v_entryDecl_x3f_1912_, 0);
lean_inc(v_val_1922_);
lean_dec_ref_known(v_entryDecl_x3f_1912_, 1);
v___x_1923_ = lean_apply_1(v_val_1922_, v_b_1905_);
v_declName_1917_ = v___x_1923_;
goto v___jp_1916_;
}
else
{
lean_dec(v_entryDecl_x3f_1912_);
lean_dec(v_b_1905_);
v_declName_1917_ = v___x_1915_;
goto v___jp_1916_;
}
v___jp_1916_:
{
uint8_t v___x_1918_; 
v___x_1918_ = 1;
if (v_logWrites_1911_ == 0)
{
lean_object* v___x_1919_; 
lean_dec(v_declName_1917_);
v___x_1919_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1907_, v_env_1904_, v___f_1914_, v_asyncMode_1910_, v___x_1915_, v___x_1918_);
lean_dec(v_asyncMode_1910_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = l_Lean_Environment_logDeclChange(v_env_1904_, v_declName_1917_);
v___x_1921_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1907_, v___x_1920_, v___f_1914_, v_asyncMode_1910_, v___x_1915_, v___x_1918_);
lean_dec(v_asyncMode_1910_);
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_00_u03c3_1926_, lean_object* v_ext_1927_, lean_object* v_env_1928_, lean_object* v_b_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1927_, v_env_1928_, v_b_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1931_, lean_object* v_env_1932_, lean_object* v_namespaceName_1933_, lean_object* v_b_1934_){
_start:
{
lean_object* v_ext_1935_; lean_object* v_toEnvExtension_1936_; lean_object* v_descr_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1958_; 
v_ext_1935_ = lean_ctor_get(v_ext_1931_, 1);
lean_inc_ref(v_ext_1935_);
v_toEnvExtension_1936_ = lean_ctor_get(v_ext_1935_, 0);
lean_inc_ref(v_toEnvExtension_1936_);
v_descr_1937_ = lean_ctor_get(v_ext_1931_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_ext_1931_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_ext_1931_, 1);
lean_dec(v_unused_1959_);
v___x_1939_ = v_ext_1931_;
v_isShared_1940_ = v_isSharedCheck_1958_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_descr_1937_);
lean_dec(v_ext_1931_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1958_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_addEntryFn_1941_; lean_object* v_asyncMode_1942_; uint8_t v_logWrites_1943_; lean_object* v_entryDecl_x3f_1944_; lean_object* v___x_1946_; 
v_addEntryFn_1941_ = lean_ctor_get(v_ext_1935_, 3);
lean_inc(v_addEntryFn_1941_);
lean_dec_ref(v_ext_1935_);
v_asyncMode_1942_ = lean_ctor_get(v_toEnvExtension_1936_, 2);
lean_inc(v_asyncMode_1942_);
v_logWrites_1943_ = lean_ctor_get_uint8(v_toEnvExtension_1936_, sizeof(void*)*6);
v_entryDecl_x3f_1944_ = lean_ctor_get(v_descr_1937_, 7);
lean_inc(v_entryDecl_x3f_1944_);
lean_dec_ref(v_descr_1937_);
lean_inc(v_b_1934_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 1);
lean_ctor_set(v___x_1939_, 1, v_b_1934_);
lean_ctor_set(v___x_1939_, 0, v_namespaceName_1933_);
v___x_1946_ = v___x_1939_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_namespaceName_1933_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_b_1934_);
v___x_1946_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___f_1947_; lean_object* v___x_1948_; lean_object* v_declName_1950_; 
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1947_, 0, v_addEntryFn_1941_);
lean_closure_set(v___f_1947_, 1, v___x_1946_);
v___x_1948_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1944_) == 1)
{
lean_object* v_val_1955_; lean_object* v___x_1956_; 
v_val_1955_ = lean_ctor_get(v_entryDecl_x3f_1944_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v_entryDecl_x3f_1944_, 1);
v___x_1956_ = lean_apply_1(v_val_1955_, v_b_1934_);
v_declName_1950_ = v___x_1956_;
goto v___jp_1949_;
}
else
{
lean_dec(v_entryDecl_x3f_1944_);
lean_dec(v_b_1934_);
v_declName_1950_ = v___x_1948_;
goto v___jp_1949_;
}
v___jp_1949_:
{
uint8_t v___x_1951_; 
v___x_1951_ = 1;
if (v_logWrites_1943_ == 0)
{
lean_object* v___x_1952_; 
lean_dec(v_declName_1950_);
v___x_1952_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1936_, v_env_1932_, v___f_1947_, v_asyncMode_1942_, v___x_1948_, v___x_1951_);
lean_dec(v_asyncMode_1942_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_Lean_Environment_logDeclChange(v_env_1932_, v_declName_1950_);
v___x_1954_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1936_, v___x_1953_, v___f_1947_, v_asyncMode_1942_, v___x_1948_, v___x_1951_);
lean_dec(v_asyncMode_1942_);
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_00_u03c3_1962_, lean_object* v_ext_1963_, lean_object* v_env_1964_, lean_object* v_namespaceName_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1963_, v_env_1964_, v_namespaceName_1965_, v_b_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1968_, lean_object* v_states_1969_, lean_object* v_b_1970_){
_start:
{
if (lean_obj_tag(v_states_1969_) == 0)
{
lean_dec(v_b_1970_);
lean_dec_ref(v_ext_1968_);
return v_states_1969_;
}
else
{
lean_object* v_descr_1971_; lean_object* v_head_1972_; lean_object* v_tail_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2000_; 
v_descr_1971_ = lean_ctor_get(v_ext_1968_, 0);
v_head_1972_ = lean_ctor_get(v_states_1969_, 0);
v_tail_1973_ = lean_ctor_get(v_states_1969_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_states_1969_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1975_ = v_states_1969_;
v_isShared_1976_ = v_isSharedCheck_2000_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_tail_1973_);
lean_inc(v_head_1972_);
lean_dec(v_states_1969_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2000_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_addEntry_1977_; lean_object* v_state_1978_; lean_object* v_activeScopes_1979_; uint8_t v_delimitsLocal_1980_; uint8_t v_scopeChanged_1981_; lean_object* v_scopeChangedDecls_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1999_; 
v_addEntry_1977_ = lean_ctor_get(v_descr_1971_, 4);
v_state_1978_ = lean_ctor_get(v_head_1972_, 0);
v_activeScopes_1979_ = lean_ctor_get(v_head_1972_, 1);
v_delimitsLocal_1980_ = lean_ctor_get_uint8(v_head_1972_, sizeof(void*)*3);
v_scopeChanged_1981_ = lean_ctor_get_uint8(v_head_1972_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1982_ = lean_ctor_get(v_head_1972_, 2);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_head_1972_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1984_ = v_head_1972_;
v_isShared_1985_ = v_isSharedCheck_1999_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_scopeChangedDecls_1982_);
lean_inc(v_activeScopes_1979_);
lean_inc(v_state_1978_);
lean_dec(v_head_1972_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1999_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_inc(v_addEntry_1977_);
lean_inc(v_b_1970_);
v___x_1986_ = lean_apply_2(v_addEntry_1977_, v_state_1978_, v_b_1970_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_activeScopes_1979_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_scopeChangedDecls_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1998_, sizeof(void*)*3, v_delimitsLocal_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1998_, sizeof(void*)*3 + 1, v_scopeChanged_1981_);
v___x_1988_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v_top_1989_; uint8_t v_delimitsLocal_1990_; 
lean_inc(v_b_1970_);
lean_inc_ref(v_descr_1971_);
v_top_1989_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1971_, v___x_1988_, v_b_1970_);
v_delimitsLocal_1990_ = lean_ctor_get_uint8(v_top_1989_, sizeof(void*)*3);
if (v_delimitsLocal_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = l_Lean_stateStackModify___redArg(v_ext_1968_, v_tail_1973_, v_b_1970_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_1991_);
lean_ctor_set(v___x_1975_, 0, v_top_1989_);
v___x_1993_ = v___x_1975_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_top_1989_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_b_1970_);
lean_dec_ref(v_ext_1968_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_top_1989_);
v___x_1996_ = v___x_1975_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_top_1989_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_tail_1973_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_00_u03c3_2003_, lean_object* v_ext_2004_, lean_object* v_states_2005_, lean_object* v_b_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_stateStackModify___redArg(v_ext_2004_, v_states_2005_, v_b_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_2008_, lean_object* v_b_2009_, lean_object* v_ps_2010_){
_start:
{
lean_object* v_state_2011_; lean_object* v_importedEntries_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2030_; 
v_state_2011_ = lean_ctor_get(v_ps_2010_, 1);
v_importedEntries_2012_ = lean_ctor_get(v_ps_2010_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_ps_2010_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2014_ = v_ps_2010_;
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_state_2011_);
lean_inc(v_importedEntries_2012_);
lean_dec(v_ps_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_stateStack_2016_; lean_object* v_scopedEntries_2017_; lean_object* v_newEntries_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2029_; 
v_stateStack_2016_ = lean_ctor_get(v_state_2011_, 0);
v_scopedEntries_2017_ = lean_ctor_get(v_state_2011_, 1);
v_newEntries_2018_ = lean_ctor_get(v_state_2011_, 2);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_state_2011_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2020_ = v_state_2011_;
v_isShared_2021_ = v_isSharedCheck_2029_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_newEntries_2018_);
lean_inc(v_scopedEntries_2017_);
lean_inc(v_stateStack_2016_);
lean_dec(v_state_2011_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2029_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = l_Lean_stateStackModify___redArg(v_ext_2008_, v_stateStack_2016_, v_b_2009_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_scopedEntries_2017_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_newEntries_2018_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v___x_2024_);
v___x_2026_ = v___x_2014_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_importedEntries_2012_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_2031_, lean_object* v_env_2032_, lean_object* v_b_2033_){
_start:
{
lean_object* v_descr_2034_; lean_object* v_ext_2035_; lean_object* v_entryDecl_x3f_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v_declName_2042_; 
v_descr_2034_ = lean_ctor_get(v_ext_2031_, 0);
v_ext_2035_ = lean_ctor_get(v_ext_2031_, 1);
lean_inc_ref(v_ext_2035_);
v_entryDecl_x3f_2036_ = lean_ctor_get(v_descr_2034_, 7);
lean_inc(v_entryDecl_x3f_2036_);
lean_inc(v_b_2033_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2037_, 0, v_ext_2031_);
lean_closure_set(v___f_2037_, 1, v_b_2033_);
v___x_2038_ = lean_box(1);
v___x_2039_ = lean_box(0);
v___x_2040_ = 1;
if (lean_obj_tag(v_entryDecl_x3f_2036_) == 1)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; 
v_val_2048_ = lean_ctor_get(v_entryDecl_x3f_2036_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v_entryDecl_x3f_2036_, 1);
v___x_2049_ = lean_apply_1(v_val_2048_, v_b_2033_);
v_declName_2042_ = v___x_2049_;
goto v___jp_2041_;
}
else
{
lean_dec(v_entryDecl_x3f_2036_);
lean_dec(v_b_2033_);
v_declName_2042_ = v___x_2039_;
goto v___jp_2041_;
}
v___jp_2041_:
{
lean_object* v_toEnvExtension_2043_; uint8_t v_logWrites_2044_; 
v_toEnvExtension_2043_ = lean_ctor_get(v_ext_2035_, 0);
lean_inc_ref(v_toEnvExtension_2043_);
lean_dec_ref(v_ext_2035_);
v_logWrites_2044_ = lean_ctor_get_uint8(v_toEnvExtension_2043_, sizeof(void*)*6);
if (v_logWrites_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v_declName_2042_);
v___x_2045_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2043_, v_env_2032_, v___f_2037_, v___x_2038_, v___x_2039_, v___x_2040_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = l_Lean_Environment_logDeclChange(v_env_2032_, v_declName_2042_);
v___x_2047_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2043_, v___x_2046_, v___f_2037_, v___x_2038_, v___x_2039_, v___x_2040_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_00_u03c3_2052_, lean_object* v_ext_2053_, lean_object* v_env_2054_, lean_object* v_b_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2053_, v_env_2054_, v_b_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_2057_, lean_object* v_ext_2058_, lean_object* v_b_2059_, uint8_t v_kind_2060_, lean_object* v_namespaceName_2061_){
_start:
{
switch(v_kind_2060_)
{
case 0:
{
lean_object* v___x_2062_; 
lean_dec(v_namespaceName_2061_);
v___x_2062_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_2058_, v_env_2057_, v_b_2059_);
return v___x_2062_;
}
case 1:
{
lean_object* v___x_2063_; 
lean_dec(v_namespaceName_2061_);
v___x_2063_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2058_, v_env_2057_, v_b_2059_);
return v___x_2063_;
}
default: 
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2058_, v_env_2057_, v_namespaceName_2061_, v_b_2059_);
return v___x_2064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_2065_, lean_object* v_ext_2066_, lean_object* v_b_2067_, lean_object* v_kind_2068_, lean_object* v_namespaceName_2069_){
_start:
{
uint8_t v_kind_boxed_2070_; lean_object* v_res_2071_; 
v_kind_boxed_2070_ = lean_unbox(v_kind_2068_);
v_res_2071_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2065_, v_ext_2066_, v_b_2067_, v_kind_boxed_2070_, v_namespaceName_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_2072_, lean_object* v_00_u03b2_2073_, lean_object* v_00_u03c3_2074_, lean_object* v_env_2075_, lean_object* v_ext_2076_, lean_object* v_b_2077_, uint8_t v_kind_2078_, lean_object* v_namespaceName_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2075_, v_ext_2076_, v_b_2077_, v_kind_2078_, v_namespaceName_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_00_u03b2_2082_, lean_object* v_00_u03c3_2083_, lean_object* v_env_2084_, lean_object* v_ext_2085_, lean_object* v_b_2086_, lean_object* v_kind_2087_, lean_object* v_namespaceName_2088_){
_start:
{
uint8_t v_kind_boxed_2089_; lean_object* v_res_2090_; 
v_kind_boxed_2089_ = lean_unbox(v_kind_2087_);
v_res_2090_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_2081_, v_00_u03b2_2082_, v_00_u03c3_2083_, v_env_2084_, v_ext_2085_, v_b_2086_, v_kind_boxed_2089_, v_namespaceName_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_2091_, lean_object* v_b_2092_, uint8_t v_kind_2093_, lean_object* v_ns_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_2095_, v_ext_2091_, v_b_2092_, v_kind_2093_, v_ns_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_2097_, lean_object* v_b_2098_, lean_object* v_kind_2099_, lean_object* v_ns_2100_, lean_object* v_x_2101_){
_start:
{
uint8_t v_kind_boxed_2102_; lean_object* v_res_2103_; 
v_kind_boxed_2102_ = lean_unbox(v_kind_2099_);
v_res_2103_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_2097_, v_b_2098_, v_kind_boxed_2102_, v_ns_2100_, v_x_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_2104_, lean_object* v_ext_2105_, lean_object* v_b_2106_, uint8_t v_kind_2107_, lean_object* v_ns_2108_){
_start:
{
lean_object* v_modifyEnv_2109_; lean_object* v___x_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; 
v_modifyEnv_2109_ = lean_ctor_get(v_inst_2104_, 1);
lean_inc(v_modifyEnv_2109_);
lean_dec_ref(v_inst_2104_);
v___x_2110_ = lean_box(v_kind_2107_);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2111_, 0, v_ext_2105_);
lean_closure_set(v___f_2111_, 1, v_b_2106_);
lean_closure_set(v___f_2111_, 2, v___x_2110_);
lean_closure_set(v___f_2111_, 3, v_ns_2108_);
v___x_2112_ = lean_apply_1(v_modifyEnv_2109_, v___f_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_2113_, lean_object* v_ext_2114_, lean_object* v_b_2115_, lean_object* v_kind_2116_, lean_object* v_ns_2117_){
_start:
{
uint8_t v_kind_boxed_2118_; lean_object* v_res_2119_; 
v_kind_boxed_2118_ = lean_unbox(v_kind_2116_);
v_res_2119_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_2113_, v_ext_2114_, v_b_2115_, v_kind_boxed_2118_, v_ns_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_ext_2123_, lean_object* v_b_2124_, uint8_t v_kind_2125_){
_start:
{
lean_object* v_toBind_2126_; lean_object* v_getCurrNamespace_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; 
v_toBind_2126_ = lean_ctor_get(v_inst_2120_, 1);
lean_inc(v_toBind_2126_);
lean_dec_ref(v_inst_2120_);
v_getCurrNamespace_2127_ = lean_ctor_get(v_inst_2121_, 0);
lean_inc(v_getCurrNamespace_2127_);
lean_dec_ref(v_inst_2121_);
v___x_2128_ = lean_box(v_kind_2125_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2129_, 0, v_inst_2122_);
lean_closure_set(v___f_2129_, 1, v_ext_2123_);
lean_closure_set(v___f_2129_, 2, v_b_2124_);
lean_closure_set(v___f_2129_, 3, v___x_2128_);
v___x_2130_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v_getCurrNamespace_2127_, v___f_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_ext_2134_, lean_object* v_b_2135_, lean_object* v_kind_2136_){
_start:
{
uint8_t v_kind_boxed_2137_; lean_object* v_res_2138_; 
v_kind_boxed_2137_ = lean_unbox(v_kind_2136_);
v_res_2138_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2131_, v_inst_2132_, v_inst_2133_, v_ext_2134_, v_b_2135_, v_kind_boxed_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_2139_, lean_object* v_00_u03b1_2140_, lean_object* v_00_u03b2_2141_, lean_object* v_00_u03c3_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_ext_2146_, lean_object* v_b_2147_, uint8_t v_kind_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2143_, v_inst_2144_, v_inst_2145_, v_ext_2146_, v_b_2147_, v_kind_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_2150_, lean_object* v_00_u03b1_2151_, lean_object* v_00_u03b2_2152_, lean_object* v_00_u03c3_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_ext_2157_, lean_object* v_b_2158_, lean_object* v_kind_2159_){
_start:
{
uint8_t v_kind_boxed_2160_; lean_object* v_res_2161_; 
v_kind_boxed_2160_ = lean_unbox(v_kind_2159_);
v_res_2161_ = l_Lean_ScopedEnvExtension_add(v_m_2150_, v_00_u03b1_2151_, v_00_u03b2_2152_, v_00_u03c3_2153_, v_inst_2154_, v_inst_2155_, v_inst_2156_, v_ext_2157_, v_b_2158_, v_kind_boxed_2160_);
return v_res_2161_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2165_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_2166_ = lean_unsigned_to_nat(16u);
v___x_2167_ = lean_unsigned_to_nat(285u);
v___x_2168_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_2169_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_2170_ = l_mkPanicMessageWithDecl(v___x_2169_, v___x_2168_, v___x_2167_, v___x_2166_, v___x_2165_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_2171_, lean_object* v_ext_2172_, lean_object* v_env_2173_, lean_object* v_asyncMode_2174_, uint8_t v_genRecorded_2175_){
_start:
{
lean_object* v_ext_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_stateStack_2180_; 
v_ext_2176_ = lean_ctor_get(v_ext_2172_, 1);
v___x_2177_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2178_ = lean_box(0);
v___x_2179_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2177_, v_ext_2176_, v_env_2173_, v_asyncMode_2174_, v___x_2178_, v_genRecorded_2175_);
v_stateStack_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_stateStack_2180_);
lean_dec(v___x_2179_);
if (lean_obj_tag(v_stateStack_2180_) == 1)
{
lean_object* v_head_2181_; lean_object* v_state_2182_; 
v_head_2181_ = lean_ctor_get(v_stateStack_2180_, 0);
lean_inc(v_head_2181_);
lean_dec_ref_known(v_stateStack_2180_, 2);
v_state_2182_ = lean_ctor_get(v_head_2181_, 0);
lean_inc(v_state_2182_);
lean_dec(v_head_2181_);
return v_state_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v_stateStack_2180_);
v___x_2183_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_2184_ = l_panic___redArg(v_inst_2171_, v___x_2183_);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_2185_, lean_object* v_ext_2186_, lean_object* v_env_2187_, lean_object* v_asyncMode_2188_, lean_object* v_genRecorded_2189_){
_start:
{
uint8_t v_genRecorded_boxed_2190_; lean_object* v_res_2191_; 
v_genRecorded_boxed_2190_ = lean_unbox(v_genRecorded_2189_);
v_res_2191_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2185_, v_ext_2186_, v_env_2187_, v_asyncMode_2188_, v_genRecorded_boxed_2190_);
lean_dec(v_asyncMode_2188_);
lean_dec_ref(v_ext_2186_);
lean_dec(v_inst_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_2192_, lean_object* v_00_u03b1_2193_, lean_object* v_00_u03b2_2194_, lean_object* v_inst_2195_, lean_object* v_ext_2196_, lean_object* v_env_2197_, lean_object* v_asyncMode_2198_, uint8_t v_genRecorded_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2195_, v_ext_2196_, v_env_2197_, v_asyncMode_2198_, v_genRecorded_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_2201_, lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_inst_2204_, lean_object* v_ext_2205_, lean_object* v_env_2206_, lean_object* v_asyncMode_2207_, lean_object* v_genRecorded_2208_){
_start:
{
uint8_t v_genRecorded_boxed_2209_; lean_object* v_res_2210_; 
v_genRecorded_boxed_2209_ = lean_unbox(v_genRecorded_2208_);
v_res_2210_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_2201_, v_00_u03b1_2202_, v_00_u03b2_2203_, v_inst_2204_, v_ext_2205_, v_env_2206_, v_asyncMode_2207_, v_genRecorded_boxed_2209_);
lean_dec(v_asyncMode_2207_);
lean_dec_ref(v_ext_2205_);
lean_dec(v_inst_2204_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v___y_2211_, lean_object* v_tail_2212_, lean_object* v_s_2213_){
_start:
{
lean_object* v_scopedEntries_2214_; lean_object* v_newEntries_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
v_scopedEntries_2214_ = lean_ctor_get(v_s_2213_, 1);
v_newEntries_2215_ = lean_ctor_get(v_s_2213_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_s_2213_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v_s_2213_, 0);
lean_dec(v_unused_2224_);
v___x_2217_ = v_s_2213_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_newEntries_2215_);
lean_inc(v_scopedEntries_2214_);
lean_dec(v_s_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2211_);
lean_ctor_set(v___x_2219_, 1, v_tail_2212_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2219_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_scopedEntries_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_newEntries_2215_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(lean_object* v_ext_2225_, lean_object* v_as_2226_, size_t v_i_2227_, size_t v_stop_2228_, lean_object* v_b_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_eq(v_i_2227_, v_stop_2228_);
if (v___x_2230_ == 0)
{
lean_object* v_descr_2231_; lean_object* v_addEntry_2232_; lean_object* v_state_2233_; lean_object* v_activeScopes_2234_; uint8_t v_delimitsLocal_2235_; uint8_t v_scopeChanged_2236_; lean_object* v_scopeChangedDecls_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2250_; 
v_descr_2231_ = lean_ctor_get(v_ext_2225_, 0);
v_addEntry_2232_ = lean_ctor_get(v_descr_2231_, 4);
v_state_2233_ = lean_ctor_get(v_b_2229_, 0);
v_activeScopes_2234_ = lean_ctor_get(v_b_2229_, 1);
v_delimitsLocal_2235_ = lean_ctor_get_uint8(v_b_2229_, sizeof(void*)*3);
v_scopeChanged_2236_ = lean_ctor_get_uint8(v_b_2229_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2237_ = lean_ctor_get(v_b_2229_, 2);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_b_2229_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2239_ = v_b_2229_;
v_isShared_2240_ = v_isSharedCheck_2250_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_scopeChangedDecls_2237_);
lean_inc(v_activeScopes_2234_);
lean_inc(v_state_2233_);
lean_dec(v_b_2229_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2250_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = lean_array_uget_borrowed(v_as_2226_, v_i_2227_);
lean_inc(v_addEntry_2232_);
lean_inc(v___x_2241_);
v___x_2242_ = lean_apply_2(v_addEntry_2232_, v_state_2233_, v___x_2241_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_activeScopes_2234_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_scopeChangedDecls_2237_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*3, v_delimitsLocal_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*3 + 1, v_scopeChanged_2236_);
v___x_2244_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; 
lean_inc(v___x_2241_);
lean_inc_ref(v_descr_2231_);
v___x_2245_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2231_, v___x_2244_, v___x_2241_);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_add(v_i_2227_, v___x_2246_);
v_i_2227_ = v___x_2247_;
v_b_2229_ = v___x_2245_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ext_2225_);
return v_b_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg___boxed(lean_object* v_ext_2251_, lean_object* v_as_2252_, lean_object* v_i_2253_, lean_object* v_stop_2254_, lean_object* v_b_2255_){
_start:
{
size_t v_i_boxed_2256_; size_t v_stop_boxed_2257_; lean_object* v_res_2258_; 
v_i_boxed_2256_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_stop_boxed_2257_ = lean_unbox_usize(v_stop_2254_);
lean_dec(v_stop_2254_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2251_, v_as_2252_, v_i_boxed_2256_, v_stop_boxed_2257_, v_b_2255_);
lean_dec_ref(v_as_2252_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(lean_object* v_ext_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v_cs_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_cs_2262_ = lean_ctor_get(v_x_2260_, 0);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_array_get_size(v_cs_2262_);
v___x_2265_ = lean_nat_dec_lt(v___x_2263_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v_ext_2259_);
return v_x_2261_;
}
else
{
size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = lean_usize_of_nat(v___x_2264_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2259_, v_cs_2262_, v___x_2266_, v___x_2267_, v_x_2261_);
return v___x_2268_;
}
}
else
{
lean_object* v_vs_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_vs_2269_ = lean_ctor_get(v_x_2260_, 0);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_array_get_size(v_vs_2269_);
v___x_2272_ = lean_nat_dec_lt(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v_ext_2259_);
return v_x_2261_;
}
else
{
size_t v___x_2273_; size_t v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = ((size_t)0ULL);
v___x_2274_ = lean_usize_of_nat(v___x_2271_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2259_, v_vs_2269_, v___x_2273_, v___x_2274_, v_x_2261_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(lean_object* v_ext_2276_, lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_, lean_object* v_b_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_eq(v_i_2278_, v_stop_2279_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; 
v___x_2282_ = lean_array_uget_borrowed(v_as_2277_, v_i_2278_);
lean_inc_ref(v_ext_2276_);
v___x_2283_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2276_, v___x_2282_, v_b_2280_);
v___x_2284_ = ((size_t)1ULL);
v___x_2285_ = lean_usize_add(v_i_2278_, v___x_2284_);
v_i_2278_ = v___x_2285_;
v_b_2280_ = v___x_2283_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2276_);
return v_b_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ext_2287_, lean_object* v_as_2288_, lean_object* v_i_2289_, lean_object* v_stop_2290_, lean_object* v_b_2291_){
_start:
{
size_t v_i_boxed_2292_; size_t v_stop_boxed_2293_; lean_object* v_res_2294_; 
v_i_boxed_2292_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_stop_boxed_2293_ = lean_unbox_usize(v_stop_2290_);
lean_dec(v_stop_2290_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2287_, v_as_2288_, v_i_boxed_2292_, v_stop_boxed_2293_, v_b_2291_);
lean_dec_ref(v_as_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg___boxed(lean_object* v_ext_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2295_, v_x_2296_, v_x_2297_);
lean_dec_ref(v_x_2296_);
return v_res_2298_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(lean_object* v_ext_2300_, lean_object* v_x_2301_, size_t v_x_2302_, size_t v_x_2303_, lean_object* v_x_2304_){
_start:
{
if (lean_obj_tag(v_x_2301_) == 0)
{
lean_object* v_cs_2305_; lean_object* v___x_2306_; size_t v___x_2307_; lean_object* v_j_2308_; lean_object* v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; size_t v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_cs_2305_ = lean_ctor_get(v_x_2301_, 0);
v___x_2306_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2307_ = lean_usize_shift_right(v_x_2302_, v_x_2303_);
v_j_2308_ = lean_usize_to_nat(v___x_2307_);
v___x_2309_ = lean_array_get_borrowed(v___x_2306_, v_cs_2305_, v_j_2308_);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_shift_left(v___x_2310_, v_x_2303_);
v___x_2312_ = lean_usize_sub(v___x_2311_, v___x_2310_);
v___x_2313_ = lean_usize_land(v_x_2302_, v___x_2312_);
v___x_2314_ = ((size_t)5ULL);
v___x_2315_ = lean_usize_sub(v_x_2303_, v___x_2314_);
lean_inc_ref(v_ext_2300_);
v___x_2316_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2300_, v___x_2309_, v___x_2313_, v___x_2315_, v_x_2304_);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_add(v_j_2308_, v___x_2317_);
lean_dec(v_j_2308_);
v___x_2319_ = lean_array_get_size(v_cs_2305_);
v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec(v___x_2318_);
lean_dec_ref(v_ext_2300_);
return v___x_2316_;
}
else
{
size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_usize_of_nat(v___x_2318_);
lean_dec(v___x_2318_);
v___x_2322_ = lean_usize_of_nat(v___x_2319_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2300_, v_cs_2305_, v___x_2321_, v___x_2322_, v___x_2316_);
return v___x_2323_;
}
}
else
{
lean_object* v_vs_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_vs_2324_ = lean_ctor_get(v_x_2301_, 0);
v___x_2325_ = lean_usize_to_nat(v_x_2302_);
v___x_2326_ = lean_array_get_size(v_vs_2324_);
v___x_2327_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec(v___x_2325_);
lean_dec_ref(v_ext_2300_);
return v_x_2304_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_usize_of_nat(v___x_2325_);
lean_dec(v___x_2325_);
v___x_2329_ = lean_usize_of_nat(v___x_2326_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2300_, v_vs_2324_, v___x_2328_, v___x_2329_, v_x_2304_);
return v___x_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
size_t v_x_2633__boxed_2336_; size_t v_x_2634__boxed_2337_; lean_object* v_res_2338_; 
v_x_2633__boxed_2336_ = lean_unbox_usize(v_x_2333_);
lean_dec(v_x_2333_);
v_x_2634__boxed_2337_ = lean_unbox_usize(v_x_2334_);
lean_dec(v_x_2334_);
v_res_2338_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2331_, v_x_2332_, v_x_2633__boxed_2336_, v_x_2634__boxed_2337_, v_x_2335_);
lean_dec_ref(v_x_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(lean_object* v_ext_2339_, lean_object* v_t_2340_, lean_object* v_init_2341_, lean_object* v_start_2342_){
_start:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = lean_nat_dec_eq(v_start_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v_root_2345_; lean_object* v_tail_2346_; size_t v_shift_2347_; lean_object* v_tailOff_2348_; uint8_t v___x_2349_; 
v_root_2345_ = lean_ctor_get(v_t_2340_, 0);
v_tail_2346_ = lean_ctor_get(v_t_2340_, 1);
v_shift_2347_ = lean_ctor_get_usize(v_t_2340_, 4);
v_tailOff_2348_ = lean_ctor_get(v_t_2340_, 3);
v___x_2349_ = lean_nat_dec_le(v_tailOff_2348_, v_start_2342_);
if (v___x_2349_ == 0)
{
size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2350_ = lean_usize_of_nat(v_start_2342_);
lean_inc_ref(v_ext_2339_);
v___x_2351_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2339_, v_root_2345_, v___x_2350_, v_shift_2347_, v_init_2341_);
v___x_2352_ = lean_array_get_size(v_tail_2346_);
v___x_2353_ = lean_nat_dec_lt(v___x_2343_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v_ext_2339_);
return v___x_2351_;
}
else
{
size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = lean_usize_of_nat(v___x_2352_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2339_, v_tail_2346_, v___x_2354_, v___x_2355_, v___x_2351_);
return v___x_2356_;
}
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_nat_sub(v_start_2342_, v_tailOff_2348_);
v___x_2358_ = lean_array_get_size(v_tail_2346_);
v___x_2359_ = lean_nat_dec_lt(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec(v___x_2357_);
lean_dec_ref(v_ext_2339_);
return v_init_2341_;
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_usize_of_nat(v___x_2357_);
lean_dec(v___x_2357_);
v___x_2361_ = lean_usize_of_nat(v___x_2358_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2339_, v_tail_2346_, v___x_2360_, v___x_2361_, v_init_2341_);
return v___x_2362_;
}
}
}
else
{
lean_object* v_root_2363_; lean_object* v_tail_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_root_2363_ = lean_ctor_get(v_t_2340_, 0);
v_tail_2364_ = lean_ctor_get(v_t_2340_, 1);
lean_inc_ref(v_ext_2339_);
v___x_2365_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2339_, v_root_2363_, v_init_2341_);
v___x_2366_ = lean_array_get_size(v_tail_2364_);
v___x_2367_ = lean_nat_dec_lt(v___x_2343_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec_ref(v_ext_2339_);
return v___x_2365_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = lean_usize_of_nat(v___x_2366_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2339_, v_tail_2364_, v___x_2368_, v___x_2369_, v___x_2365_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg___boxed(lean_object* v_ext_2371_, lean_object* v_t_2372_, lean_object* v_init_2373_, lean_object* v_start_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2371_, v_t_2372_, v_init_2373_, v_start_2374_);
lean_dec(v_start_2374_);
lean_dec_ref(v_t_2372_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_val_2376_, lean_object* v_as_2377_, size_t v_i_2378_, size_t v_stop_2379_, lean_object* v_b_2380_){
_start:
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_usize_dec_eq(v_i_2378_, v_stop_2379_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; size_t v___x_2385_; size_t v___x_2386_; 
v___x_2382_ = lean_array_uget_borrowed(v_as_2377_, v_i_2378_);
lean_inc_ref(v_val_2376_);
lean_inc(v___x_2382_);
v___x_2383_ = lean_apply_1(v_val_2376_, v___x_2382_);
v___x_2384_ = lean_array_push(v_b_2380_, v___x_2383_);
v___x_2385_ = ((size_t)1ULL);
v___x_2386_ = lean_usize_add(v_i_2378_, v___x_2385_);
v_i_2378_ = v___x_2386_;
v_b_2380_ = v___x_2384_;
goto _start;
}
else
{
lean_dec_ref(v_val_2376_);
return v_b_2380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_val_2388_, lean_object* v_as_2389_, lean_object* v_i_2390_, lean_object* v_stop_2391_, lean_object* v_b_2392_){
_start:
{
size_t v_i_boxed_2393_; size_t v_stop_boxed_2394_; lean_object* v_res_2395_; 
v_i_boxed_2393_ = lean_unbox_usize(v_i_2390_);
lean_dec(v_i_2390_);
v_stop_boxed_2394_ = lean_unbox_usize(v_stop_2391_);
lean_dec(v_stop_2391_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2388_, v_as_2389_, v_i_boxed_2393_, v_stop_boxed_2394_, v_b_2392_);
lean_dec_ref(v_as_2389_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object* v_val_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
if (lean_obj_tag(v_x_2397_) == 0)
{
lean_object* v_cs_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v_cs_2399_ = lean_ctor_get(v_x_2397_, 0);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_array_get_size(v_cs_2399_);
v___x_2402_ = lean_nat_dec_lt(v___x_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v_val_2396_);
return v_x_2398_;
}
else
{
size_t v___x_2403_; size_t v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = ((size_t)0ULL);
v___x_2404_ = lean_usize_of_nat(v___x_2401_);
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2396_, v_cs_2399_, v___x_2403_, v___x_2404_, v_x_2398_);
return v___x_2405_;
}
}
else
{
lean_object* v_vs_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v_vs_2406_ = lean_ctor_get(v_x_2397_, 0);
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2408_ = lean_array_get_size(v_vs_2406_);
v___x_2409_ = lean_nat_dec_lt(v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v_val_2396_);
return v_x_2398_;
}
else
{
size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = lean_usize_of_nat(v___x_2408_);
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2396_, v_vs_2406_, v___x_2410_, v___x_2411_, v_x_2398_);
return v___x_2412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_val_2413_, lean_object* v_as_2414_, size_t v_i_2415_, size_t v_stop_2416_, lean_object* v_b_2417_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_eq(v_i_2415_, v_stop_2416_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; size_t v___x_2421_; size_t v___x_2422_; 
v___x_2419_ = lean_array_uget_borrowed(v_as_2414_, v_i_2415_);
lean_inc_ref(v_val_2413_);
v___x_2420_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2413_, v___x_2419_, v_b_2417_);
v___x_2421_ = ((size_t)1ULL);
v___x_2422_ = lean_usize_add(v_i_2415_, v___x_2421_);
v_i_2415_ = v___x_2422_;
v_b_2417_ = v___x_2420_;
goto _start;
}
else
{
lean_dec_ref(v_val_2413_);
return v_b_2417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_val_2424_, lean_object* v_as_2425_, lean_object* v_i_2426_, lean_object* v_stop_2427_, lean_object* v_b_2428_){
_start:
{
size_t v_i_boxed_2429_; size_t v_stop_boxed_2430_; lean_object* v_res_2431_; 
v_i_boxed_2429_ = lean_unbox_usize(v_i_2426_);
lean_dec(v_i_2426_);
v_stop_boxed_2430_ = lean_unbox_usize(v_stop_2427_);
lean_dec(v_stop_2427_);
v_res_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2424_, v_as_2425_, v_i_boxed_2429_, v_stop_boxed_2430_, v_b_2428_);
lean_dec_ref(v_as_2425_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object* v_val_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2432_, v_x_2433_, v_x_2434_);
lean_dec_ref(v_x_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_val_2436_, lean_object* v_x_2437_, size_t v_x_2438_, size_t v_x_2439_, lean_object* v_x_2440_){
_start:
{
if (lean_obj_tag(v_x_2437_) == 0)
{
lean_object* v_cs_2441_; lean_object* v___x_2442_; size_t v___x_2443_; lean_object* v_j_2444_; lean_object* v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_cs_2441_ = lean_ctor_get(v_x_2437_, 0);
v___x_2442_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2443_ = lean_usize_shift_right(v_x_2438_, v_x_2439_);
v_j_2444_ = lean_usize_to_nat(v___x_2443_);
v___x_2445_ = lean_array_get_borrowed(v___x_2442_, v_cs_2441_, v_j_2444_);
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = lean_usize_shift_left(v___x_2446_, v_x_2439_);
v___x_2448_ = lean_usize_sub(v___x_2447_, v___x_2446_);
v___x_2449_ = lean_usize_land(v_x_2438_, v___x_2448_);
v___x_2450_ = ((size_t)5ULL);
v___x_2451_ = lean_usize_sub(v_x_2439_, v___x_2450_);
lean_inc_ref(v_val_2436_);
v___x_2452_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2436_, v___x_2445_, v___x_2449_, v___x_2451_, v_x_2440_);
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_nat_add(v_j_2444_, v___x_2453_);
lean_dec(v_j_2444_);
v___x_2455_ = lean_array_get_size(v_cs_2441_);
v___x_2456_ = lean_nat_dec_lt(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_dec(v___x_2454_);
lean_dec_ref(v_val_2436_);
return v___x_2452_;
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = lean_usize_of_nat(v___x_2454_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_usize_of_nat(v___x_2455_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2436_, v_cs_2441_, v___x_2457_, v___x_2458_, v___x_2452_);
return v___x_2459_;
}
}
else
{
lean_object* v_vs_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_vs_2460_ = lean_ctor_get(v_x_2437_, 0);
v___x_2461_ = lean_usize_to_nat(v_x_2438_);
v___x_2462_ = lean_array_get_size(v_vs_2460_);
v___x_2463_ = lean_nat_dec_lt(v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_dec(v___x_2461_);
lean_dec_ref(v_val_2436_);
return v_x_2440_;
}
else
{
size_t v___x_2464_; size_t v___x_2465_; lean_object* v___x_2466_; 
v___x_2464_ = lean_usize_of_nat(v___x_2461_);
lean_dec(v___x_2461_);
v___x_2465_ = lean_usize_of_nat(v___x_2462_);
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2436_, v_vs_2460_, v___x_2464_, v___x_2465_, v_x_2440_);
return v___x_2466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_val_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_){
_start:
{
size_t v_x_2811__boxed_2472_; size_t v_x_2812__boxed_2473_; lean_object* v_res_2474_; 
v_x_2811__boxed_2472_ = lean_unbox_usize(v_x_2469_);
lean_dec(v_x_2469_);
v_x_2812__boxed_2473_ = lean_unbox_usize(v_x_2470_);
lean_dec(v_x_2470_);
v_res_2474_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2467_, v_x_2468_, v_x_2811__boxed_2472_, v_x_2812__boxed_2473_, v_x_2471_);
lean_dec_ref(v_x_2468_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_val_2475_, lean_object* v_t_2476_, lean_object* v_init_2477_, lean_object* v_start_2478_){
_start:
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_nat_dec_eq(v_start_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v_root_2481_; lean_object* v_tail_2482_; size_t v_shift_2483_; lean_object* v_tailOff_2484_; uint8_t v___x_2485_; 
v_root_2481_ = lean_ctor_get(v_t_2476_, 0);
v_tail_2482_ = lean_ctor_get(v_t_2476_, 1);
v_shift_2483_ = lean_ctor_get_usize(v_t_2476_, 4);
v_tailOff_2484_ = lean_ctor_get(v_t_2476_, 3);
v___x_2485_ = lean_nat_dec_le(v_tailOff_2484_, v_start_2478_);
if (v___x_2485_ == 0)
{
size_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2486_ = lean_usize_of_nat(v_start_2478_);
lean_inc_ref(v_val_2475_);
v___x_2487_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2475_, v_root_2481_, v___x_2486_, v_shift_2483_, v_init_2477_);
v___x_2488_ = lean_array_get_size(v_tail_2482_);
v___x_2489_ = lean_nat_dec_lt(v___x_2479_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v_val_2475_);
return v___x_2487_;
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2488_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2475_, v_tail_2482_, v___x_2490_, v___x_2491_, v___x_2487_);
return v___x_2492_;
}
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2493_ = lean_nat_sub(v_start_2478_, v_tailOff_2484_);
v___x_2494_ = lean_array_get_size(v_tail_2482_);
v___x_2495_ = lean_nat_dec_lt(v___x_2493_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_dec(v___x_2493_);
lean_dec_ref(v_val_2475_);
return v_init_2477_;
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_usize_of_nat(v___x_2493_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_usize_of_nat(v___x_2494_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2475_, v_tail_2482_, v___x_2496_, v___x_2497_, v_init_2477_);
return v___x_2498_;
}
}
}
else
{
lean_object* v_root_2499_; lean_object* v_tail_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_root_2499_ = lean_ctor_get(v_t_2476_, 0);
v_tail_2500_ = lean_ctor_get(v_t_2476_, 1);
lean_inc_ref(v_val_2475_);
v___x_2501_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2475_, v_root_2499_, v_init_2477_);
v___x_2502_ = lean_array_get_size(v_tail_2500_);
v___x_2503_ = lean_nat_dec_lt(v___x_2479_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec_ref(v_val_2475_);
return v___x_2501_;
}
else
{
size_t v___x_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = lean_usize_of_nat(v___x_2502_);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2475_, v_tail_2500_, v___x_2504_, v___x_2505_, v___x_2501_);
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_val_2507_, lean_object* v_t_2508_, lean_object* v_init_2509_, lean_object* v_start_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2507_, v_t_2508_, v_init_2509_, v_start_2510_);
lean_dec(v_start_2510_);
lean_dec_ref(v_t_2508_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2512_, lean_object* v_env_2513_, lean_object* v_namespaceName_2514_){
_start:
{
lean_object* v_descr_2515_; lean_object* v_ext_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; lean_object* v_s_2521_; lean_object* v_stateStack_2522_; 
v_descr_2515_ = lean_ctor_get(v_ext_2512_, 0);
v_ext_2516_ = lean_ctor_get(v_ext_2512_, 1);
v___x_2517_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2518_ = lean_box(1);
v___x_2519_ = lean_box(0);
v___x_2520_ = 0;
lean_inc_ref(v_env_2513_);
v_s_2521_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2517_, v_ext_2516_, v_env_2513_, v___x_2518_, v___x_2519_, v___x_2520_);
v_stateStack_2522_ = lean_ctor_get(v_s_2521_, 0);
lean_inc(v_stateStack_2522_);
if (lean_obj_tag(v_stateStack_2522_) == 1)
{
lean_object* v_head_2523_; lean_object* v_scopedEntries_2524_; lean_object* v_tail_2525_; lean_object* v_state_2526_; lean_object* v_activeScopes_2527_; uint8_t v_delimitsLocal_2528_; uint8_t v_scopeChanged_2529_; lean_object* v_scopeChangedDecls_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2565_; 
v_head_2523_ = lean_ctor_get(v_stateStack_2522_, 0);
lean_inc(v_head_2523_);
v_scopedEntries_2524_ = lean_ctor_get(v_s_2521_, 1);
lean_inc_ref(v_scopedEntries_2524_);
lean_dec(v_s_2521_);
v_tail_2525_ = lean_ctor_get(v_stateStack_2522_, 1);
lean_inc(v_tail_2525_);
lean_dec_ref_known(v_stateStack_2522_, 2);
v_state_2526_ = lean_ctor_get(v_head_2523_, 0);
v_activeScopes_2527_ = lean_ctor_get(v_head_2523_, 1);
v_delimitsLocal_2528_ = lean_ctor_get_uint8(v_head_2523_, sizeof(void*)*3);
v_scopeChanged_2529_ = lean_ctor_get_uint8(v_head_2523_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2530_ = lean_ctor_get(v_head_2523_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_head_2523_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2532_ = v_head_2523_;
v_isShared_2533_ = v_isSharedCheck_2565_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_scopeChangedDecls_2530_);
lean_inc(v_activeScopes_2527_);
lean_inc(v_state_2526_);
lean_dec(v_head_2523_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2565_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Lean_NameSet_contains(v_activeScopes_2527_, v_namespaceName_2514_);
if (v___x_2534_ == 0)
{
lean_object* v_activeScopes_2535_; lean_object* v_bs_x3f_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2544_; lean_object* v___y_2547_; 
lean_inc(v_namespaceName_2514_);
v_activeScopes_2535_ = l_Lean_NameSet_insert(v_activeScopes_2527_, v_namespaceName_2514_);
v_bs_x3f_2536_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2524_, v_namespaceName_2514_);
lean_dec(v_namespaceName_2514_);
lean_dec_ref(v_scopedEntries_2524_);
if (lean_obj_tag(v_bs_x3f_2536_) == 1)
{
lean_object* v_val_2555_; uint8_t v___x_2556_; lean_object* v___x_2558_; 
v_val_2555_ = lean_ctor_get(v_bs_x3f_2536_, 0);
v___x_2556_ = 1;
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 1, v_activeScopes_2535_);
v___x_2558_ = v___x_2532_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_state_2526_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_activeScopes_2535_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_scopeChangedDecls_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*3 + 1, v_scopeChanged_2529_);
v___x_2558_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*3, v___x_2556_);
v___x_2559_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ext_2512_);
v___x_2560_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2512_, v_val_2555_, v___x_2558_, v___x_2559_);
v___y_2547_ = v___x_2560_;
goto v___jp_2546_;
}
}
else
{
lean_object* v___x_2563_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 1, v_activeScopes_2535_);
v___x_2563_ = v___x_2532_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_state_2526_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_activeScopes_2535_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_scopeChangedDecls_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2564_, sizeof(void*)*3, v_delimitsLocal_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2564_, sizeof(void*)*3 + 1, v_scopeChanged_2529_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
v___y_2547_ = v___x_2563_;
goto v___jp_2546_;
}
}
v___jp_2537_:
{
if (lean_obj_tag(v_bs_x3f_2536_) == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2512_, v_env_2513_, v___x_2534_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2539_);
return v___x_2540_;
}
else
{
uint8_t v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref_known(v_bs_x3f_2536_, 1);
v___x_2541_ = 1;
v___x_2542_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2512_, v_env_2513_, v___x_2541_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2539_);
return v___x_2542_;
}
}
v___jp_2543_:
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___y_2538_ = v___y_2544_;
v___y_2539_ = v___x_2545_;
goto v___jp_2537_;
}
v___jp_2546_:
{
lean_object* v___f_2548_; 
v___f_2548_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2548_, 0, v___y_2547_);
lean_closure_set(v___f_2548_, 1, v_tail_2525_);
if (lean_obj_tag(v_bs_x3f_2536_) == 1)
{
lean_object* v_entryDecl_x3f_2549_; 
v_entryDecl_x3f_2549_ = lean_ctor_get(v_descr_2515_, 7);
if (lean_obj_tag(v_entryDecl_x3f_2549_) == 1)
{
lean_object* v_val_2550_; lean_object* v_val_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_val_2550_ = lean_ctor_get(v_bs_x3f_2536_, 0);
v_val_2551_ = lean_ctor_get(v_entryDecl_x3f_2549_, 0);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
lean_inc(v_val_2551_);
v___x_2554_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2551_, v_val_2550_, v___x_2553_, v___x_2552_);
v___y_2538_ = v___f_2548_;
v___y_2539_ = v___x_2554_;
goto v___jp_2537_;
}
else
{
v___y_2544_ = v___f_2548_;
goto v___jp_2543_;
}
}
else
{
v___y_2544_ = v___f_2548_;
goto v___jp_2543_;
}
}
}
else
{
lean_del_object(v___x_2532_);
lean_dec_ref(v_scopeChangedDecls_2530_);
lean_dec(v_activeScopes_2527_);
lean_dec(v_state_2526_);
lean_dec(v_tail_2525_);
lean_dec_ref(v_scopedEntries_2524_);
lean_dec(v_namespaceName_2514_);
lean_dec_ref(v_ext_2512_);
return v_env_2513_;
}
}
}
else
{
lean_dec(v_stateStack_2522_);
lean_dec(v_s_2521_);
lean_dec(v_namespaceName_2514_);
lean_dec_ref(v_ext_2512_);
return v_env_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2566_, lean_object* v_00_u03b2_2567_, lean_object* v_00_u03c3_2568_, lean_object* v_ext_2569_, lean_object* v_env_2570_, lean_object* v_namespaceName_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2569_, v_env_2570_, v_namespaceName_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2573_, lean_object* v_val_2574_, lean_object* v_t_2575_, lean_object* v_init_2576_, lean_object* v_start_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2574_, v_t_2575_, v_init_2576_, v_start_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2579_, lean_object* v_val_2580_, lean_object* v_t_2581_, lean_object* v_init_2582_, lean_object* v_start_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2579_, v_val_2580_, v_t_2581_, v_init_2582_, v_start_2583_);
lean_dec(v_start_2583_);
lean_dec_ref(v_t_2581_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(lean_object* v_00_u03b2_2585_, lean_object* v_00_u03c3_2586_, lean_object* v_00_u03b1_2587_, lean_object* v_ext_2588_, lean_object* v_t_2589_, lean_object* v_init_2590_, lean_object* v_start_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2588_, v_t_2589_, v_init_2590_, v_start_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___boxed(lean_object* v_00_u03b2_2593_, lean_object* v_00_u03c3_2594_, lean_object* v_00_u03b1_2595_, lean_object* v_ext_2596_, lean_object* v_t_2597_, lean_object* v_init_2598_, lean_object* v_start_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(v_00_u03b2_2593_, v_00_u03c3_2594_, v_00_u03b1_2595_, v_ext_2596_, v_t_2597_, v_init_2598_, v_start_2599_);
lean_dec(v_start_2599_);
lean_dec_ref(v_t_2597_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2601_, lean_object* v_val_2602_, lean_object* v_x_2603_, size_t v_x_2604_, size_t v_x_2605_, lean_object* v_x_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2602_, v_x_2603_, v_x_2604_, v_x_2605_, v_x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_val_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
size_t v_x_3015__boxed_2614_; size_t v_x_3016__boxed_2615_; lean_object* v_res_2616_; 
v_x_3015__boxed_2614_ = lean_unbox_usize(v_x_2611_);
lean_dec(v_x_2611_);
v_x_3016__boxed_2615_ = lean_unbox_usize(v_x_2612_);
lean_dec(v_x_2612_);
v_res_2616_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2608_, v_val_2609_, v_x_2610_, v_x_3015__boxed_2614_, v_x_3016__boxed_2615_, v_x_2613_);
lean_dec_ref(v_x_2610_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2617_, lean_object* v_val_2618_, lean_object* v_as_2619_, size_t v_i_2620_, size_t v_stop_2621_, lean_object* v_b_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2618_, v_as_2619_, v_i_2620_, v_stop_2621_, v_b_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_val_2625_, lean_object* v_as_2626_, lean_object* v_i_2627_, lean_object* v_stop_2628_, lean_object* v_b_2629_){
_start:
{
size_t v_i_boxed_2630_; size_t v_stop_boxed_2631_; lean_object* v_res_2632_; 
v_i_boxed_2630_ = lean_unbox_usize(v_i_2627_);
lean_dec(v_i_2627_);
v_stop_boxed_2631_ = lean_unbox_usize(v_stop_2628_);
lean_dec(v_stop_2628_);
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2624_, v_val_2625_, v_as_2626_, v_i_boxed_2630_, v_stop_boxed_2631_, v_b_2629_);
lean_dec_ref(v_as_2626_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object* v_00_u03b2_2633_, lean_object* v_val_2634_, lean_object* v_x_2635_, lean_object* v_x_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2634_, v_x_2635_, v_x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2638_, lean_object* v_val_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(v_00_u03b2_2638_, v_val_2639_, v_x_2640_, v_x_2641_);
lean_dec_ref(v_x_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_object* v_00_u03b2_2643_, lean_object* v_00_u03c3_2644_, lean_object* v_00_u03b1_2645_, lean_object* v_ext_2646_, lean_object* v_x_2647_, size_t v_x_2648_, size_t v_x_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2646_, v_x_2647_, v_x_2648_, v_x_2649_, v_x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2652_, lean_object* v_00_u03c3_2653_, lean_object* v_00_u03b1_2654_, lean_object* v_ext_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
size_t v_x_3047__boxed_2660_; size_t v_x_3048__boxed_2661_; lean_object* v_res_2662_; 
v_x_3047__boxed_2660_ = lean_unbox_usize(v_x_2657_);
lean_dec(v_x_2657_);
v_x_3048__boxed_2661_ = lean_unbox_usize(v_x_2658_);
lean_dec(v_x_2658_);
v_res_2662_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(v_00_u03b2_2652_, v_00_u03c3_2653_, v_00_u03b1_2654_, v_ext_2655_, v_x_2656_, v_x_3047__boxed_2660_, v_x_3048__boxed_2661_, v_x_2659_);
lean_dec_ref(v_x_2656_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_object* v_00_u03b2_2663_, lean_object* v_00_u03c3_2664_, lean_object* v_00_u03b1_2665_, lean_object* v_ext_2666_, lean_object* v_as_2667_, size_t v_i_2668_, size_t v_stop_2669_, lean_object* v_b_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2666_, v_as_2667_, v_i_2668_, v_stop_2669_, v_b_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2672_, lean_object* v_00_u03c3_2673_, lean_object* v_00_u03b1_2674_, lean_object* v_ext_2675_, lean_object* v_as_2676_, lean_object* v_i_2677_, lean_object* v_stop_2678_, lean_object* v_b_2679_){
_start:
{
size_t v_i_boxed_2680_; size_t v_stop_boxed_2681_; lean_object* v_res_2682_; 
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_stop_boxed_2681_ = lean_unbox_usize(v_stop_2678_);
lean_dec(v_stop_2678_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(v_00_u03b2_2672_, v_00_u03c3_2673_, v_00_u03b1_2674_, v_ext_2675_, v_as_2676_, v_i_boxed_2680_, v_stop_boxed_2681_, v_b_2679_);
lean_dec_ref(v_as_2676_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(lean_object* v_00_u03b2_2683_, lean_object* v_00_u03c3_2684_, lean_object* v_00_u03b1_2685_, lean_object* v_ext_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2686_, v_x_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_00_u03c3_2691_, lean_object* v_00_u03b1_2692_, lean_object* v_ext_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(v_00_u03b2_2690_, v_00_u03c3_2691_, v_00_u03b1_2692_, v_ext_2693_, v_x_2694_, v_x_2695_);
lean_dec_ref(v_x_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2697_, lean_object* v_val_2698_, lean_object* v_as_2699_, size_t v_i_2700_, size_t v_stop_2701_, lean_object* v_b_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2698_, v_as_2699_, v_i_2700_, v_stop_2701_, v_b_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2704_, lean_object* v_val_2705_, lean_object* v_as_2706_, lean_object* v_i_2707_, lean_object* v_stop_2708_, lean_object* v_b_2709_){
_start:
{
size_t v_i_boxed_2710_; size_t v_stop_boxed_2711_; lean_object* v_res_2712_; 
v_i_boxed_2710_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_stop_boxed_2711_ = lean_unbox_usize(v_stop_2708_);
lean_dec(v_stop_2708_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2704_, v_val_2705_, v_as_2706_, v_i_boxed_2710_, v_stop_boxed_2711_, v_b_2709_);
lean_dec_ref(v_as_2706_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_2713_, lean_object* v_00_u03c3_2714_, lean_object* v_00_u03b1_2715_, lean_object* v_ext_2716_, lean_object* v_as_2717_, size_t v_i_2718_, size_t v_stop_2719_, lean_object* v_b_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2716_, v_as_2717_, v_i_2718_, v_stop_2719_, v_b_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2722_, lean_object* v_00_u03c3_2723_, lean_object* v_00_u03b1_2724_, lean_object* v_ext_2725_, lean_object* v_as_2726_, lean_object* v_i_2727_, lean_object* v_stop_2728_, lean_object* v_b_2729_){
_start:
{
size_t v_i_boxed_2730_; size_t v_stop_boxed_2731_; lean_object* v_res_2732_; 
v_i_boxed_2730_ = lean_unbox_usize(v_i_2727_);
lean_dec(v_i_2727_);
v_stop_boxed_2731_ = lean_unbox_usize(v_stop_2728_);
lean_dec(v_stop_2728_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(v_00_u03b2_2722_, v_00_u03c3_2723_, v_00_u03b1_2724_, v_ext_2725_, v_as_2726_, v_i_boxed_2730_, v_stop_boxed_2731_, v_b_2729_);
lean_dec_ref(v_as_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2733_, lean_object* v_descr_2734_, lean_object* v_ps_2735_){
_start:
{
lean_object* v_state_2736_; lean_object* v_stateStack_2737_; 
v_state_2736_ = lean_ctor_get(v_ps_2735_, 1);
lean_inc(v_state_2736_);
v_stateStack_2737_ = lean_ctor_get(v_state_2736_, 0);
lean_inc(v_stateStack_2737_);
if (lean_obj_tag(v_stateStack_2737_) == 1)
{
lean_object* v_head_2738_; lean_object* v_importedEntries_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2781_; 
v_head_2738_ = lean_ctor_get(v_stateStack_2737_, 0);
lean_inc(v_head_2738_);
v_importedEntries_2739_ = lean_ctor_get(v_ps_2735_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_ps_2735_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v_ps_2735_, 1);
lean_dec(v_unused_2782_);
v___x_2741_ = v_ps_2735_;
v_isShared_2742_ = v_isSharedCheck_2781_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_importedEntries_2739_);
lean_dec(v_ps_2735_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2781_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_scopedEntries_2743_; lean_object* v_newEntries_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2779_; 
v_scopedEntries_2743_ = lean_ctor_get(v_state_2736_, 1);
v_newEntries_2744_ = lean_ctor_get(v_state_2736_, 2);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_state_2736_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_state_2736_, 0);
lean_dec(v_unused_2780_);
v___x_2746_ = v_state_2736_;
v_isShared_2747_ = v_isSharedCheck_2779_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_newEntries_2744_);
lean_inc(v_scopedEntries_2743_);
lean_dec(v_state_2736_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2779_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_tail_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2777_; 
v_tail_2748_ = lean_ctor_get(v_stateStack_2737_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_stateStack_2737_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v_stateStack_2737_, 0);
lean_dec(v_unused_2778_);
v___x_2750_ = v_stateStack_2737_;
v_isShared_2751_ = v_isSharedCheck_2777_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_tail_2748_);
lean_dec(v_stateStack_2737_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2777_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_state_2752_; lean_object* v_activeScopes_2753_; uint8_t v_delimitsLocal_2754_; uint8_t v_scopeChanged_2755_; lean_object* v_scopeChangedDecls_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2776_; 
v_state_2752_ = lean_ctor_get(v_head_2738_, 0);
v_activeScopes_2753_ = lean_ctor_get(v_head_2738_, 1);
v_delimitsLocal_2754_ = lean_ctor_get_uint8(v_head_2738_, sizeof(void*)*3);
v_scopeChanged_2755_ = lean_ctor_get_uint8(v_head_2738_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2756_ = lean_ctor_get(v_head_2738_, 2);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_head_2738_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2758_ = v_head_2738_;
v_isShared_2759_ = v_isSharedCheck_2776_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_scopeChangedDecls_2756_);
lean_inc(v_activeScopes_2753_);
lean_inc(v_state_2752_);
lean_dec(v_head_2738_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2776_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
uint8_t v___y_2761_; 
if (v_scopeChanged_2755_ == 0)
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_2734_);
v___y_2761_ = v___x_2775_;
goto v___jp_2760_;
}
else
{
v___y_2761_ = v_scopeChanged_2755_;
goto v___jp_2760_;
}
v___jp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = lean_apply_1(v_f_2733_, v_state_2752_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2762_);
v___x_2764_ = v___x_2758_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_activeScopes_2753_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_scopeChangedDecls_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, sizeof(void*)*3, v_delimitsLocal_2754_);
v___x_2764_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2766_; 
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*3 + 1, v___y_2761_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2764_);
v___x_2766_ = v___x_2750_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_tail_2748_);
v___x_2766_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2768_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2766_);
v___x_2768_ = v___x_2746_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_scopedEntries_2743_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_newEntries_2744_);
v___x_2768_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2768_);
v___x_2770_ = v___x_2741_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_importedEntries_2739_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
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
lean_object* v_importedEntries_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_stateStack_2737_);
lean_dec(v_f_2733_);
v_importedEntries_2783_ = lean_ctor_get(v_ps_2735_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_ps_2735_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v_ps_2735_, 1);
lean_dec(v_unused_2791_);
v___x_2785_ = v_ps_2735_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_importedEntries_2783_);
lean_dec(v_ps_2735_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_importedEntries_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_state_2736_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object* v_f_2792_, lean_object* v_descr_2793_, lean_object* v_ps_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(v_f_2792_, v_descr_2793_, v_ps_2794_);
lean_dec_ref(v_descr_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2796_, lean_object* v_env_2797_, lean_object* v_f_2798_){
_start:
{
lean_object* v_ext_2799_; lean_object* v_toEnvExtension_2800_; lean_object* v_descr_2801_; lean_object* v_asyncMode_2802_; uint8_t v_logWrites_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_ext_2799_ = lean_ctor_get(v_ext_2796_, 1);
v_toEnvExtension_2800_ = lean_ctor_get(v_ext_2799_, 0);
lean_inc_ref(v_toEnvExtension_2800_);
v_descr_2801_ = lean_ctor_get(v_ext_2796_, 0);
lean_inc_ref(v_descr_2801_);
lean_dec_ref(v_ext_2796_);
v_asyncMode_2802_ = lean_ctor_get(v_toEnvExtension_2800_, 2);
lean_inc(v_asyncMode_2802_);
v_logWrites_2803_ = lean_ctor_get_uint8(v_toEnvExtension_2800_, sizeof(void*)*6);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2804_, 0, v_f_2798_);
lean_closure_set(v___f_2804_, 1, v_descr_2801_);
v___x_2805_ = lean_box(0);
v___x_2806_ = 1;
if (v_logWrites_2803_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2800_, v_env_2797_, v___f_2804_, v_asyncMode_2802_, v___x_2805_, v___x_2806_);
lean_dec(v_asyncMode_2802_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_inc_ref(v_toEnvExtension_2800_);
v___x_2808_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2800_, v_env_2797_);
lean_dec_ref(v_env_2797_);
v___x_2809_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2800_, v___x_2808_, v___f_2804_, v_asyncMode_2802_, v___x_2805_, v___x_2806_);
lean_dec(v_asyncMode_2802_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_00_u03c3_2812_, lean_object* v_ext_2813_, lean_object* v_env_2814_, lean_object* v_f_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2813_, v_env_2814_, v_f_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2817_, lean_object* v_____s_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_apply_2(v_toPure_2817_, lean_box(0), v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2821_, lean_object* v_toPure_2822_, lean_object* v_r_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
v___x_2825_ = lean_apply_2(v_toPure_2822_, lean_box(0), v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2826_, lean_object* v_toBind_2827_, lean_object* v___f_2828_, lean_object* v_a_2829_, lean_object* v_x_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_modifyEnv_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_modifyEnv_2832_ = lean_ctor_get(v_inst_2826_, 1);
lean_inc(v_modifyEnv_2832_);
lean_dec_ref(v_inst_2826_);
v___x_2833_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2833_, 0, lean_box(0));
lean_closure_set(v___x_2833_, 1, lean_box(0));
lean_closure_set(v___x_2833_, 2, lean_box(0));
lean_closure_set(v___x_2833_, 3, v_a_2829_);
v___x_2834_ = lean_apply_1(v_modifyEnv_2832_, v___x_2833_);
v___x_2835_ = lean_apply_4(v_toBind_2827_, lean_box(0), lean_box(0), v___x_2834_, v___f_2828_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2836_, lean_object* v_inst_2837_, lean_object* v_toBind_2838_, lean_object* v_inst_2839_, lean_object* v___f_2840_, lean_object* v_____do__lift_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___f_2844_; size_t v_sz_2845_; size_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2842_ = lean_box(0);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
lean_closure_set(v___f_2843_, 1, v_toPure_2836_);
lean_inc(v_toBind_2838_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2844_, 0, v_inst_2837_);
lean_closure_set(v___f_2844_, 1, v_toBind_2838_);
lean_closure_set(v___f_2844_, 2, v___f_2843_);
v_sz_2845_ = lean_array_size(v_____do__lift_2841_);
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2839_, v_____do__lift_2841_, v___f_2844_, v_sz_2845_, v___x_2846_, v___x_2842_);
v___x_2848_ = lean_apply_4(v_toBind_2838_, lean_box(0), lean_box(0), v___x_2847_, v___f_2840_);
return v___x_2848_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = l_Lean_scopedEnvExtensionsRef;
v___x_2850_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2850_, 0, lean_box(0));
lean_closure_set(v___x_2850_, 1, lean_box(0));
lean_closure_set(v___x_2850_, 2, v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_){
_start:
{
lean_object* v_toApplicative_2854_; lean_object* v_toBind_2855_; lean_object* v_toPure_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___f_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v_toApplicative_2854_ = lean_ctor_get(v_inst_2851_, 0);
v_toBind_2855_ = lean_ctor_get(v_inst_2851_, 1);
lean_inc_n(v_toBind_2855_, 2);
v_toPure_2856_ = lean_ctor_get(v_toApplicative_2854_, 1);
lean_inc_n(v_toPure_2856_, 2);
v___x_2857_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2858_ = lean_apply_2(v_inst_2853_, lean_box(0), v___x_2857_);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2859_, 0, v_toPure_2856_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2860_, 0, v_toPure_2856_);
lean_closure_set(v___f_2860_, 1, v_inst_2852_);
lean_closure_set(v___f_2860_, 2, v_toBind_2855_);
lean_closure_set(v___f_2860_, 3, v_inst_2851_);
lean_closure_set(v___f_2860_, 4, v___f_2859_);
v___x_2861_ = lean_apply_4(v_toBind_2855_, lean_box(0), lean_box(0), v___x_2858_, v___f_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_pushScope___redArg(v_inst_2863_, v_inst_2864_, v_inst_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2867_, lean_object* v_toBind_2868_, lean_object* v___f_2869_, lean_object* v_a_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_modifyEnv_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_modifyEnv_2873_ = lean_ctor_get(v_inst_2867_, 1);
lean_inc(v_modifyEnv_2873_);
lean_dec_ref(v_inst_2867_);
v___x_2874_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2874_, 0, lean_box(0));
lean_closure_set(v___x_2874_, 1, lean_box(0));
lean_closure_set(v___x_2874_, 2, lean_box(0));
lean_closure_set(v___x_2874_, 3, v_a_2870_);
v___x_2875_ = lean_apply_1(v_modifyEnv_2873_, v___x_2874_);
v___x_2876_ = lean_apply_4(v_toBind_2868_, lean_box(0), lean_box(0), v___x_2875_, v___f_2869_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2877_, lean_object* v_inst_2878_, lean_object* v_toBind_2879_, lean_object* v_inst_2880_, lean_object* v___f_2881_, lean_object* v_____do__lift_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___f_2884_; lean_object* v___f_2885_; size_t v_sz_2886_; size_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2883_ = lean_box(0);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2884_, 0, v___x_2883_);
lean_closure_set(v___f_2884_, 1, v_toPure_2877_);
lean_inc(v_toBind_2879_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2885_, 0, v_inst_2878_);
lean_closure_set(v___f_2885_, 1, v_toBind_2879_);
lean_closure_set(v___f_2885_, 2, v___f_2884_);
v_sz_2886_ = lean_array_size(v_____do__lift_2882_);
v___x_2887_ = ((size_t)0ULL);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2880_, v_____do__lift_2882_, v___f_2885_, v_sz_2886_, v___x_2887_, v___x_2883_);
v___x_2889_ = lean_apply_4(v_toBind_2879_, lean_box(0), lean_box(0), v___x_2888_, v___f_2881_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_){
_start:
{
lean_object* v_toApplicative_2893_; lean_object* v_toBind_2894_; lean_object* v_toPure_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___f_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; 
v_toApplicative_2893_ = lean_ctor_get(v_inst_2890_, 0);
v_toBind_2894_ = lean_ctor_get(v_inst_2890_, 1);
lean_inc_n(v_toBind_2894_, 2);
v_toPure_2895_ = lean_ctor_get(v_toApplicative_2893_, 1);
lean_inc_n(v_toPure_2895_, 2);
v___x_2896_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2897_ = lean_apply_2(v_inst_2892_, lean_box(0), v___x_2896_);
v___f_2898_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2898_, 0, v_toPure_2895_);
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2899_, 0, v_toPure_2895_);
lean_closure_set(v___f_2899_, 1, v_inst_2891_);
lean_closure_set(v___f_2899_, 2, v_toBind_2894_);
lean_closure_set(v___f_2899_, 3, v_inst_2890_);
lean_closure_set(v___f_2899_, 4, v___f_2898_);
v___x_2900_ = lean_apply_4(v_toBind_2894_, lean_box(0), lean_box(0), v___x_2897_, v___f_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_popScope___redArg(v_inst_2902_, v_inst_2903_, v_inst_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2906_, lean_object* v_depth_2907_, lean_object* v_x_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2906_, v_x_2908_, v_depth_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2910_, lean_object* v_depth_2911_, lean_object* v_toBind_2912_, lean_object* v___f_2913_, lean_object* v_a_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_modifyEnv_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_modifyEnv_2917_ = lean_ctor_get(v_inst_2910_, 1);
lean_inc(v_modifyEnv_2917_);
lean_dec_ref(v_inst_2910_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2918_, 0, v_a_2914_);
lean_closure_set(v___f_2918_, 1, v_depth_2911_);
v___x_2919_ = lean_apply_1(v_modifyEnv_2917_, v___f_2918_);
v___x_2920_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v___x_2919_, v___f_2913_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2921_, lean_object* v_inst_2922_, lean_object* v_depth_2923_, lean_object* v_toBind_2924_, lean_object* v_inst_2925_, lean_object* v___f_2926_, lean_object* v_____do__lift_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___f_2930_; size_t v_sz_2931_; size_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2928_ = lean_box(0);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2929_, 0, v___x_2928_);
lean_closure_set(v___f_2929_, 1, v_toPure_2921_);
lean_inc(v_toBind_2924_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2930_, 0, v_inst_2922_);
lean_closure_set(v___f_2930_, 1, v_depth_2923_);
lean_closure_set(v___f_2930_, 2, v_toBind_2924_);
lean_closure_set(v___f_2930_, 3, v___f_2929_);
v_sz_2931_ = lean_array_size(v_____do__lift_2927_);
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2925_, v_____do__lift_2927_, v___f_2930_, v_sz_2931_, v___x_2932_, v___x_2928_);
v___x_2934_ = lean_apply_4(v_toBind_2924_, lean_box(0), lean_box(0), v___x_2933_, v___f_2926_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_depth_2938_){
_start:
{
lean_object* v_toApplicative_2939_; lean_object* v_toBind_2940_; lean_object* v_toPure_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; 
v_toApplicative_2939_ = lean_ctor_get(v_inst_2935_, 0);
v_toBind_2940_ = lean_ctor_get(v_inst_2935_, 1);
lean_inc_n(v_toBind_2940_, 2);
v_toPure_2941_ = lean_ctor_get(v_toApplicative_2939_, 1);
lean_inc_n(v_toPure_2941_, 2);
v___x_2942_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2943_ = lean_apply_2(v_inst_2937_, lean_box(0), v___x_2942_);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2944_, 0, v_toPure_2941_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2945_, 0, v_toPure_2941_);
lean_closure_set(v___f_2945_, 1, v_inst_2936_);
lean_closure_set(v___f_2945_, 2, v_depth_2938_);
lean_closure_set(v___f_2945_, 3, v_toBind_2940_);
lean_closure_set(v___f_2945_, 4, v_inst_2935_);
lean_closure_set(v___f_2945_, 5, v___f_2944_);
v___x_2946_ = lean_apply_4(v_toBind_2940_, lean_box(0), lean_box(0), v___x_2943_, v___f_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_depth_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_setDelimitsLocal___redArg(v_inst_2948_, v_inst_2949_, v_inst_2950_, v_depth_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2953_, lean_object* v_namespaceName_2954_, lean_object* v_x_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2953_, v_x_2955_, v_namespaceName_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2957_, lean_object* v_namespaceName_2958_, lean_object* v_toBind_2959_, lean_object* v___f_2960_, lean_object* v_a_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_modifyEnv_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_modifyEnv_2964_ = lean_ctor_get(v_inst_2957_, 1);
lean_inc(v_modifyEnv_2964_);
lean_dec_ref(v_inst_2957_);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2965_, 0, v_a_2961_);
lean_closure_set(v___f_2965_, 1, v_namespaceName_2958_);
v___x_2966_ = lean_apply_1(v_modifyEnv_2964_, v___f_2965_);
v___x_2967_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v___x_2966_, v___f_2960_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2968_, lean_object* v_inst_2969_, lean_object* v_namespaceName_2970_, lean_object* v_toBind_2971_, lean_object* v_inst_2972_, lean_object* v___f_2973_, lean_object* v_____do__lift_2974_){
_start:
{
lean_object* v___x_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; size_t v_sz_2978_; size_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2975_ = lean_box(0);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2976_, 0, v___x_2975_);
lean_closure_set(v___f_2976_, 1, v_toPure_2968_);
lean_inc(v_toBind_2971_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2977_, 0, v_inst_2969_);
lean_closure_set(v___f_2977_, 1, v_namespaceName_2970_);
lean_closure_set(v___f_2977_, 2, v_toBind_2971_);
lean_closure_set(v___f_2977_, 3, v___f_2976_);
v_sz_2978_ = lean_array_size(v_____do__lift_2974_);
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2972_, v_____do__lift_2974_, v___f_2977_, v_sz_2978_, v___x_2979_, v___x_2975_);
v___x_2981_ = lean_apply_4(v_toBind_2971_, lean_box(0), lean_box(0), v___x_2980_, v___f_2973_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_namespaceName_2985_){
_start:
{
lean_object* v_toApplicative_2986_; lean_object* v_toBind_2987_; lean_object* v_toPure_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___f_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; 
v_toApplicative_2986_ = lean_ctor_get(v_inst_2982_, 0);
v_toBind_2987_ = lean_ctor_get(v_inst_2982_, 1);
lean_inc_n(v_toBind_2987_, 2);
v_toPure_2988_ = lean_ctor_get(v_toApplicative_2986_, 1);
lean_inc_n(v_toPure_2988_, 2);
v___x_2989_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2990_ = lean_apply_2(v_inst_2984_, lean_box(0), v___x_2989_);
v___f_2991_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2991_, 0, v_toPure_2988_);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2992_, 0, v_toPure_2988_);
lean_closure_set(v___f_2992_, 1, v_inst_2983_);
lean_closure_set(v___f_2992_, 2, v_namespaceName_2985_);
lean_closure_set(v___f_2992_, 3, v_toBind_2987_);
lean_closure_set(v___f_2992_, 4, v_inst_2982_);
lean_closure_set(v___f_2992_, 5, v___f_2991_);
v___x_2993_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2990_, v___f_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2994_, lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_namespaceName_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_activateScoped___redArg(v_inst_2995_, v_inst_2996_, v_inst_2997_, v_namespaceName_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_3001_){
_start:
{
lean_inc(v___y_3001_);
return v___y_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_3002_);
lean_dec(v___y_3002_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_3004_, lean_object* v_a_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_a_3005_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_3009_, lean_object* v_a_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_3009_, v_a_3010_, v___y_3011_);
lean_dec_ref(v___y_3011_);
lean_dec(v_x_3009_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_3014_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_initial_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_3022_){
_start:
{
lean_object* v_name_3024_; lean_object* v_addEntry_3025_; lean_object* v_initial_3026_; lean_object* v_finalizeImport_3027_; lean_object* v_exportEntry_x3f_3028_; uint8_t v_trackGen_3029_; uint8_t v_logWrites_3030_; lean_object* v_entryDecl_x3f_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_name_3024_ = lean_ctor_get(v_descr_3022_, 0);
lean_inc(v_name_3024_);
v_addEntry_3025_ = lean_ctor_get(v_descr_3022_, 1);
lean_inc(v_addEntry_3025_);
v_initial_3026_ = lean_ctor_get(v_descr_3022_, 2);
lean_inc(v_initial_3026_);
v_finalizeImport_3027_ = lean_ctor_get(v_descr_3022_, 3);
lean_inc(v_finalizeImport_3027_);
v_exportEntry_x3f_3028_ = lean_ctor_get(v_descr_3022_, 4);
lean_inc_ref(v_exportEntry_x3f_3028_);
v_trackGen_3029_ = lean_ctor_get_uint8(v_descr_3022_, sizeof(void*)*6);
v_logWrites_3030_ = lean_ctor_get_uint8(v_descr_3022_, sizeof(void*)*6 + 1);
v_entryDecl_x3f_3031_ = lean_ctor_get(v_descr_3022_, 5);
lean_inc(v_entryDecl_x3f_3031_);
lean_dec_ref(v_descr_3022_);
v___f_3032_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_3033_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3034_, 0, v_initial_3026_);
v___x_3035_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3035_, 0, v_name_3024_);
lean_ctor_set(v___x_3035_, 1, v___f_3034_);
lean_ctor_set(v___x_3035_, 2, v___f_3033_);
lean_ctor_set(v___x_3035_, 3, v___f_3032_);
lean_ctor_set(v___x_3035_, 4, v_addEntry_3025_);
lean_ctor_set(v___x_3035_, 5, v_finalizeImport_3027_);
lean_ctor_set(v___x_3035_, 6, v_exportEntry_x3f_3028_);
lean_ctor_set(v___x_3035_, 7, v_entryDecl_x3f_3031_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*8, v_trackGen_3029_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*8 + 1, v_logWrites_3030_);
v___x_3036_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3037_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_3040_, lean_object* v_00_u03c3_3041_, lean_object* v_descr_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_3045_, lean_object* v_00_u03c3_3046_, lean_object* v_descr_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_3045_, v_00_u03c3_3046_, v_descr_3047_);
return v_res_3049_;
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
