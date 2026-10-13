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
uint8_t v___x_1681_; 
v___x_1681_ = lean_nat_dec_le(v___x_1679_, v___x_1679_);
if (v___x_1681_ == 0)
{
if (v___x_1680_ == 0)
{
v___y_1668_ = v___x_1676_;
v___y_1669_ = v_env_1662_;
goto v___jp_1667_;
}
else
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = lean_usize_of_nat(v___x_1679_);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1665_, v___x_1682_, v___x_1683_, v_env_1662_);
v___y_1668_ = v___x_1676_;
v___y_1669_ = v___x_1684_;
goto v___jp_1667_;
}
}
else
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1679_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1665_, v___x_1685_, v___x_1686_, v_env_1662_);
v___y_1668_ = v___x_1676_;
v___y_1669_ = v___x_1687_;
goto v___jp_1667_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___boxed(lean_object* v_ext_1688_, lean_object* v_env_1689_, lean_object* v_changed_1690_, lean_object* v_f_1691_, lean_object* v_changedDecls_1692_){
_start:
{
uint8_t v_changed_boxed_1693_; lean_object* v_res_1694_; 
v_changed_boxed_1693_ = lean_unbox(v_changed_1690_);
v_res_1694_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1688_, v_env_1689_, v_changed_boxed_1693_, v_f_1691_, v_changedDecls_1692_);
lean_dec_ref(v_changedDecls_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_object* v_00_u03b1_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_00_u03c3_1697_, lean_object* v_ext_1698_, lean_object* v_env_1699_, uint8_t v_changed_1700_, lean_object* v_f_1701_, lean_object* v_changedDecls_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1698_, v_env_1699_, v_changed_1700_, v_f_1701_, v_changedDecls_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_00_u03c3_1706_, lean_object* v_ext_1707_, lean_object* v_env_1708_, lean_object* v_changed_1709_, lean_object* v_f_1710_, lean_object* v_changedDecls_1711_){
_start:
{
uint8_t v_changed_boxed_1712_; lean_object* v_res_1713_; 
v_changed_boxed_1712_ = lean_unbox(v_changed_1709_);
v_res_1713_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(v_00_u03b1_1704_, v_00_u03b2_1705_, v_00_u03c3_1706_, v_ext_1707_, v_env_1708_, v_changed_boxed_1712_, v_f_1710_, v_changedDecls_1711_);
lean_dec_ref(v_changedDecls_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(uint8_t v___x_1714_, lean_object* v_s_1715_){
_start:
{
lean_object* v_stateStack_1716_; 
v_stateStack_1716_ = lean_ctor_get(v_s_1715_, 0);
if (lean_obj_tag(v_stateStack_1716_) == 0)
{
return v_s_1715_;
}
else
{
lean_object* v_head_1717_; lean_object* v_scopedEntries_1718_; lean_object* v_newEntries_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1739_; 
lean_inc_ref(v_stateStack_1716_);
v_head_1717_ = lean_ctor_get(v_stateStack_1716_, 0);
lean_inc(v_head_1717_);
v_scopedEntries_1718_ = lean_ctor_get(v_s_1715_, 1);
v_newEntries_1719_ = lean_ctor_get(v_s_1715_, 2);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_s_1715_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_s_1715_, 0);
lean_dec(v_unused_1740_);
v___x_1721_ = v_s_1715_;
v_isShared_1722_ = v_isSharedCheck_1739_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_newEntries_1719_);
lean_inc(v_scopedEntries_1718_);
lean_dec(v_s_1715_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1739_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_state_1723_; lean_object* v_activeScopes_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1737_; 
v_state_1723_ = lean_ctor_get(v_head_1717_, 0);
v_activeScopes_1724_ = lean_ctor_get(v_head_1717_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_head_1717_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v_head_1717_, 2);
lean_dec(v_unused_1738_);
v___x_1726_ = v_head_1717_;
v_isShared_1727_ = v_isSharedCheck_1737_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_activeScopes_1724_);
lean_inc(v_state_1723_);
lean_dec(v_head_1717_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1737_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = 1;
v___x_1729_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 2, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_state_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_activeScopes_1724_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*3, v___x_1728_);
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*3 + 1, v___x_1714_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_stateStack_1716_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1732_);
v___x_1734_ = v___x_1721_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_scopedEntries_1718_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_newEntries_1719_);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed(lean_object* v___x_1741_, lean_object* v_s_1742_){
_start:
{
uint8_t v___x_59__boxed_1743_; lean_object* v_res_1744_; 
v___x_59__boxed_1743_ = lean_unbox(v___x_1741_);
v_res_1744_ = l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(v___x_59__boxed_1743_, v_s_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1748_, lean_object* v_env_1749_){
_start:
{
uint8_t v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = 0;
v___f_1751_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1752_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1753_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1748_, v_env_1749_, v___x_1750_, v___f_1751_, v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_00_u03c3_1756_, lean_object* v_ext_1757_, lean_object* v_env_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1757_, v_env_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_tail_1760_, lean_object* v_s_1761_){
_start:
{
lean_object* v_scopedEntries_1762_; lean_object* v_newEntries_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_scopedEntries_1762_ = lean_ctor_get(v_s_1761_, 1);
v_newEntries_1763_ = lean_ctor_get(v_s_1761_, 2);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_s_1761_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v_s_1761_, 0);
lean_dec(v_unused_1771_);
v___x_1765_ = v_s_1761_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_newEntries_1763_);
lean_inc(v_scopedEntries_1762_);
lean_dec(v_s_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_tail_1760_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_tail_1760_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_scopedEntries_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_newEntries_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1772_, lean_object* v_env_1773_){
_start:
{
lean_object* v_ext_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v_stateStack_1780_; 
v_ext_1774_ = lean_ctor_get(v_ext_1772_, 1);
v___x_1775_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1776_ = lean_box(1);
v___x_1777_ = lean_box(0);
v___x_1778_ = 0;
lean_inc_ref(v_env_1773_);
v___x_1779_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1775_, v_ext_1774_, v_env_1773_, v___x_1776_, v___x_1777_, v___x_1778_);
v_stateStack_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_stateStack_1780_);
lean_dec(v___x_1779_);
if (lean_obj_tag(v_stateStack_1780_) == 1)
{
lean_object* v_tail_1781_; 
v_tail_1781_ = lean_ctor_get(v_stateStack_1780_, 1);
lean_inc(v_tail_1781_);
if (lean_obj_tag(v_tail_1781_) == 1)
{
lean_object* v_head_1782_; uint8_t v_scopeChanged_1783_; lean_object* v_scopeChangedDecls_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; 
v_head_1782_ = lean_ctor_get(v_stateStack_1780_, 0);
lean_inc(v_head_1782_);
lean_dec_ref_known(v_stateStack_1780_, 2);
v_scopeChanged_1783_ = lean_ctor_get_uint8(v_head_1782_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1784_ = lean_ctor_get(v_head_1782_, 2);
lean_inc_ref(v_scopeChangedDecls_1784_);
lean_dec(v_head_1782_);
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1785_, 0, v_tail_1781_);
v___x_1786_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1772_, v_env_1773_, v_scopeChanged_1783_, v___f_1785_, v_scopeChangedDecls_1784_);
lean_dec_ref(v_scopeChangedDecls_1784_);
return v___x_1786_;
}
else
{
lean_dec_ref_known(v_stateStack_1780_, 2);
lean_dec(v_tail_1781_);
lean_dec_ref(v_ext_1772_);
return v_env_1773_;
}
}
else
{
lean_dec(v_stateStack_1780_);
lean_dec_ref(v_ext_1772_);
return v_env_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_00_u03c3_1789_, lean_object* v_ext_1790_, lean_object* v_env_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1790_, v_env_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_zero_1795_; uint8_t v_isZero_1796_; 
v_zero_1795_ = lean_unsigned_to_nat(0u);
v_isZero_1796_ = lean_nat_dec_eq(v_a_1793_, v_zero_1795_);
if (v_isZero_1796_ == 1)
{
return v_a_1794_;
}
else
{
if (lean_obj_tag(v_a_1794_) == 0)
{
return v_a_1794_;
}
else
{
lean_object* v_head_1797_; lean_object* v_tail_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1819_; 
v_head_1797_ = lean_ctor_get(v_a_1794_, 0);
v_tail_1798_ = lean_ctor_get(v_a_1794_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_a_1794_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1800_ = v_a_1794_;
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_tail_1798_);
lean_inc(v_head_1797_);
lean_dec(v_a_1794_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1819_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_state_1802_; lean_object* v_activeScopes_1803_; uint8_t v_scopeChanged_1804_; lean_object* v_scopeChangedDecls_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_state_1802_ = lean_ctor_get(v_head_1797_, 0);
v_activeScopes_1803_ = lean_ctor_get(v_head_1797_, 1);
v_scopeChanged_1804_ = lean_ctor_get_uint8(v_head_1797_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1805_ = lean_ctor_get(v_head_1797_, 2);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_head_1797_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1807_ = v_head_1797_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_scopeChangedDecls_1805_);
lean_inc(v_activeScopes_1803_);
lean_inc(v_state_1802_);
lean_dec(v_head_1797_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_one_1809_; lean_object* v_n_1810_; lean_object* v___x_1812_; 
v_one_1809_ = lean_unsigned_to_nat(1u);
v_n_1810_ = lean_nat_sub(v_a_1793_, v_one_1809_);
if (v_isShared_1808_ == 0)
{
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_state_1802_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_activeScopes_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_scopeChangedDecls_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3 + 1, v_scopeChanged_1804_);
v___x_1812_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*3, v_isZero_1796_);
v___x_1813_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1810_, v_tail_1798_);
lean_dec(v_n_1810_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v___x_1813_);
lean_ctor_set(v___x_1800_, 0, v___x_1812_);
v___x_1815_ = v___x_1800_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1820_, v_a_1821_);
lean_dec(v_a_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1824_, v_a_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1831_, lean_object* v_s_1832_){
_start:
{
lean_object* v_stateStack_1833_; lean_object* v_scopedEntries_1834_; lean_object* v_newEntries_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_stateStack_1833_ = lean_ctor_get(v_s_1832_, 0);
v_scopedEntries_1834_ = lean_ctor_get(v_s_1832_, 1);
v_newEntries_1835_ = lean_ctor_get(v_s_1832_, 2);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_s_1832_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v_s_1832_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_newEntries_1835_);
lean_inc(v_scopedEntries_1834_);
lean_inc(v_stateStack_1833_);
lean_dec(v_s_1832_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1831_, v_stateStack_1833_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_scopedEntries_1834_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_newEntries_1835_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1844_, lean_object* v_s_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1844_, v_s_1845_);
lean_dec(v_depth_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1847_, lean_object* v_env_1848_, lean_object* v_depth_1849_){
_start:
{
lean_object* v___f_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1850_, 0, v_depth_1849_);
v___x_1851_ = 0;
v___x_1852_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1853_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1847_, v_env_1848_, v___x_1851_, v___f_1850_, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_00_u03c3_1856_, lean_object* v_ext_1857_, lean_object* v_env_1858_, lean_object* v_depth_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1857_, v_env_1858_, v_depth_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg(lean_object* v_ext_1863_, lean_object* v_b_1864_){
_start:
{
lean_object* v_descr_1865_; lean_object* v_entryDecl_x3f_1866_; 
v_descr_1865_ = lean_ctor_get(v_ext_1863_, 0);
lean_inc_ref(v_descr_1865_);
lean_dec_ref(v_ext_1863_);
v_entryDecl_x3f_1866_ = lean_ctor_get(v_descr_1865_, 7);
lean_inc(v_entryDecl_x3f_1866_);
lean_dec_ref(v_descr_1865_);
if (lean_obj_tag(v_entryDecl_x3f_1866_) == 1)
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1875_; 
v_val_1867_ = lean_ctor_get(v_entryDecl_x3f_1866_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_entryDecl_x3f_1866_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1869_ = v_entryDecl_x3f_1866_;
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v_entryDecl_x3f_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = lean_apply_1(v_val_1867_, v_b_1864_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v_entryDecl_x3f_1866_);
lean_dec(v_b_1864_);
v___x_1876_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog(lean_object* v_00_u03b1_1877_, lean_object* v_00_u03b2_1878_, lean_object* v_00_u03c3_1879_, lean_object* v_ext_1880_, lean_object* v_b_1881_){
_start:
{
lean_object* v_descr_1882_; lean_object* v_entryDecl_x3f_1883_; 
v_descr_1882_ = lean_ctor_get(v_ext_1880_, 0);
lean_inc_ref(v_descr_1882_);
lean_dec_ref(v_ext_1880_);
v_entryDecl_x3f_1883_ = lean_ctor_get(v_descr_1882_, 7);
lean_inc(v_entryDecl_x3f_1883_);
lean_dec_ref(v_descr_1882_);
if (lean_obj_tag(v_entryDecl_x3f_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1892_; 
v_val_1884_ = lean_ctor_get(v_entryDecl_x3f_1883_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_entryDecl_x3f_1883_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1886_ = v_entryDecl_x3f_1883_;
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_entryDecl_x3f_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_apply_1(v_val_1884_, v_b_1881_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1893_; 
lean_dec(v_entryDecl_x3f_1883_);
lean_dec(v_b_1881_);
v___x_1893_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0(lean_object* v_addEntryFn_1894_, lean_object* v___x_1895_, lean_object* v_s_1896_){
_start:
{
lean_object* v_importedEntries_1897_; lean_object* v_state_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
v_importedEntries_1897_ = lean_ctor_get(v_s_1896_, 0);
v_state_1898_ = lean_ctor_get(v_s_1896_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_s_1896_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v_s_1896_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_state_1898_);
lean_inc(v_importedEntries_1897_);
lean_dec(v_s_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_state_1902_; lean_object* v___x_1904_; 
v_state_1902_ = lean_apply_2(v_addEntryFn_1894_, v_state_1898_, v___x_1895_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v_state_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_importedEntries_1897_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_state_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_1907_, lean_object* v_env_1908_, lean_object* v_b_1909_){
_start:
{
lean_object* v_ext_1910_; lean_object* v_toEnvExtension_1911_; lean_object* v_descr_1912_; lean_object* v_addEntryFn_1913_; lean_object* v_asyncMode_1914_; uint8_t v_logWrites_1915_; lean_object* v_entryDecl_x3f_1916_; lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v_declName_1921_; 
v_ext_1910_ = lean_ctor_get(v_ext_1907_, 1);
lean_inc_ref(v_ext_1910_);
v_toEnvExtension_1911_ = lean_ctor_get(v_ext_1910_, 0);
lean_inc_ref(v_toEnvExtension_1911_);
v_descr_1912_ = lean_ctor_get(v_ext_1907_, 0);
lean_inc_ref(v_descr_1912_);
lean_dec_ref(v_ext_1907_);
v_addEntryFn_1913_ = lean_ctor_get(v_ext_1910_, 3);
lean_inc(v_addEntryFn_1913_);
lean_dec_ref(v_ext_1910_);
v_asyncMode_1914_ = lean_ctor_get(v_toEnvExtension_1911_, 2);
lean_inc(v_asyncMode_1914_);
v_logWrites_1915_ = lean_ctor_get_uint8(v_toEnvExtension_1911_, sizeof(void*)*6);
v_entryDecl_x3f_1916_ = lean_ctor_get(v_descr_1912_, 7);
lean_inc(v_entryDecl_x3f_1916_);
lean_dec_ref(v_descr_1912_);
lean_inc(v_b_1909_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_b_1909_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1918_, 0, v_addEntryFn_1913_);
lean_closure_set(v___f_1918_, 1, v___x_1917_);
v___x_1919_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1916_) == 1)
{
lean_object* v_val_1926_; lean_object* v___x_1927_; 
v_val_1926_ = lean_ctor_get(v_entryDecl_x3f_1916_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v_entryDecl_x3f_1916_, 1);
v___x_1927_ = lean_apply_1(v_val_1926_, v_b_1909_);
v_declName_1921_ = v___x_1927_;
goto v___jp_1920_;
}
else
{
lean_dec(v_entryDecl_x3f_1916_);
lean_dec(v_b_1909_);
v_declName_1921_ = v___x_1919_;
goto v___jp_1920_;
}
v___jp_1920_:
{
uint8_t v___x_1922_; 
v___x_1922_ = 1;
if (v_logWrites_1915_ == 0)
{
lean_object* v___x_1923_; 
lean_dec(v_declName_1921_);
v___x_1923_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1911_, v_env_1908_, v___f_1918_, v_asyncMode_1914_, v___x_1919_, v___x_1922_);
lean_dec(v_asyncMode_1914_);
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = l_Lean_Environment_logDeclChange(v_env_1908_, v_declName_1921_);
v___x_1925_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1911_, v___x_1924_, v___f_1918_, v_asyncMode_1914_, v___x_1919_, v___x_1922_);
lean_dec(v_asyncMode_1914_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_1928_, lean_object* v_00_u03b2_1929_, lean_object* v_00_u03c3_1930_, lean_object* v_ext_1931_, lean_object* v_env_1932_, lean_object* v_b_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_1931_, v_env_1932_, v_b_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_1935_, lean_object* v_env_1936_, lean_object* v_namespaceName_1937_, lean_object* v_b_1938_){
_start:
{
lean_object* v_ext_1939_; lean_object* v_toEnvExtension_1940_; lean_object* v_descr_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1962_; 
v_ext_1939_ = lean_ctor_get(v_ext_1935_, 1);
lean_inc_ref(v_ext_1939_);
v_toEnvExtension_1940_ = lean_ctor_get(v_ext_1939_, 0);
lean_inc_ref(v_toEnvExtension_1940_);
v_descr_1941_ = lean_ctor_get(v_ext_1935_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_ext_1935_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_ext_1935_, 1);
lean_dec(v_unused_1963_);
v___x_1943_ = v_ext_1935_;
v_isShared_1944_ = v_isSharedCheck_1962_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_descr_1941_);
lean_dec(v_ext_1935_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1962_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_addEntryFn_1945_; lean_object* v_asyncMode_1946_; uint8_t v_logWrites_1947_; lean_object* v_entryDecl_x3f_1948_; lean_object* v___x_1950_; 
v_addEntryFn_1945_ = lean_ctor_get(v_ext_1939_, 3);
lean_inc(v_addEntryFn_1945_);
lean_dec_ref(v_ext_1939_);
v_asyncMode_1946_ = lean_ctor_get(v_toEnvExtension_1940_, 2);
lean_inc(v_asyncMode_1946_);
v_logWrites_1947_ = lean_ctor_get_uint8(v_toEnvExtension_1940_, sizeof(void*)*6);
v_entryDecl_x3f_1948_ = lean_ctor_get(v_descr_1941_, 7);
lean_inc(v_entryDecl_x3f_1948_);
lean_dec_ref(v_descr_1941_);
lean_inc(v_b_1938_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 1);
lean_ctor_set(v___x_1943_, 1, v_b_1938_);
lean_ctor_set(v___x_1943_, 0, v_namespaceName_1937_);
v___x_1950_ = v___x_1943_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_namespaceName_1937_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_b_1938_);
v___x_1950_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v_declName_1954_; 
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1951_, 0, v_addEntryFn_1945_);
lean_closure_set(v___f_1951_, 1, v___x_1950_);
v___x_1952_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_1948_) == 1)
{
lean_object* v_val_1959_; lean_object* v___x_1960_; 
v_val_1959_ = lean_ctor_get(v_entryDecl_x3f_1948_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v_entryDecl_x3f_1948_, 1);
v___x_1960_ = lean_apply_1(v_val_1959_, v_b_1938_);
v_declName_1954_ = v___x_1960_;
goto v___jp_1953_;
}
else
{
lean_dec(v_entryDecl_x3f_1948_);
lean_dec(v_b_1938_);
v_declName_1954_ = v___x_1952_;
goto v___jp_1953_;
}
v___jp_1953_:
{
uint8_t v___x_1955_; 
v___x_1955_ = 1;
if (v_logWrites_1947_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_declName_1954_);
v___x_1956_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1940_, v_env_1936_, v___f_1951_, v_asyncMode_1946_, v___x_1952_, v___x_1955_);
lean_dec(v_asyncMode_1946_);
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = l_Lean_Environment_logDeclChange(v_env_1936_, v_declName_1954_);
v___x_1958_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1940_, v___x_1957_, v___f_1951_, v_asyncMode_1946_, v___x_1952_, v___x_1955_);
lean_dec(v_asyncMode_1946_);
return v___x_1958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_00_u03c3_1966_, lean_object* v_ext_1967_, lean_object* v_env_1968_, lean_object* v_namespaceName_1969_, lean_object* v_b_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_1967_, v_env_1968_, v_namespaceName_1969_, v_b_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_1972_, lean_object* v_states_1973_, lean_object* v_b_1974_){
_start:
{
if (lean_obj_tag(v_states_1973_) == 0)
{
lean_dec(v_b_1974_);
lean_dec_ref(v_ext_1972_);
return v_states_1973_;
}
else
{
lean_object* v_descr_1975_; lean_object* v_head_1976_; lean_object* v_tail_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2004_; 
v_descr_1975_ = lean_ctor_get(v_ext_1972_, 0);
v_head_1976_ = lean_ctor_get(v_states_1973_, 0);
v_tail_1977_ = lean_ctor_get(v_states_1973_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_states_1973_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1979_ = v_states_1973_;
v_isShared_1980_ = v_isSharedCheck_2004_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_tail_1977_);
lean_inc(v_head_1976_);
lean_dec(v_states_1973_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2004_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_addEntry_1981_; lean_object* v_state_1982_; lean_object* v_activeScopes_1983_; uint8_t v_delimitsLocal_1984_; uint8_t v_scopeChanged_1985_; lean_object* v_scopeChangedDecls_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2003_; 
v_addEntry_1981_ = lean_ctor_get(v_descr_1975_, 4);
v_state_1982_ = lean_ctor_get(v_head_1976_, 0);
v_activeScopes_1983_ = lean_ctor_get(v_head_1976_, 1);
v_delimitsLocal_1984_ = lean_ctor_get_uint8(v_head_1976_, sizeof(void*)*3);
v_scopeChanged_1985_ = lean_ctor_get_uint8(v_head_1976_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1986_ = lean_ctor_get(v_head_1976_, 2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_head_1976_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1988_ = v_head_1976_;
v_isShared_1989_ = v_isSharedCheck_2003_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_scopeChangedDecls_1986_);
lean_inc(v_activeScopes_1983_);
lean_inc(v_state_1982_);
lean_dec(v_head_1976_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2003_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_inc(v_addEntry_1981_);
lean_inc(v_b_1974_);
v___x_1990_ = lean_apply_2(v_addEntry_1981_, v_state_1982_, v_b_1974_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_activeScopes_1983_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_scopeChangedDecls_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*3, v_delimitsLocal_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*3 + 1, v_scopeChanged_1985_);
v___x_1992_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v_top_1993_; uint8_t v_delimitsLocal_1994_; 
lean_inc(v_b_1974_);
lean_inc_ref(v_descr_1975_);
v_top_1993_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1975_, v___x_1992_, v_b_1974_);
v_delimitsLocal_1994_ = lean_ctor_get_uint8(v_top_1993_, sizeof(void*)*3);
if (v_delimitsLocal_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = l_Lean_stateStackModify___redArg(v_ext_1972_, v_tail_1977_, v_b_1974_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1995_);
lean_ctor_set(v___x_1979_, 0, v_top_1993_);
v___x_1997_ = v___x_1979_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_top_1993_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
else
{
lean_object* v___x_2000_; 
lean_dec(v_b_1974_);
lean_dec_ref(v_ext_1972_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v_top_1993_);
v___x_2000_ = v___x_1979_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_top_1993_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_tail_1977_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_2005_, lean_object* v_00_u03b2_2006_, lean_object* v_00_u03c3_2007_, lean_object* v_ext_2008_, lean_object* v_states_2009_, lean_object* v_b_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_stateStackModify___redArg(v_ext_2008_, v_states_2009_, v_b_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_2012_, lean_object* v_b_2013_, lean_object* v_ps_2014_){
_start:
{
lean_object* v_state_2015_; lean_object* v_importedEntries_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2034_; 
v_state_2015_ = lean_ctor_get(v_ps_2014_, 1);
v_importedEntries_2016_ = lean_ctor_get(v_ps_2014_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_ps_2014_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2018_ = v_ps_2014_;
v_isShared_2019_ = v_isSharedCheck_2034_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_state_2015_);
lean_inc(v_importedEntries_2016_);
lean_dec(v_ps_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2034_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_stateStack_2020_; lean_object* v_scopedEntries_2021_; lean_object* v_newEntries_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2033_; 
v_stateStack_2020_ = lean_ctor_get(v_state_2015_, 0);
v_scopedEntries_2021_ = lean_ctor_get(v_state_2015_, 1);
v_newEntries_2022_ = lean_ctor_get(v_state_2015_, 2);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_state_2015_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2024_ = v_state_2015_;
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_newEntries_2022_);
lean_inc(v_scopedEntries_2021_);
lean_inc(v_stateStack_2020_);
lean_dec(v_state_2015_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = l_Lean_stateStackModify___redArg(v_ext_2012_, v_stateStack_2020_, v_b_2013_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_scopedEntries_2021_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_newEntries_2022_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2028_);
v___x_2030_ = v___x_2018_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_importedEntries_2016_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_2035_, lean_object* v_env_2036_, lean_object* v_b_2037_){
_start:
{
lean_object* v_descr_2038_; lean_object* v_ext_2039_; lean_object* v_entryDecl_x3f_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v_declName_2046_; 
v_descr_2038_ = lean_ctor_get(v_ext_2035_, 0);
v_ext_2039_ = lean_ctor_get(v_ext_2035_, 1);
lean_inc_ref(v_ext_2039_);
v_entryDecl_x3f_2040_ = lean_ctor_get(v_descr_2038_, 7);
lean_inc(v_entryDecl_x3f_2040_);
lean_inc(v_b_2037_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2041_, 0, v_ext_2035_);
lean_closure_set(v___f_2041_, 1, v_b_2037_);
v___x_2042_ = lean_box(1);
v___x_2043_ = lean_box(0);
v___x_2044_ = 1;
if (lean_obj_tag(v_entryDecl_x3f_2040_) == 1)
{
lean_object* v_val_2052_; lean_object* v___x_2053_; 
v_val_2052_ = lean_ctor_get(v_entryDecl_x3f_2040_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v_entryDecl_x3f_2040_, 1);
v___x_2053_ = lean_apply_1(v_val_2052_, v_b_2037_);
v_declName_2046_ = v___x_2053_;
goto v___jp_2045_;
}
else
{
lean_dec(v_entryDecl_x3f_2040_);
lean_dec(v_b_2037_);
v_declName_2046_ = v___x_2043_;
goto v___jp_2045_;
}
v___jp_2045_:
{
lean_object* v_toEnvExtension_2047_; uint8_t v_logWrites_2048_; 
v_toEnvExtension_2047_ = lean_ctor_get(v_ext_2039_, 0);
lean_inc_ref(v_toEnvExtension_2047_);
lean_dec_ref(v_ext_2039_);
v_logWrites_2048_ = lean_ctor_get_uint8(v_toEnvExtension_2047_, sizeof(void*)*6);
if (v_logWrites_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_declName_2046_);
v___x_2049_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2047_, v_env_2036_, v___f_2041_, v___x_2042_, v___x_2043_, v___x_2044_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = l_Lean_Environment_logDeclChange(v_env_2036_, v_declName_2046_);
v___x_2051_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2047_, v___x_2050_, v___f_2041_, v___x_2042_, v___x_2043_, v___x_2044_);
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_00_u03c3_2056_, lean_object* v_ext_2057_, lean_object* v_env_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2057_, v_env_2058_, v_b_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_2061_, lean_object* v_ext_2062_, lean_object* v_b_2063_, uint8_t v_kind_2064_, lean_object* v_namespaceName_2065_){
_start:
{
switch(v_kind_2064_)
{
case 0:
{
lean_object* v___x_2066_; 
lean_dec(v_namespaceName_2065_);
v___x_2066_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_2062_, v_env_2061_, v_b_2063_);
return v___x_2066_;
}
case 1:
{
lean_object* v___x_2067_; 
lean_dec(v_namespaceName_2065_);
v___x_2067_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2062_, v_env_2061_, v_b_2063_);
return v___x_2067_;
}
default: 
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2062_, v_env_2061_, v_namespaceName_2065_, v_b_2063_);
return v___x_2068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_2069_, lean_object* v_ext_2070_, lean_object* v_b_2071_, lean_object* v_kind_2072_, lean_object* v_namespaceName_2073_){
_start:
{
uint8_t v_kind_boxed_2074_; lean_object* v_res_2075_; 
v_kind_boxed_2074_ = lean_unbox(v_kind_2072_);
v_res_2075_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2069_, v_ext_2070_, v_b_2071_, v_kind_boxed_2074_, v_namespaceName_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_00_u03c3_2078_, lean_object* v_env_2079_, lean_object* v_ext_2080_, lean_object* v_b_2081_, uint8_t v_kind_2082_, lean_object* v_namespaceName_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2079_, v_ext_2080_, v_b_2081_, v_kind_2082_, v_namespaceName_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_00_u03c3_2087_, lean_object* v_env_2088_, lean_object* v_ext_2089_, lean_object* v_b_2090_, lean_object* v_kind_2091_, lean_object* v_namespaceName_2092_){
_start:
{
uint8_t v_kind_boxed_2093_; lean_object* v_res_2094_; 
v_kind_boxed_2093_ = lean_unbox(v_kind_2091_);
v_res_2094_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_2085_, v_00_u03b2_2086_, v_00_u03c3_2087_, v_env_2088_, v_ext_2089_, v_b_2090_, v_kind_boxed_2093_, v_namespaceName_2092_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_2095_, lean_object* v_b_2096_, uint8_t v_kind_2097_, lean_object* v_ns_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_2099_, v_ext_2095_, v_b_2096_, v_kind_2097_, v_ns_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_2101_, lean_object* v_b_2102_, lean_object* v_kind_2103_, lean_object* v_ns_2104_, lean_object* v_x_2105_){
_start:
{
uint8_t v_kind_boxed_2106_; lean_object* v_res_2107_; 
v_kind_boxed_2106_ = lean_unbox(v_kind_2103_);
v_res_2107_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_2101_, v_b_2102_, v_kind_boxed_2106_, v_ns_2104_, v_x_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_2108_, lean_object* v_ext_2109_, lean_object* v_b_2110_, uint8_t v_kind_2111_, lean_object* v_ns_2112_){
_start:
{
lean_object* v_modifyEnv_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; 
v_modifyEnv_2113_ = lean_ctor_get(v_inst_2108_, 1);
lean_inc(v_modifyEnv_2113_);
lean_dec_ref(v_inst_2108_);
v___x_2114_ = lean_box(v_kind_2111_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2115_, 0, v_ext_2109_);
lean_closure_set(v___f_2115_, 1, v_b_2110_);
lean_closure_set(v___f_2115_, 2, v___x_2114_);
lean_closure_set(v___f_2115_, 3, v_ns_2112_);
v___x_2116_ = lean_apply_1(v_modifyEnv_2113_, v___f_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_2117_, lean_object* v_ext_2118_, lean_object* v_b_2119_, lean_object* v_kind_2120_, lean_object* v_ns_2121_){
_start:
{
uint8_t v_kind_boxed_2122_; lean_object* v_res_2123_; 
v_kind_boxed_2122_ = lean_unbox(v_kind_2120_);
v_res_2123_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_2117_, v_ext_2118_, v_b_2119_, v_kind_boxed_2122_, v_ns_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_ext_2127_, lean_object* v_b_2128_, uint8_t v_kind_2129_){
_start:
{
lean_object* v_toBind_2130_; lean_object* v_getCurrNamespace_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; 
v_toBind_2130_ = lean_ctor_get(v_inst_2124_, 1);
lean_inc(v_toBind_2130_);
lean_dec_ref(v_inst_2124_);
v_getCurrNamespace_2131_ = lean_ctor_get(v_inst_2125_, 0);
lean_inc(v_getCurrNamespace_2131_);
lean_dec_ref(v_inst_2125_);
v___x_2132_ = lean_box(v_kind_2129_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2133_, 0, v_inst_2126_);
lean_closure_set(v___f_2133_, 1, v_ext_2127_);
lean_closure_set(v___f_2133_, 2, v_b_2128_);
lean_closure_set(v___f_2133_, 3, v___x_2132_);
v___x_2134_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v_getCurrNamespace_2131_, v___f_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_ext_2138_, lean_object* v_b_2139_, lean_object* v_kind_2140_){
_start:
{
uint8_t v_kind_boxed_2141_; lean_object* v_res_2142_; 
v_kind_boxed_2141_ = lean_unbox(v_kind_2140_);
v_res_2142_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2135_, v_inst_2136_, v_inst_2137_, v_ext_2138_, v_b_2139_, v_kind_boxed_2141_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_2143_, lean_object* v_00_u03b1_2144_, lean_object* v_00_u03b2_2145_, lean_object* v_00_u03c3_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_ext_2150_, lean_object* v_b_2151_, uint8_t v_kind_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2147_, v_inst_2148_, v_inst_2149_, v_ext_2150_, v_b_2151_, v_kind_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_2154_, lean_object* v_00_u03b1_2155_, lean_object* v_00_u03b2_2156_, lean_object* v_00_u03c3_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_ext_2161_, lean_object* v_b_2162_, lean_object* v_kind_2163_){
_start:
{
uint8_t v_kind_boxed_2164_; lean_object* v_res_2165_; 
v_kind_boxed_2164_ = lean_unbox(v_kind_2163_);
v_res_2165_ = l_Lean_ScopedEnvExtension_add(v_m_2154_, v_00_u03b1_2155_, v_00_u03b2_2156_, v_00_u03c3_2157_, v_inst_2158_, v_inst_2159_, v_inst_2160_, v_ext_2161_, v_b_2162_, v_kind_boxed_2164_);
return v_res_2165_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_2170_ = lean_unsigned_to_nat(16u);
v___x_2171_ = lean_unsigned_to_nat(285u);
v___x_2172_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_2173_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_2174_ = l_mkPanicMessageWithDecl(v___x_2173_, v___x_2172_, v___x_2171_, v___x_2170_, v___x_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_2175_, lean_object* v_ext_2176_, lean_object* v_env_2177_, lean_object* v_asyncMode_2178_, uint8_t v_genRecorded_2179_){
_start:
{
lean_object* v_ext_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v_stateStack_2184_; 
v_ext_2180_ = lean_ctor_get(v_ext_2176_, 1);
v___x_2181_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2182_ = lean_box(0);
v___x_2183_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2181_, v_ext_2180_, v_env_2177_, v_asyncMode_2178_, v___x_2182_, v_genRecorded_2179_);
v_stateStack_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_stateStack_2184_);
lean_dec(v___x_2183_);
if (lean_obj_tag(v_stateStack_2184_) == 1)
{
lean_object* v_head_2185_; lean_object* v_state_2186_; 
v_head_2185_ = lean_ctor_get(v_stateStack_2184_, 0);
lean_inc(v_head_2185_);
lean_dec_ref_known(v_stateStack_2184_, 2);
v_state_2186_ = lean_ctor_get(v_head_2185_, 0);
lean_inc(v_state_2186_);
lean_dec(v_head_2185_);
return v_state_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_dec(v_stateStack_2184_);
v___x_2187_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_2188_ = l_panic___redArg(v_inst_2175_, v___x_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_2189_, lean_object* v_ext_2190_, lean_object* v_env_2191_, lean_object* v_asyncMode_2192_, lean_object* v_genRecorded_2193_){
_start:
{
uint8_t v_genRecorded_boxed_2194_; lean_object* v_res_2195_; 
v_genRecorded_boxed_2194_ = lean_unbox(v_genRecorded_2193_);
v_res_2195_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2189_, v_ext_2190_, v_env_2191_, v_asyncMode_2192_, v_genRecorded_boxed_2194_);
lean_dec(v_asyncMode_2192_);
lean_dec_ref(v_ext_2190_);
lean_dec(v_inst_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_2196_, lean_object* v_00_u03b1_2197_, lean_object* v_00_u03b2_2198_, lean_object* v_inst_2199_, lean_object* v_ext_2200_, lean_object* v_env_2201_, lean_object* v_asyncMode_2202_, uint8_t v_genRecorded_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2199_, v_ext_2200_, v_env_2201_, v_asyncMode_2202_, v_genRecorded_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_2205_, lean_object* v_00_u03b1_2206_, lean_object* v_00_u03b2_2207_, lean_object* v_inst_2208_, lean_object* v_ext_2209_, lean_object* v_env_2210_, lean_object* v_asyncMode_2211_, lean_object* v_genRecorded_2212_){
_start:
{
uint8_t v_genRecorded_boxed_2213_; lean_object* v_res_2214_; 
v_genRecorded_boxed_2213_ = lean_unbox(v_genRecorded_2212_);
v_res_2214_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_2205_, v_00_u03b1_2206_, v_00_u03b2_2207_, v_inst_2208_, v_ext_2209_, v_env_2210_, v_asyncMode_2211_, v_genRecorded_boxed_2213_);
lean_dec(v_asyncMode_2211_);
lean_dec_ref(v_ext_2209_);
lean_dec(v_inst_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v___y_2215_, lean_object* v_tail_2216_, lean_object* v_s_2217_){
_start:
{
lean_object* v_scopedEntries_2218_; lean_object* v_newEntries_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2227_; 
v_scopedEntries_2218_ = lean_ctor_get(v_s_2217_, 1);
v_newEntries_2219_ = lean_ctor_get(v_s_2217_, 2);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_s_2217_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v_s_2217_, 0);
lean_dec(v_unused_2228_);
v___x_2221_ = v_s_2217_;
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_newEntries_2219_);
lean_inc(v_scopedEntries_2218_);
lean_dec(v_s_2217_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___y_2215_);
lean_ctor_set(v___x_2223_, 1, v_tail_2216_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2223_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_scopedEntries_2218_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_newEntries_2219_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(lean_object* v_ext_2229_, lean_object* v_as_2230_, size_t v_i_2231_, size_t v_stop_2232_, lean_object* v_b_2233_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_eq(v_i_2231_, v_stop_2232_);
if (v___x_2234_ == 0)
{
lean_object* v_descr_2235_; lean_object* v_addEntry_2236_; lean_object* v_state_2237_; lean_object* v_activeScopes_2238_; uint8_t v_delimitsLocal_2239_; uint8_t v_scopeChanged_2240_; lean_object* v_scopeChangedDecls_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2254_; 
v_descr_2235_ = lean_ctor_get(v_ext_2229_, 0);
v_addEntry_2236_ = lean_ctor_get(v_descr_2235_, 4);
v_state_2237_ = lean_ctor_get(v_b_2233_, 0);
v_activeScopes_2238_ = lean_ctor_get(v_b_2233_, 1);
v_delimitsLocal_2239_ = lean_ctor_get_uint8(v_b_2233_, sizeof(void*)*3);
v_scopeChanged_2240_ = lean_ctor_get_uint8(v_b_2233_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2241_ = lean_ctor_get(v_b_2233_, 2);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2233_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2243_ = v_b_2233_;
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_scopeChangedDecls_2241_);
lean_inc(v_activeScopes_2238_);
lean_inc(v_state_2237_);
lean_dec(v_b_2233_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_array_uget_borrowed(v_as_2230_, v_i_2231_);
lean_inc(v_addEntry_2236_);
lean_inc(v___x_2245_);
v___x_2246_ = lean_apply_2(v_addEntry_2236_, v_state_2237_, v___x_2245_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_activeScopes_2238_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_scopeChangedDecls_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2253_, sizeof(void*)*3, v_delimitsLocal_2239_);
lean_ctor_set_uint8(v_reuseFailAlloc_2253_, sizeof(void*)*3 + 1, v_scopeChanged_2240_);
v___x_2248_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; 
lean_inc(v___x_2245_);
lean_inc_ref(v_descr_2235_);
v___x_2249_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2235_, v___x_2248_, v___x_2245_);
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2231_, v___x_2250_);
v_i_2231_ = v___x_2251_;
v_b_2233_ = v___x_2249_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ext_2229_);
return v_b_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg___boxed(lean_object* v_ext_2255_, lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_stop_2258_, lean_object* v_b_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2258_);
lean_dec(v_stop_2258_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2255_, v_as_2256_, v_i_boxed_2260_, v_stop_boxed_2261_, v_b_2259_);
lean_dec_ref(v_as_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(lean_object* v_ext_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2264_) == 0)
{
lean_object* v_cs_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_cs_2266_ = lean_ctor_get(v_x_2264_, 0);
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_array_get_size(v_cs_2266_);
v___x_2269_ = lean_nat_dec_lt(v___x_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v_ext_2263_);
return v_x_2265_;
}
else
{
size_t v___x_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = lean_usize_of_nat(v___x_2268_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2263_, v_cs_2266_, v___x_2270_, v___x_2271_, v_x_2265_);
return v___x_2272_;
}
}
else
{
lean_object* v_vs_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_vs_2273_ = lean_ctor_get(v_x_2264_, 0);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = lean_array_get_size(v_vs_2273_);
v___x_2276_ = lean_nat_dec_lt(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_dec_ref(v_ext_2263_);
return v_x_2265_;
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2275_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2263_, v_vs_2273_, v___x_2277_, v___x_2278_, v_x_2265_);
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(lean_object* v_ext_2280_, lean_object* v_as_2281_, size_t v_i_2282_, size_t v_stop_2283_, lean_object* v_b_2284_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_usize_dec_eq(v_i_2282_, v_stop_2283_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; 
v___x_2286_ = lean_array_uget_borrowed(v_as_2281_, v_i_2282_);
lean_inc_ref(v_ext_2280_);
v___x_2287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2280_, v___x_2286_, v_b_2284_);
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_add(v_i_2282_, v___x_2288_);
v_i_2282_ = v___x_2289_;
v_b_2284_ = v___x_2287_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2280_);
return v_b_2284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ext_2291_, lean_object* v_as_2292_, lean_object* v_i_2293_, lean_object* v_stop_2294_, lean_object* v_b_2295_){
_start:
{
size_t v_i_boxed_2296_; size_t v_stop_boxed_2297_; lean_object* v_res_2298_; 
v_i_boxed_2296_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_stop_boxed_2297_ = lean_unbox_usize(v_stop_2294_);
lean_dec(v_stop_2294_);
v_res_2298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2291_, v_as_2292_, v_i_boxed_2296_, v_stop_boxed_2297_, v_b_2295_);
lean_dec_ref(v_as_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg___boxed(lean_object* v_ext_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2299_, v_x_2300_, v_x_2301_);
lean_dec_ref(v_x_2300_);
return v_res_2302_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(lean_object* v_ext_2304_, lean_object* v_x_2305_, size_t v_x_2306_, size_t v_x_2307_, lean_object* v_x_2308_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
lean_object* v_cs_2309_; lean_object* v___x_2310_; size_t v___x_2311_; lean_object* v_j_2312_; lean_object* v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_cs_2309_ = lean_ctor_get(v_x_2305_, 0);
v___x_2310_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2311_ = lean_usize_shift_right(v_x_2306_, v_x_2307_);
v_j_2312_ = lean_usize_to_nat(v___x_2311_);
v___x_2313_ = lean_array_get_borrowed(v___x_2310_, v_cs_2309_, v_j_2312_);
v___x_2314_ = ((size_t)1ULL);
v___x_2315_ = lean_usize_shift_left(v___x_2314_, v_x_2307_);
v___x_2316_ = lean_usize_sub(v___x_2315_, v___x_2314_);
v___x_2317_ = lean_usize_land(v_x_2306_, v___x_2316_);
v___x_2318_ = ((size_t)5ULL);
v___x_2319_ = lean_usize_sub(v_x_2307_, v___x_2318_);
lean_inc_ref(v_ext_2304_);
v___x_2320_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2304_, v___x_2313_, v___x_2317_, v___x_2319_, v_x_2308_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v_j_2312_, v___x_2321_);
lean_dec(v_j_2312_);
v___x_2323_ = lean_array_get_size(v_cs_2309_);
v___x_2324_ = lean_nat_dec_lt(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec(v___x_2322_);
lean_dec_ref(v_ext_2304_);
return v___x_2320_;
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_usize_of_nat(v___x_2323_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2304_, v_cs_2309_, v___x_2325_, v___x_2326_, v___x_2320_);
return v___x_2327_;
}
}
else
{
lean_object* v_vs_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_vs_2328_ = lean_ctor_get(v_x_2305_, 0);
v___x_2329_ = lean_usize_to_nat(v_x_2306_);
v___x_2330_ = lean_array_get_size(v_vs_2328_);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v___x_2329_);
lean_dec_ref(v_ext_2304_);
return v_x_2308_;
}
else
{
size_t v___x_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_usize_of_nat(v___x_2329_);
lean_dec(v___x_2329_);
v___x_2333_ = lean_usize_of_nat(v___x_2330_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2304_, v_vs_2328_, v___x_2332_, v___x_2333_, v_x_2308_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_2633__boxed_2340_; size_t v_x_2634__boxed_2341_; lean_object* v_res_2342_; 
v_x_2633__boxed_2340_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_x_2634__boxed_2341_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2342_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2335_, v_x_2336_, v_x_2633__boxed_2340_, v_x_2634__boxed_2341_, v_x_2339_);
lean_dec_ref(v_x_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(lean_object* v_ext_2343_, lean_object* v_t_2344_, lean_object* v_init_2345_, lean_object* v_start_2346_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_nat_dec_eq(v_start_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v_root_2349_; lean_object* v_tail_2350_; size_t v_shift_2351_; lean_object* v_tailOff_2352_; uint8_t v___x_2353_; 
v_root_2349_ = lean_ctor_get(v_t_2344_, 0);
v_tail_2350_ = lean_ctor_get(v_t_2344_, 1);
v_shift_2351_ = lean_ctor_get_usize(v_t_2344_, 4);
v_tailOff_2352_ = lean_ctor_get(v_t_2344_, 3);
v___x_2353_ = lean_nat_dec_le(v_tailOff_2352_, v_start_2346_);
if (v___x_2353_ == 0)
{
size_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2354_ = lean_usize_of_nat(v_start_2346_);
lean_inc_ref(v_ext_2343_);
v___x_2355_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2343_, v_root_2349_, v___x_2354_, v_shift_2351_, v_init_2345_);
v___x_2356_ = lean_array_get_size(v_tail_2350_);
v___x_2357_ = lean_nat_dec_lt(v___x_2347_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec_ref(v_ext_2343_);
return v___x_2355_;
}
else
{
size_t v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = lean_usize_of_nat(v___x_2356_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2343_, v_tail_2350_, v___x_2358_, v___x_2359_, v___x_2355_);
return v___x_2360_;
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = lean_nat_sub(v_start_2346_, v_tailOff_2352_);
v___x_2362_ = lean_array_get_size(v_tail_2350_);
v___x_2363_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v___x_2361_);
lean_dec_ref(v_ext_2343_);
return v_init_2345_;
}
else
{
size_t v___x_2364_; size_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = lean_usize_of_nat(v___x_2361_);
lean_dec(v___x_2361_);
v___x_2365_ = lean_usize_of_nat(v___x_2362_);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2343_, v_tail_2350_, v___x_2364_, v___x_2365_, v_init_2345_);
return v___x_2366_;
}
}
}
else
{
lean_object* v_root_2367_; lean_object* v_tail_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_root_2367_ = lean_ctor_get(v_t_2344_, 0);
v_tail_2368_ = lean_ctor_get(v_t_2344_, 1);
lean_inc_ref(v_ext_2343_);
v___x_2369_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2343_, v_root_2367_, v_init_2345_);
v___x_2370_ = lean_array_get_size(v_tail_2368_);
v___x_2371_ = lean_nat_dec_lt(v___x_2347_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec_ref(v_ext_2343_);
return v___x_2369_;
}
else
{
size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = ((size_t)0ULL);
v___x_2373_ = lean_usize_of_nat(v___x_2370_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2343_, v_tail_2368_, v___x_2372_, v___x_2373_, v___x_2369_);
return v___x_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg___boxed(lean_object* v_ext_2375_, lean_object* v_t_2376_, lean_object* v_init_2377_, lean_object* v_start_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2375_, v_t_2376_, v_init_2377_, v_start_2378_);
lean_dec(v_start_2378_);
lean_dec_ref(v_t_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_val_2380_, lean_object* v_as_2381_, size_t v_i_2382_, size_t v_stop_2383_, lean_object* v_b_2384_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_usize_dec_eq(v_i_2382_, v_stop_2383_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; size_t v___x_2389_; size_t v___x_2390_; 
v___x_2386_ = lean_array_uget_borrowed(v_as_2381_, v_i_2382_);
lean_inc_ref(v_val_2380_);
lean_inc(v___x_2386_);
v___x_2387_ = lean_apply_1(v_val_2380_, v___x_2386_);
v___x_2388_ = lean_array_push(v_b_2384_, v___x_2387_);
v___x_2389_ = ((size_t)1ULL);
v___x_2390_ = lean_usize_add(v_i_2382_, v___x_2389_);
v_i_2382_ = v___x_2390_;
v_b_2384_ = v___x_2388_;
goto _start;
}
else
{
lean_dec_ref(v_val_2380_);
return v_b_2384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_val_2392_, lean_object* v_as_2393_, lean_object* v_i_2394_, lean_object* v_stop_2395_, lean_object* v_b_2396_){
_start:
{
size_t v_i_boxed_2397_; size_t v_stop_boxed_2398_; lean_object* v_res_2399_; 
v_i_boxed_2397_ = lean_unbox_usize(v_i_2394_);
lean_dec(v_i_2394_);
v_stop_boxed_2398_ = lean_unbox_usize(v_stop_2395_);
lean_dec(v_stop_2395_);
v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2392_, v_as_2393_, v_i_boxed_2397_, v_stop_boxed_2398_, v_b_2396_);
lean_dec_ref(v_as_2393_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object* v_val_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
if (lean_obj_tag(v_x_2401_) == 0)
{
lean_object* v_cs_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_cs_2403_ = lean_ctor_get(v_x_2401_, 0);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_cs_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v_val_2400_);
return v_x_2402_;
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = ((size_t)0ULL);
v___x_2408_ = lean_usize_of_nat(v___x_2405_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2400_, v_cs_2403_, v___x_2407_, v___x_2408_, v_x_2402_);
return v___x_2409_;
}
}
else
{
lean_object* v_vs_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_vs_2410_ = lean_ctor_get(v_x_2401_, 0);
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_array_get_size(v_vs_2410_);
v___x_2413_ = lean_nat_dec_lt(v___x_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_val_2400_);
return v_x_2402_;
}
else
{
size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((size_t)0ULL);
v___x_2415_ = lean_usize_of_nat(v___x_2412_);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2400_, v_vs_2410_, v___x_2414_, v___x_2415_, v_x_2402_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_val_2417_, lean_object* v_as_2418_, size_t v_i_2419_, size_t v_stop_2420_, lean_object* v_b_2421_){
_start:
{
uint8_t v___x_2422_; 
v___x_2422_ = lean_usize_dec_eq(v_i_2419_, v_stop_2420_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; 
v___x_2423_ = lean_array_uget_borrowed(v_as_2418_, v_i_2419_);
lean_inc_ref(v_val_2417_);
v___x_2424_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2417_, v___x_2423_, v_b_2421_);
v___x_2425_ = ((size_t)1ULL);
v___x_2426_ = lean_usize_add(v_i_2419_, v___x_2425_);
v_i_2419_ = v___x_2426_;
v_b_2421_ = v___x_2424_;
goto _start;
}
else
{
lean_dec_ref(v_val_2417_);
return v_b_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_val_2428_, lean_object* v_as_2429_, lean_object* v_i_2430_, lean_object* v_stop_2431_, lean_object* v_b_2432_){
_start:
{
size_t v_i_boxed_2433_; size_t v_stop_boxed_2434_; lean_object* v_res_2435_; 
v_i_boxed_2433_ = lean_unbox_usize(v_i_2430_);
lean_dec(v_i_2430_);
v_stop_boxed_2434_ = lean_unbox_usize(v_stop_2431_);
lean_dec(v_stop_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2428_, v_as_2429_, v_i_boxed_2433_, v_stop_boxed_2434_, v_b_2432_);
lean_dec_ref(v_as_2429_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object* v_val_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2436_, v_x_2437_, v_x_2438_);
lean_dec_ref(v_x_2437_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_val_2440_, lean_object* v_x_2441_, size_t v_x_2442_, size_t v_x_2443_, lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_object* v_cs_2445_; lean_object* v___x_2446_; size_t v___x_2447_; lean_object* v_j_2448_; lean_object* v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_cs_2445_ = lean_ctor_get(v_x_2441_, 0);
v___x_2446_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2447_ = lean_usize_shift_right(v_x_2442_, v_x_2443_);
v_j_2448_ = lean_usize_to_nat(v___x_2447_);
v___x_2449_ = lean_array_get_borrowed(v___x_2446_, v_cs_2445_, v_j_2448_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_shift_left(v___x_2450_, v_x_2443_);
v___x_2452_ = lean_usize_sub(v___x_2451_, v___x_2450_);
v___x_2453_ = lean_usize_land(v_x_2442_, v___x_2452_);
v___x_2454_ = ((size_t)5ULL);
v___x_2455_ = lean_usize_sub(v_x_2443_, v___x_2454_);
lean_inc_ref(v_val_2440_);
v___x_2456_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2440_, v___x_2449_, v___x_2453_, v___x_2455_, v_x_2444_);
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2458_ = lean_nat_add(v_j_2448_, v___x_2457_);
lean_dec(v_j_2448_);
v___x_2459_ = lean_array_get_size(v_cs_2445_);
v___x_2460_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_dec(v___x_2458_);
lean_dec_ref(v_val_2440_);
return v___x_2456_;
}
else
{
size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = lean_usize_of_nat(v___x_2458_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_usize_of_nat(v___x_2459_);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2440_, v_cs_2445_, v___x_2461_, v___x_2462_, v___x_2456_);
return v___x_2463_;
}
}
else
{
lean_object* v_vs_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_vs_2464_ = lean_ctor_get(v_x_2441_, 0);
v___x_2465_ = lean_usize_to_nat(v_x_2442_);
v___x_2466_ = lean_array_get_size(v_vs_2464_);
v___x_2467_ = lean_nat_dec_lt(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v___x_2465_);
lean_dec_ref(v_val_2440_);
return v_x_2444_;
}
else
{
size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_usize_of_nat(v___x_2465_);
lean_dec(v___x_2465_);
v___x_2469_ = lean_usize_of_nat(v___x_2466_);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2440_, v_vs_2464_, v___x_2468_, v___x_2469_, v_x_2444_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_val_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
size_t v_x_2811__boxed_2476_; size_t v_x_2812__boxed_2477_; lean_object* v_res_2478_; 
v_x_2811__boxed_2476_ = lean_unbox_usize(v_x_2473_);
lean_dec(v_x_2473_);
v_x_2812__boxed_2477_ = lean_unbox_usize(v_x_2474_);
lean_dec(v_x_2474_);
v_res_2478_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2471_, v_x_2472_, v_x_2811__boxed_2476_, v_x_2812__boxed_2477_, v_x_2475_);
lean_dec_ref(v_x_2472_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_val_2479_, lean_object* v_t_2480_, lean_object* v_init_2481_, lean_object* v_start_2482_){
_start:
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = lean_nat_dec_eq(v_start_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v_root_2485_; lean_object* v_tail_2486_; size_t v_shift_2487_; lean_object* v_tailOff_2488_; uint8_t v___x_2489_; 
v_root_2485_ = lean_ctor_get(v_t_2480_, 0);
v_tail_2486_ = lean_ctor_get(v_t_2480_, 1);
v_shift_2487_ = lean_ctor_get_usize(v_t_2480_, 4);
v_tailOff_2488_ = lean_ctor_get(v_t_2480_, 3);
v___x_2489_ = lean_nat_dec_le(v_tailOff_2488_, v_start_2482_);
if (v___x_2489_ == 0)
{
size_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2490_ = lean_usize_of_nat(v_start_2482_);
lean_inc_ref(v_val_2479_);
v___x_2491_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2479_, v_root_2485_, v___x_2490_, v_shift_2487_, v_init_2481_);
v___x_2492_ = lean_array_get_size(v_tail_2486_);
v___x_2493_ = lean_nat_dec_lt(v___x_2483_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v_val_2479_);
return v___x_2491_;
}
else
{
size_t v___x_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = lean_usize_of_nat(v___x_2492_);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2479_, v_tail_2486_, v___x_2494_, v___x_2495_, v___x_2491_);
return v___x_2496_;
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2497_ = lean_nat_sub(v_start_2482_, v_tailOff_2488_);
v___x_2498_ = lean_array_get_size(v_tail_2486_);
v___x_2499_ = lean_nat_dec_lt(v___x_2497_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_dec(v___x_2497_);
lean_dec_ref(v_val_2479_);
return v_init_2481_;
}
else
{
size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = lean_usize_of_nat(v___x_2497_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_usize_of_nat(v___x_2498_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2479_, v_tail_2486_, v___x_2500_, v___x_2501_, v_init_2481_);
return v___x_2502_;
}
}
}
else
{
lean_object* v_root_2503_; lean_object* v_tail_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_root_2503_ = lean_ctor_get(v_t_2480_, 0);
v_tail_2504_ = lean_ctor_get(v_t_2480_, 1);
lean_inc_ref(v_val_2479_);
v___x_2505_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2479_, v_root_2503_, v_init_2481_);
v___x_2506_ = lean_array_get_size(v_tail_2504_);
v___x_2507_ = lean_nat_dec_lt(v___x_2483_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v_val_2479_);
return v___x_2505_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2506_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2479_, v_tail_2504_, v___x_2508_, v___x_2509_, v___x_2505_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_val_2511_, lean_object* v_t_2512_, lean_object* v_init_2513_, lean_object* v_start_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2511_, v_t_2512_, v_init_2513_, v_start_2514_);
lean_dec(v_start_2514_);
lean_dec_ref(v_t_2512_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2516_, lean_object* v_env_2517_, lean_object* v_namespaceName_2518_){
_start:
{
lean_object* v_descr_2519_; lean_object* v_ext_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v_s_2525_; lean_object* v_stateStack_2526_; 
v_descr_2519_ = lean_ctor_get(v_ext_2516_, 0);
v_ext_2520_ = lean_ctor_get(v_ext_2516_, 1);
v___x_2521_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2522_ = lean_box(1);
v___x_2523_ = lean_box(0);
v___x_2524_ = 0;
lean_inc_ref(v_env_2517_);
v_s_2525_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2521_, v_ext_2520_, v_env_2517_, v___x_2522_, v___x_2523_, v___x_2524_);
v_stateStack_2526_ = lean_ctor_get(v_s_2525_, 0);
lean_inc(v_stateStack_2526_);
if (lean_obj_tag(v_stateStack_2526_) == 1)
{
lean_object* v_head_2527_; lean_object* v_scopedEntries_2528_; lean_object* v_tail_2529_; lean_object* v_state_2530_; lean_object* v_activeScopes_2531_; uint8_t v_delimitsLocal_2532_; uint8_t v_scopeChanged_2533_; lean_object* v_scopeChangedDecls_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2569_; 
v_head_2527_ = lean_ctor_get(v_stateStack_2526_, 0);
lean_inc(v_head_2527_);
v_scopedEntries_2528_ = lean_ctor_get(v_s_2525_, 1);
lean_inc_ref(v_scopedEntries_2528_);
lean_dec(v_s_2525_);
v_tail_2529_ = lean_ctor_get(v_stateStack_2526_, 1);
lean_inc(v_tail_2529_);
lean_dec_ref_known(v_stateStack_2526_, 2);
v_state_2530_ = lean_ctor_get(v_head_2527_, 0);
v_activeScopes_2531_ = lean_ctor_get(v_head_2527_, 1);
v_delimitsLocal_2532_ = lean_ctor_get_uint8(v_head_2527_, sizeof(void*)*3);
v_scopeChanged_2533_ = lean_ctor_get_uint8(v_head_2527_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2534_ = lean_ctor_get(v_head_2527_, 2);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_head_2527_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2536_ = v_head_2527_;
v_isShared_2537_ = v_isSharedCheck_2569_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_scopeChangedDecls_2534_);
lean_inc(v_activeScopes_2531_);
lean_inc(v_state_2530_);
lean_dec(v_head_2527_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2569_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
uint8_t v___x_2538_; 
v___x_2538_ = l_Lean_NameSet_contains(v_activeScopes_2531_, v_namespaceName_2518_);
if (v___x_2538_ == 0)
{
lean_object* v_activeScopes_2539_; lean_object* v_bs_x3f_2540_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2548_; lean_object* v___y_2551_; 
lean_inc(v_namespaceName_2518_);
v_activeScopes_2539_ = l_Lean_NameSet_insert(v_activeScopes_2531_, v_namespaceName_2518_);
v_bs_x3f_2540_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2528_, v_namespaceName_2518_);
lean_dec(v_namespaceName_2518_);
lean_dec_ref(v_scopedEntries_2528_);
if (lean_obj_tag(v_bs_x3f_2540_) == 1)
{
lean_object* v_val_2559_; uint8_t v___x_2560_; lean_object* v___x_2562_; 
v_val_2559_ = lean_ctor_get(v_bs_x3f_2540_, 0);
v___x_2560_ = 1;
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v_activeScopes_2539_);
v___x_2562_ = v___x_2536_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_state_2530_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_activeScopes_2539_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_scopeChangedDecls_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2565_, sizeof(void*)*3 + 1, v_scopeChanged_2533_);
v___x_2562_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*3, v___x_2560_);
v___x_2563_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ext_2516_);
v___x_2564_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2516_, v_val_2559_, v___x_2562_, v___x_2563_);
v___y_2551_ = v___x_2564_;
goto v___jp_2550_;
}
}
else
{
lean_object* v___x_2567_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v_activeScopes_2539_);
v___x_2567_ = v___x_2536_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_state_2530_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_activeScopes_2539_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_scopeChangedDecls_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*3, v_delimitsLocal_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*3 + 1, v_scopeChanged_2533_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
v___y_2551_ = v___x_2567_;
goto v___jp_2550_;
}
}
v___jp_2541_:
{
if (lean_obj_tag(v_bs_x3f_2540_) == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2516_, v_env_2517_, v___x_2538_, v___y_2542_, v___y_2543_);
lean_dec_ref(v___y_2543_);
return v___x_2544_;
}
else
{
uint8_t v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref_known(v_bs_x3f_2540_, 1);
v___x_2545_ = 1;
v___x_2546_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2516_, v_env_2517_, v___x_2545_, v___y_2542_, v___y_2543_);
lean_dec_ref(v___y_2543_);
return v___x_2546_;
}
}
v___jp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___x_2549_;
goto v___jp_2541_;
}
v___jp_2550_:
{
lean_object* v___f_2552_; 
v___f_2552_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2552_, 0, v___y_2551_);
lean_closure_set(v___f_2552_, 1, v_tail_2529_);
if (lean_obj_tag(v_bs_x3f_2540_) == 1)
{
lean_object* v_entryDecl_x3f_2553_; 
v_entryDecl_x3f_2553_ = lean_ctor_get(v_descr_2519_, 7);
if (lean_obj_tag(v_entryDecl_x3f_2553_) == 1)
{
lean_object* v_val_2554_; lean_object* v_val_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_val_2554_ = lean_ctor_get(v_bs_x3f_2540_, 0);
v_val_2555_ = lean_ctor_get(v_entryDecl_x3f_2553_, 0);
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
lean_inc(v_val_2555_);
v___x_2558_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2555_, v_val_2554_, v___x_2557_, v___x_2556_);
v___y_2542_ = v___f_2552_;
v___y_2543_ = v___x_2558_;
goto v___jp_2541_;
}
else
{
v___y_2548_ = v___f_2552_;
goto v___jp_2547_;
}
}
else
{
v___y_2548_ = v___f_2552_;
goto v___jp_2547_;
}
}
}
else
{
lean_del_object(v___x_2536_);
lean_dec_ref(v_scopeChangedDecls_2534_);
lean_dec(v_activeScopes_2531_);
lean_dec(v_state_2530_);
lean_dec(v_tail_2529_);
lean_dec_ref(v_scopedEntries_2528_);
lean_dec(v_namespaceName_2518_);
lean_dec_ref(v_ext_2516_);
return v_env_2517_;
}
}
}
else
{
lean_dec(v_stateStack_2526_);
lean_dec(v_s_2525_);
lean_dec(v_namespaceName_2518_);
lean_dec_ref(v_ext_2516_);
return v_env_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2570_, lean_object* v_00_u03b2_2571_, lean_object* v_00_u03c3_2572_, lean_object* v_ext_2573_, lean_object* v_env_2574_, lean_object* v_namespaceName_2575_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2573_, v_env_2574_, v_namespaceName_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2577_, lean_object* v_val_2578_, lean_object* v_t_2579_, lean_object* v_init_2580_, lean_object* v_start_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2578_, v_t_2579_, v_init_2580_, v_start_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2583_, lean_object* v_val_2584_, lean_object* v_t_2585_, lean_object* v_init_2586_, lean_object* v_start_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2583_, v_val_2584_, v_t_2585_, v_init_2586_, v_start_2587_);
lean_dec(v_start_2587_);
lean_dec_ref(v_t_2585_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(lean_object* v_00_u03b2_2589_, lean_object* v_00_u03c3_2590_, lean_object* v_00_u03b1_2591_, lean_object* v_ext_2592_, lean_object* v_t_2593_, lean_object* v_init_2594_, lean_object* v_start_2595_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2592_, v_t_2593_, v_init_2594_, v_start_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___boxed(lean_object* v_00_u03b2_2597_, lean_object* v_00_u03c3_2598_, lean_object* v_00_u03b1_2599_, lean_object* v_ext_2600_, lean_object* v_t_2601_, lean_object* v_init_2602_, lean_object* v_start_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(v_00_u03b2_2597_, v_00_u03c3_2598_, v_00_u03b1_2599_, v_ext_2600_, v_t_2601_, v_init_2602_, v_start_2603_);
lean_dec(v_start_2603_);
lean_dec_ref(v_t_2601_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2605_, lean_object* v_val_2606_, lean_object* v_x_2607_, size_t v_x_2608_, size_t v_x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2606_, v_x_2607_, v_x_2608_, v_x_2609_, v_x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2612_, lean_object* v_val_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_){
_start:
{
size_t v_x_3015__boxed_2618_; size_t v_x_3016__boxed_2619_; lean_object* v_res_2620_; 
v_x_3015__boxed_2618_ = lean_unbox_usize(v_x_2615_);
lean_dec(v_x_2615_);
v_x_3016__boxed_2619_ = lean_unbox_usize(v_x_2616_);
lean_dec(v_x_2616_);
v_res_2620_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2612_, v_val_2613_, v_x_2614_, v_x_3015__boxed_2618_, v_x_3016__boxed_2619_, v_x_2617_);
lean_dec_ref(v_x_2614_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2621_, lean_object* v_val_2622_, lean_object* v_as_2623_, size_t v_i_2624_, size_t v_stop_2625_, lean_object* v_b_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2622_, v_as_2623_, v_i_2624_, v_stop_2625_, v_b_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2628_, lean_object* v_val_2629_, lean_object* v_as_2630_, lean_object* v_i_2631_, lean_object* v_stop_2632_, lean_object* v_b_2633_){
_start:
{
size_t v_i_boxed_2634_; size_t v_stop_boxed_2635_; lean_object* v_res_2636_; 
v_i_boxed_2634_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_stop_boxed_2635_ = lean_unbox_usize(v_stop_2632_);
lean_dec(v_stop_2632_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2628_, v_val_2629_, v_as_2630_, v_i_boxed_2634_, v_stop_boxed_2635_, v_b_2633_);
lean_dec_ref(v_as_2630_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object* v_00_u03b2_2637_, lean_object* v_val_2638_, lean_object* v_x_2639_, lean_object* v_x_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2638_, v_x_2639_, v_x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2642_, lean_object* v_val_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(v_00_u03b2_2642_, v_val_2643_, v_x_2644_, v_x_2645_);
lean_dec_ref(v_x_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_object* v_00_u03b2_2647_, lean_object* v_00_u03c3_2648_, lean_object* v_00_u03b1_2649_, lean_object* v_ext_2650_, lean_object* v_x_2651_, size_t v_x_2652_, size_t v_x_2653_, lean_object* v_x_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2650_, v_x_2651_, v_x_2652_, v_x_2653_, v_x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2656_, lean_object* v_00_u03c3_2657_, lean_object* v_00_u03b1_2658_, lean_object* v_ext_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
size_t v_x_3047__boxed_2664_; size_t v_x_3048__boxed_2665_; lean_object* v_res_2666_; 
v_x_3047__boxed_2664_ = lean_unbox_usize(v_x_2661_);
lean_dec(v_x_2661_);
v_x_3048__boxed_2665_ = lean_unbox_usize(v_x_2662_);
lean_dec(v_x_2662_);
v_res_2666_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(v_00_u03b2_2656_, v_00_u03c3_2657_, v_00_u03b1_2658_, v_ext_2659_, v_x_2660_, v_x_3047__boxed_2664_, v_x_3048__boxed_2665_, v_x_2663_);
lean_dec_ref(v_x_2660_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_object* v_00_u03b2_2667_, lean_object* v_00_u03c3_2668_, lean_object* v_00_u03b1_2669_, lean_object* v_ext_2670_, lean_object* v_as_2671_, size_t v_i_2672_, size_t v_stop_2673_, lean_object* v_b_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2670_, v_as_2671_, v_i_2672_, v_stop_2673_, v_b_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2676_, lean_object* v_00_u03c3_2677_, lean_object* v_00_u03b1_2678_, lean_object* v_ext_2679_, lean_object* v_as_2680_, lean_object* v_i_2681_, lean_object* v_stop_2682_, lean_object* v_b_2683_){
_start:
{
size_t v_i_boxed_2684_; size_t v_stop_boxed_2685_; lean_object* v_res_2686_; 
v_i_boxed_2684_ = lean_unbox_usize(v_i_2681_);
lean_dec(v_i_2681_);
v_stop_boxed_2685_ = lean_unbox_usize(v_stop_2682_);
lean_dec(v_stop_2682_);
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(v_00_u03b2_2676_, v_00_u03c3_2677_, v_00_u03b1_2678_, v_ext_2679_, v_as_2680_, v_i_boxed_2684_, v_stop_boxed_2685_, v_b_2683_);
lean_dec_ref(v_as_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(lean_object* v_00_u03b2_2687_, lean_object* v_00_u03c3_2688_, lean_object* v_00_u03b1_2689_, lean_object* v_ext_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2690_, v_x_2691_, v_x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2694_, lean_object* v_00_u03c3_2695_, lean_object* v_00_u03b1_2696_, lean_object* v_ext_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(v_00_u03b2_2694_, v_00_u03c3_2695_, v_00_u03b1_2696_, v_ext_2697_, v_x_2698_, v_x_2699_);
lean_dec_ref(v_x_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2701_, lean_object* v_val_2702_, lean_object* v_as_2703_, size_t v_i_2704_, size_t v_stop_2705_, lean_object* v_b_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2702_, v_as_2703_, v_i_2704_, v_stop_2705_, v_b_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2708_, lean_object* v_val_2709_, lean_object* v_as_2710_, lean_object* v_i_2711_, lean_object* v_stop_2712_, lean_object* v_b_2713_){
_start:
{
size_t v_i_boxed_2714_; size_t v_stop_boxed_2715_; lean_object* v_res_2716_; 
v_i_boxed_2714_ = lean_unbox_usize(v_i_2711_);
lean_dec(v_i_2711_);
v_stop_boxed_2715_ = lean_unbox_usize(v_stop_2712_);
lean_dec(v_stop_2712_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2708_, v_val_2709_, v_as_2710_, v_i_boxed_2714_, v_stop_boxed_2715_, v_b_2713_);
lean_dec_ref(v_as_2710_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_2717_, lean_object* v_00_u03c3_2718_, lean_object* v_00_u03b1_2719_, lean_object* v_ext_2720_, lean_object* v_as_2721_, size_t v_i_2722_, size_t v_stop_2723_, lean_object* v_b_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2720_, v_as_2721_, v_i_2722_, v_stop_2723_, v_b_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2726_, lean_object* v_00_u03c3_2727_, lean_object* v_00_u03b1_2728_, lean_object* v_ext_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_stop_2732_, lean_object* v_b_2733_){
_start:
{
size_t v_i_boxed_2734_; size_t v_stop_boxed_2735_; lean_object* v_res_2736_; 
v_i_boxed_2734_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_stop_boxed_2735_ = lean_unbox_usize(v_stop_2732_);
lean_dec(v_stop_2732_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(v_00_u03b2_2726_, v_00_u03c3_2727_, v_00_u03b1_2728_, v_ext_2729_, v_as_2730_, v_i_boxed_2734_, v_stop_boxed_2735_, v_b_2733_);
lean_dec_ref(v_as_2730_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2737_, lean_object* v_descr_2738_, lean_object* v_ps_2739_){
_start:
{
lean_object* v_state_2740_; lean_object* v_stateStack_2741_; 
v_state_2740_ = lean_ctor_get(v_ps_2739_, 1);
lean_inc(v_state_2740_);
v_stateStack_2741_ = lean_ctor_get(v_state_2740_, 0);
lean_inc(v_stateStack_2741_);
if (lean_obj_tag(v_stateStack_2741_) == 1)
{
lean_object* v_head_2742_; lean_object* v_importedEntries_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2785_; 
v_head_2742_ = lean_ctor_get(v_stateStack_2741_, 0);
lean_inc(v_head_2742_);
v_importedEntries_2743_ = lean_ctor_get(v_ps_2739_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_ps_2739_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_ps_2739_, 1);
lean_dec(v_unused_2786_);
v___x_2745_ = v_ps_2739_;
v_isShared_2746_ = v_isSharedCheck_2785_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_importedEntries_2743_);
lean_dec(v_ps_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2785_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_scopedEntries_2747_; lean_object* v_newEntries_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2783_; 
v_scopedEntries_2747_ = lean_ctor_get(v_state_2740_, 1);
v_newEntries_2748_ = lean_ctor_get(v_state_2740_, 2);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_state_2740_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; 
v_unused_2784_ = lean_ctor_get(v_state_2740_, 0);
lean_dec(v_unused_2784_);
v___x_2750_ = v_state_2740_;
v_isShared_2751_ = v_isSharedCheck_2783_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_newEntries_2748_);
lean_inc(v_scopedEntries_2747_);
lean_dec(v_state_2740_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2783_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_tail_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2781_; 
v_tail_2752_ = lean_ctor_get(v_stateStack_2741_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_stateStack_2741_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v_stateStack_2741_, 0);
lean_dec(v_unused_2782_);
v___x_2754_ = v_stateStack_2741_;
v_isShared_2755_ = v_isSharedCheck_2781_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_tail_2752_);
lean_dec(v_stateStack_2741_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2781_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_state_2756_; lean_object* v_activeScopes_2757_; uint8_t v_delimitsLocal_2758_; uint8_t v_scopeChanged_2759_; lean_object* v_scopeChangedDecls_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2780_; 
v_state_2756_ = lean_ctor_get(v_head_2742_, 0);
v_activeScopes_2757_ = lean_ctor_get(v_head_2742_, 1);
v_delimitsLocal_2758_ = lean_ctor_get_uint8(v_head_2742_, sizeof(void*)*3);
v_scopeChanged_2759_ = lean_ctor_get_uint8(v_head_2742_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2760_ = lean_ctor_get(v_head_2742_, 2);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_head_2742_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2762_ = v_head_2742_;
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_scopeChangedDecls_2760_);
lean_inc(v_activeScopes_2757_);
lean_inc(v_state_2756_);
lean_dec(v_head_2742_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v___y_2765_; 
if (v_scopeChanged_2759_ == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_2738_);
v___y_2765_ = v___x_2779_;
goto v___jp_2764_;
}
else
{
v___y_2765_ = v_scopeChanged_2759_;
goto v___jp_2764_;
}
v___jp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_apply_1(v_f_2737_, v_state_2756_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2766_);
v___x_2768_ = v___x_2762_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_activeScopes_2757_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_scopeChangedDecls_2760_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, sizeof(void*)*3, v_delimitsLocal_2758_);
v___x_2768_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
lean_ctor_set_uint8(v___x_2768_, sizeof(void*)*3 + 1, v___y_2765_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2768_);
v___x_2770_ = v___x_2754_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_tail_2752_);
v___x_2770_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2770_);
v___x_2772_ = v___x_2750_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_scopedEntries_2747_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_newEntries_2748_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v___x_2772_);
v___x_2774_ = v___x_2745_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_importedEntries_2743_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
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
lean_object* v_importedEntries_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_stateStack_2741_);
lean_dec(v_f_2737_);
v_importedEntries_2787_ = lean_ctor_get(v_ps_2739_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_ps_2739_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; 
v_unused_2795_ = lean_ctor_get(v_ps_2739_, 1);
lean_dec(v_unused_2795_);
v___x_2789_ = v_ps_2739_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_importedEntries_2787_);
lean_dec(v_ps_2739_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_importedEntries_2787_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_state_2740_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object* v_f_2796_, lean_object* v_descr_2797_, lean_object* v_ps_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(v_f_2796_, v_descr_2797_, v_ps_2798_);
lean_dec_ref(v_descr_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2800_, lean_object* v_env_2801_, lean_object* v_f_2802_){
_start:
{
lean_object* v_ext_2803_; lean_object* v_toEnvExtension_2804_; lean_object* v_descr_2805_; lean_object* v_asyncMode_2806_; uint8_t v_logWrites_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_ext_2803_ = lean_ctor_get(v_ext_2800_, 1);
v_toEnvExtension_2804_ = lean_ctor_get(v_ext_2803_, 0);
lean_inc_ref(v_toEnvExtension_2804_);
v_descr_2805_ = lean_ctor_get(v_ext_2800_, 0);
lean_inc_ref(v_descr_2805_);
lean_dec_ref(v_ext_2800_);
v_asyncMode_2806_ = lean_ctor_get(v_toEnvExtension_2804_, 2);
lean_inc(v_asyncMode_2806_);
v_logWrites_2807_ = lean_ctor_get_uint8(v_toEnvExtension_2804_, sizeof(void*)*6);
v___f_2808_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2808_, 0, v_f_2802_);
lean_closure_set(v___f_2808_, 1, v_descr_2805_);
v___x_2809_ = lean_box(0);
v___x_2810_ = 1;
if (v_logWrites_2807_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2804_, v_env_2801_, v___f_2808_, v_asyncMode_2806_, v___x_2809_, v___x_2810_);
lean_dec(v_asyncMode_2806_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_inc_ref(v_toEnvExtension_2804_);
v___x_2812_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2804_, v_env_2801_);
lean_dec_ref(v_env_2801_);
v___x_2813_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2804_, v___x_2812_, v___f_2808_, v_asyncMode_2806_, v___x_2809_, v___x_2810_);
lean_dec(v_asyncMode_2806_);
return v___x_2813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2814_, lean_object* v_00_u03b2_2815_, lean_object* v_00_u03c3_2816_, lean_object* v_ext_2817_, lean_object* v_env_2818_, lean_object* v_f_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2817_, v_env_2818_, v_f_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2821_, lean_object* v_____s_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_apply_2(v_toPure_2821_, lean_box(0), v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2825_, lean_object* v_toPure_2826_, lean_object* v_r_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2825_);
v___x_2829_ = lean_apply_2(v_toPure_2826_, lean_box(0), v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2830_, lean_object* v_toBind_2831_, lean_object* v___f_2832_, lean_object* v_a_2833_, lean_object* v_x_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_modifyEnv_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_modifyEnv_2836_ = lean_ctor_get(v_inst_2830_, 1);
lean_inc(v_modifyEnv_2836_);
lean_dec_ref(v_inst_2830_);
v___x_2837_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2837_, 0, lean_box(0));
lean_closure_set(v___x_2837_, 1, lean_box(0));
lean_closure_set(v___x_2837_, 2, lean_box(0));
lean_closure_set(v___x_2837_, 3, v_a_2833_);
v___x_2838_ = lean_apply_1(v_modifyEnv_2836_, v___x_2837_);
v___x_2839_ = lean_apply_4(v_toBind_2831_, lean_box(0), lean_box(0), v___x_2838_, v___f_2832_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2840_, lean_object* v_inst_2841_, lean_object* v_toBind_2842_, lean_object* v_inst_2843_, lean_object* v___f_2844_, lean_object* v_____do__lift_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; size_t v_sz_2849_; size_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2846_ = lean_box(0);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2847_, 0, v___x_2846_);
lean_closure_set(v___f_2847_, 1, v_toPure_2840_);
lean_inc(v_toBind_2842_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2848_, 0, v_inst_2841_);
lean_closure_set(v___f_2848_, 1, v_toBind_2842_);
lean_closure_set(v___f_2848_, 2, v___f_2847_);
v_sz_2849_ = lean_array_size(v_____do__lift_2845_);
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2843_, v_____do__lift_2845_, v___f_2848_, v_sz_2849_, v___x_2850_, v___x_2846_);
v___x_2852_ = lean_apply_4(v_toBind_2842_, lean_box(0), lean_box(0), v___x_2851_, v___f_2844_);
return v___x_2852_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = l_Lean_scopedEnvExtensionsRef;
v___x_2854_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2854_, 0, lean_box(0));
lean_closure_set(v___x_2854_, 1, lean_box(0));
lean_closure_set(v___x_2854_, 2, v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_){
_start:
{
lean_object* v_toApplicative_2858_; lean_object* v_toBind_2859_; lean_object* v_toPure_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___f_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; 
v_toApplicative_2858_ = lean_ctor_get(v_inst_2855_, 0);
v_toBind_2859_ = lean_ctor_get(v_inst_2855_, 1);
lean_inc_n(v_toBind_2859_, 2);
v_toPure_2860_ = lean_ctor_get(v_toApplicative_2858_, 1);
lean_inc_n(v_toPure_2860_, 2);
v___x_2861_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2862_ = lean_apply_2(v_inst_2857_, lean_box(0), v___x_2861_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2863_, 0, v_toPure_2860_);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2864_, 0, v_toPure_2860_);
lean_closure_set(v___f_2864_, 1, v_inst_2856_);
lean_closure_set(v___f_2864_, 2, v_toBind_2859_);
lean_closure_set(v___f_2864_, 3, v_inst_2855_);
lean_closure_set(v___f_2864_, 4, v___f_2863_);
v___x_2865_ = lean_apply_4(v_toBind_2859_, lean_box(0), lean_box(0), v___x_2862_, v___f_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_pushScope___redArg(v_inst_2867_, v_inst_2868_, v_inst_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2871_, lean_object* v_toBind_2872_, lean_object* v___f_2873_, lean_object* v_a_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_modifyEnv_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_modifyEnv_2877_ = lean_ctor_get(v_inst_2871_, 1);
lean_inc(v_modifyEnv_2877_);
lean_dec_ref(v_inst_2871_);
v___x_2878_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2878_, 0, lean_box(0));
lean_closure_set(v___x_2878_, 1, lean_box(0));
lean_closure_set(v___x_2878_, 2, lean_box(0));
lean_closure_set(v___x_2878_, 3, v_a_2874_);
v___x_2879_ = lean_apply_1(v_modifyEnv_2877_, v___x_2878_);
v___x_2880_ = lean_apply_4(v_toBind_2872_, lean_box(0), lean_box(0), v___x_2879_, v___f_2873_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2881_, lean_object* v_inst_2882_, lean_object* v_toBind_2883_, lean_object* v_inst_2884_, lean_object* v___f_2885_, lean_object* v_____do__lift_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___f_2889_; size_t v_sz_2890_; size_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2887_ = lean_box(0);
v___f_2888_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2888_, 0, v___x_2887_);
lean_closure_set(v___f_2888_, 1, v_toPure_2881_);
lean_inc(v_toBind_2883_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2889_, 0, v_inst_2882_);
lean_closure_set(v___f_2889_, 1, v_toBind_2883_);
lean_closure_set(v___f_2889_, 2, v___f_2888_);
v_sz_2890_ = lean_array_size(v_____do__lift_2886_);
v___x_2891_ = ((size_t)0ULL);
v___x_2892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2884_, v_____do__lift_2886_, v___f_2889_, v_sz_2890_, v___x_2891_, v___x_2887_);
v___x_2893_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2892_, v___f_2885_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_){
_start:
{
lean_object* v_toApplicative_2897_; lean_object* v_toBind_2898_; lean_object* v_toPure_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___f_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; 
v_toApplicative_2897_ = lean_ctor_get(v_inst_2894_, 0);
v_toBind_2898_ = lean_ctor_get(v_inst_2894_, 1);
lean_inc_n(v_toBind_2898_, 2);
v_toPure_2899_ = lean_ctor_get(v_toApplicative_2897_, 1);
lean_inc_n(v_toPure_2899_, 2);
v___x_2900_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2901_ = lean_apply_2(v_inst_2896_, lean_box(0), v___x_2900_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2902_, 0, v_toPure_2899_);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2903_, 0, v_toPure_2899_);
lean_closure_set(v___f_2903_, 1, v_inst_2895_);
lean_closure_set(v___f_2903_, 2, v_toBind_2898_);
lean_closure_set(v___f_2903_, 3, v_inst_2894_);
lean_closure_set(v___f_2903_, 4, v___f_2902_);
v___x_2904_ = lean_apply_4(v_toBind_2898_, lean_box(0), lean_box(0), v___x_2901_, v___f_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_popScope___redArg(v_inst_2906_, v_inst_2907_, v_inst_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_2910_, lean_object* v_depth_2911_, lean_object* v_x_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_2910_, v_x_2912_, v_depth_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_2914_, lean_object* v_depth_2915_, lean_object* v_toBind_2916_, lean_object* v___f_2917_, lean_object* v_a_2918_, lean_object* v_x_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_modifyEnv_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_modifyEnv_2921_ = lean_ctor_get(v_inst_2914_, 1);
lean_inc(v_modifyEnv_2921_);
lean_dec_ref(v_inst_2914_);
v___f_2922_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2922_, 0, v_a_2918_);
lean_closure_set(v___f_2922_, 1, v_depth_2915_);
v___x_2923_ = lean_apply_1(v_modifyEnv_2921_, v___f_2922_);
v___x_2924_ = lean_apply_4(v_toBind_2916_, lean_box(0), lean_box(0), v___x_2923_, v___f_2917_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_2925_, lean_object* v_inst_2926_, lean_object* v_depth_2927_, lean_object* v_toBind_2928_, lean_object* v_inst_2929_, lean_object* v___f_2930_, lean_object* v_____do__lift_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___f_2933_; lean_object* v___f_2934_; size_t v_sz_2935_; size_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2932_ = lean_box(0);
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2933_, 0, v___x_2932_);
lean_closure_set(v___f_2933_, 1, v_toPure_2925_);
lean_inc(v_toBind_2928_);
v___f_2934_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2934_, 0, v_inst_2926_);
lean_closure_set(v___f_2934_, 1, v_depth_2927_);
lean_closure_set(v___f_2934_, 2, v_toBind_2928_);
lean_closure_set(v___f_2934_, 3, v___f_2933_);
v_sz_2935_ = lean_array_size(v_____do__lift_2931_);
v___x_2936_ = ((size_t)0ULL);
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2929_, v_____do__lift_2931_, v___f_2934_, v_sz_2935_, v___x_2936_, v___x_2932_);
v___x_2938_ = lean_apply_4(v_toBind_2928_, lean_box(0), lean_box(0), v___x_2937_, v___f_2930_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_depth_2942_){
_start:
{
lean_object* v_toApplicative_2943_; lean_object* v_toBind_2944_; lean_object* v_toPure_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; 
v_toApplicative_2943_ = lean_ctor_get(v_inst_2939_, 0);
v_toBind_2944_ = lean_ctor_get(v_inst_2939_, 1);
lean_inc_n(v_toBind_2944_, 2);
v_toPure_2945_ = lean_ctor_get(v_toApplicative_2943_, 1);
lean_inc_n(v_toPure_2945_, 2);
v___x_2946_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2947_ = lean_apply_2(v_inst_2941_, lean_box(0), v___x_2946_);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2948_, 0, v_toPure_2945_);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2949_, 0, v_toPure_2945_);
lean_closure_set(v___f_2949_, 1, v_inst_2940_);
lean_closure_set(v___f_2949_, 2, v_depth_2942_);
lean_closure_set(v___f_2949_, 3, v_toBind_2944_);
lean_closure_set(v___f_2949_, 4, v_inst_2939_);
lean_closure_set(v___f_2949_, 5, v___f_2948_);
v___x_2950_ = lean_apply_4(v_toBind_2944_, lean_box(0), lean_box(0), v___x_2947_, v___f_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_depth_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_setDelimitsLocal___redArg(v_inst_2952_, v_inst_2953_, v_inst_2954_, v_depth_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_2957_, lean_object* v_namespaceName_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_2957_, v_x_2959_, v_namespaceName_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_2961_, lean_object* v_namespaceName_2962_, lean_object* v_toBind_2963_, lean_object* v___f_2964_, lean_object* v_a_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_modifyEnv_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_modifyEnv_2968_ = lean_ctor_get(v_inst_2961_, 1);
lean_inc(v_modifyEnv_2968_);
lean_dec_ref(v_inst_2961_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2969_, 0, v_a_2965_);
lean_closure_set(v___f_2969_, 1, v_namespaceName_2962_);
v___x_2970_ = lean_apply_1(v_modifyEnv_2968_, v___f_2969_);
v___x_2971_ = lean_apply_4(v_toBind_2963_, lean_box(0), lean_box(0), v___x_2970_, v___f_2964_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_2972_, lean_object* v_inst_2973_, lean_object* v_namespaceName_2974_, lean_object* v_toBind_2975_, lean_object* v_inst_2976_, lean_object* v___f_2977_, lean_object* v_____do__lift_2978_){
_start:
{
lean_object* v___x_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; size_t v_sz_2982_; size_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2979_ = lean_box(0);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2980_, 0, v___x_2979_);
lean_closure_set(v___f_2980_, 1, v_toPure_2972_);
lean_inc(v_toBind_2975_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2981_, 0, v_inst_2973_);
lean_closure_set(v___f_2981_, 1, v_namespaceName_2974_);
lean_closure_set(v___f_2981_, 2, v_toBind_2975_);
lean_closure_set(v___f_2981_, 3, v___f_2980_);
v_sz_2982_ = lean_array_size(v_____do__lift_2978_);
v___x_2983_ = ((size_t)0ULL);
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2976_, v_____do__lift_2978_, v___f_2981_, v_sz_2982_, v___x_2983_, v___x_2979_);
v___x_2985_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v___x_2984_, v___f_2977_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_namespaceName_2989_){
_start:
{
lean_object* v_toApplicative_2990_; lean_object* v_toBind_2991_; lean_object* v_toPure_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___f_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; 
v_toApplicative_2990_ = lean_ctor_get(v_inst_2986_, 0);
v_toBind_2991_ = lean_ctor_get(v_inst_2986_, 1);
lean_inc_n(v_toBind_2991_, 2);
v_toPure_2992_ = lean_ctor_get(v_toApplicative_2990_, 1);
lean_inc_n(v_toPure_2992_, 2);
v___x_2993_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2994_ = lean_apply_2(v_inst_2988_, lean_box(0), v___x_2993_);
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2995_, 0, v_toPure_2992_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2996_, 0, v_toPure_2992_);
lean_closure_set(v___f_2996_, 1, v_inst_2987_);
lean_closure_set(v___f_2996_, 2, v_namespaceName_2989_);
lean_closure_set(v___f_2996_, 3, v_toBind_2991_);
lean_closure_set(v___f_2996_, 4, v_inst_2986_);
lean_closure_set(v___f_2996_, 5, v___f_2995_);
v___x_2997_ = lean_apply_4(v_toBind_2991_, lean_box(0), lean_box(0), v___x_2994_, v___f_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_namespaceName_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_activateScoped___redArg(v_inst_2999_, v_inst_3000_, v_inst_3001_, v_namespaceName_3002_);
return v___x_3003_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_3005_){
_start:
{
lean_inc(v___y_3005_);
return v___y_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_3006_);
lean_dec(v___y_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_3008_, lean_object* v_a_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_a_3009_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_3013_, lean_object* v_a_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_3013_, v_a_3014_, v___y_3015_);
lean_dec_ref(v___y_3015_);
lean_dec(v_x_3013_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_initial_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_3026_){
_start:
{
lean_object* v_name_3028_; lean_object* v_addEntry_3029_; lean_object* v_initial_3030_; lean_object* v_finalizeImport_3031_; lean_object* v_exportEntry_x3f_3032_; uint8_t v_trackGen_3033_; uint8_t v_logWrites_3034_; lean_object* v_entryDecl_x3f_3035_; lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_name_3028_ = lean_ctor_get(v_descr_3026_, 0);
lean_inc(v_name_3028_);
v_addEntry_3029_ = lean_ctor_get(v_descr_3026_, 1);
lean_inc(v_addEntry_3029_);
v_initial_3030_ = lean_ctor_get(v_descr_3026_, 2);
lean_inc(v_initial_3030_);
v_finalizeImport_3031_ = lean_ctor_get(v_descr_3026_, 3);
lean_inc(v_finalizeImport_3031_);
v_exportEntry_x3f_3032_ = lean_ctor_get(v_descr_3026_, 4);
lean_inc_ref(v_exportEntry_x3f_3032_);
v_trackGen_3033_ = lean_ctor_get_uint8(v_descr_3026_, sizeof(void*)*6);
v_logWrites_3034_ = lean_ctor_get_uint8(v_descr_3026_, sizeof(void*)*6 + 1);
v_entryDecl_x3f_3035_ = lean_ctor_get(v_descr_3026_, 5);
lean_inc(v_entryDecl_x3f_3035_);
lean_dec_ref(v_descr_3026_);
v___f_3036_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_3037_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3038_, 0, v_initial_3030_);
v___x_3039_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3039_, 0, v_name_3028_);
lean_ctor_set(v___x_3039_, 1, v___f_3038_);
lean_ctor_set(v___x_3039_, 2, v___f_3037_);
lean_ctor_set(v___x_3039_, 3, v___f_3036_);
lean_ctor_set(v___x_3039_, 4, v_addEntry_3029_);
lean_ctor_set(v___x_3039_, 5, v_finalizeImport_3031_);
lean_ctor_set(v___x_3039_, 6, v_exportEntry_x3f_3032_);
lean_ctor_set(v___x_3039_, 7, v_entryDecl_x3f_3035_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*8, v_trackGen_3033_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*8 + 1, v_logWrites_3034_);
v___x_3040_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_3044_, lean_object* v_00_u03c3_3045_, lean_object* v_descr_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_00_u03c3_3050_, lean_object* v_descr_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_3049_, v_00_u03c3_3050_, v_descr_3051_);
return v_res_3053_;
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
