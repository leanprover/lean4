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
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__1(lean_object*);
static const lean_array_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "summary extension '"};
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' is not registered"};
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__0 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__1 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__2 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__2_value;
static const lean_string_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "moduleSummary"};
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__3 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__3_value;
static const lean_ctor_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(42, 176, 44, 157, 196, 215, 125, 231)}};
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__4 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__5 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__6 = (const lean_object*)&l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg(lean_object* v_ofOLeanEntry_96_, lean_object* v_addImportedEntry_97_, lean_object* v_as_98_, size_t v_sz_99_, size_t v_i_100_, lean_object* v_b_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_a_105_; uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_lt(v_i_100_, v_sz_99_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec(v_addImportedEntry_97_);
lean_dec_ref(v_ofOLeanEntry_96_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v_b_101_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; 
v_a_111_ = lean_array_uget_borrowed(v_as_98_, v_i_100_);
if (lean_obj_tag(v_a_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v_a_111_, 0);
lean_inc_ref(v_ofOLeanEntry_96_);
lean_inc_ref(v___y_102_);
lean_inc(v_a_112_);
lean_inc(v_b_101_);
v___x_113_ = lean_apply_4(v_ofOLeanEntry_96_, v_b_101_, v_a_112_, v___y_102_, lean_box(0));
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
lean_inc(v_addImportedEntry_97_);
v___x_115_ = lean_apply_2(v_addImportedEntry_97_, v_b_101_, v_a_114_);
v_a_105_ = v___x_115_;
goto v___jp_104_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_b_101_);
lean_dec(v_addImportedEntry_97_);
lean_dec_ref(v_ofOLeanEntry_96_);
v_a_116_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_113_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
v_a_105_ = v_b_101_;
goto v___jp_104_;
}
}
v___jp_104_:
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_100_, v___x_106_);
v_i_100_ = v___x_107_;
v_b_101_ = v_a_105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg___boxed(lean_object* v_ofOLeanEntry_124_, lean_object* v_addImportedEntry_125_, lean_object* v_as_126_, lean_object* v_sz_127_, lean_object* v_i_128_, lean_object* v_b_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
size_t v_sz_boxed_132_; size_t v_i_boxed_133_; lean_object* v_res_134_; 
v_sz_boxed_132_ = lean_unbox_usize(v_sz_127_);
lean_dec(v_sz_127_);
v_i_boxed_133_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg(v_ofOLeanEntry_124_, v_addImportedEntry_125_, v_as_126_, v_sz_boxed_132_, v_i_boxed_133_, v_b_129_, v___y_130_);
lean_dec_ref(v___y_130_);
lean_dec_ref(v_as_126_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg(lean_object* v_ofOLeanEntry_135_, lean_object* v_addImportedEntry_136_, lean_object* v_as_137_, size_t v_sz_138_, size_t v_i_139_, lean_object* v_b_140_, lean_object* v___y_141_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
lean_dec(v_addImportedEntry_136_);
lean_dec_ref(v_ofOLeanEntry_135_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v_b_140_);
return v___x_144_;
}
else
{
lean_object* v_a_145_; size_t v_sz_146_; size_t v___x_147_; lean_object* v___x_148_; 
v_a_145_ = lean_array_uget_borrowed(v_as_137_, v_i_139_);
v_sz_146_ = lean_array_size(v_a_145_);
v___x_147_ = ((size_t)0ULL);
lean_inc(v_addImportedEntry_136_);
lean_inc_ref(v_ofOLeanEntry_135_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg(v_ofOLeanEntry_135_, v_addImportedEntry_136_, v_a_145_, v_sz_146_, v___x_147_, v_b_140_, v___y_141_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; size_t v___x_150_; size_t v___x_151_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_139_, v___x_150_);
v_i_139_ = v___x_151_;
v_b_140_ = v_a_149_;
goto _start;
}
else
{
lean_dec(v_addImportedEntry_136_);
lean_dec_ref(v_ofOLeanEntry_135_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg___boxed(lean_object* v_ofOLeanEntry_153_, lean_object* v_addImportedEntry_154_, lean_object* v_as_155_, lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_b_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
size_t v_sz_boxed_161_; size_t v_i_boxed_162_; lean_object* v_res_163_; 
v_sz_boxed_161_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_162_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg(v_ofOLeanEntry_153_, v_addImportedEntry_154_, v_as_155_, v_sz_boxed_161_, v_i_boxed_162_, v_b_158_, v___y_159_);
lean_dec_ref(v___y_159_);
lean_dec_ref(v_as_155_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___redArg(lean_object* v_mkInitial_164_, lean_object* v_ofOLeanEntry_165_, lean_object* v_addImportedEntry_166_, lean_object* v_as_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_1(v_mkInitial_164_, lean_box(0));
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; size_t v_sz_172_; size_t v___x_173_; lean_object* v___x_174_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
v_sz_172_ = lean_array_size(v_as_167_);
v___x_173_ = ((size_t)0ULL);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg(v_ofOLeanEntry_165_, v_addImportedEntry_166_, v_as_167_, v_sz_172_, v___x_173_, v_a_171_, v_a_168_);
return v___x_174_;
}
else
{
lean_dec(v_addImportedEntry_166_);
lean_dec_ref(v_ofOLeanEntry_165_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___redArg___boxed(lean_object* v_mkInitial_175_, lean_object* v_ofOLeanEntry_176_, lean_object* v_addImportedEntry_177_, lean_object* v_as_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_ScopedEnvExtension_addImportedGlobals___redArg(v_mkInitial_175_, v_ofOLeanEntry_176_, v_addImportedEntry_177_, v_as_178_, v_a_179_);
lean_dec_ref(v_a_179_);
lean_dec_ref(v_as_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals(lean_object* v_00_u03c3_182_, lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_mkInitial_185_, lean_object* v_ofOLeanEntry_186_, lean_object* v_addImportedEntry_187_, lean_object* v_as_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_ScopedEnvExtension_addImportedGlobals___redArg(v_mkInitial_185_, v_ofOLeanEntry_186_, v_addImportedEntry_187_, v_as_188_, v_a_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object* v_00_u03c3_192_, lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_mkInitial_195_, lean_object* v_ofOLeanEntry_196_, lean_object* v_addImportedEntry_197_, lean_object* v_as_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_ScopedEnvExtension_addImportedGlobals(v_00_u03c3_192_, v_00_u03b1_193_, v_00_u03b2_194_, v_mkInitial_195_, v_ofOLeanEntry_196_, v_addImportedEntry_197_, v_as_198_, v_a_199_);
lean_dec_ref(v_a_199_);
lean_dec_ref(v_as_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0(lean_object* v_00_u03b1_202_, lean_object* v_00_u03c3_203_, lean_object* v_00_u03b2_204_, lean_object* v_ofOLeanEntry_205_, lean_object* v_addImportedEntry_206_, lean_object* v_as_207_, size_t v_sz_208_, size_t v_i_209_, lean_object* v_b_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___redArg(v_ofOLeanEntry_205_, v_addImportedEntry_206_, v_as_207_, v_sz_208_, v_i_209_, v_b_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0___boxed(lean_object* v_00_u03b1_214_, lean_object* v_00_u03c3_215_, lean_object* v_00_u03b2_216_, lean_object* v_ofOLeanEntry_217_, lean_object* v_addImportedEntry_218_, lean_object* v_as_219_, lean_object* v_sz_220_, lean_object* v_i_221_, lean_object* v_b_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
size_t v_sz_boxed_225_; size_t v_i_boxed_226_; lean_object* v_res_227_; 
v_sz_boxed_225_ = lean_unbox_usize(v_sz_220_);
lean_dec(v_sz_220_);
v_i_boxed_226_ = lean_unbox_usize(v_i_221_);
lean_dec(v_i_221_);
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__0(v_00_u03b1_214_, v_00_u03c3_215_, v_00_u03b2_216_, v_ofOLeanEntry_217_, v_addImportedEntry_218_, v_as_219_, v_sz_boxed_225_, v_i_boxed_226_, v_b_222_, v___y_223_);
lean_dec_ref(v___y_223_);
lean_dec_ref(v_as_219_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1(lean_object* v_00_u03b1_228_, lean_object* v_00_u03c3_229_, lean_object* v_00_u03b2_230_, lean_object* v_ofOLeanEntry_231_, lean_object* v_addImportedEntry_232_, lean_object* v_as_233_, size_t v_sz_234_, size_t v_i_235_, lean_object* v_b_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___redArg(v_ofOLeanEntry_231_, v_addImportedEntry_232_, v_as_233_, v_sz_234_, v_i_235_, v_b_236_, v___y_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1___boxed(lean_object* v_00_u03b1_240_, lean_object* v_00_u03c3_241_, lean_object* v_00_u03b2_242_, lean_object* v_ofOLeanEntry_243_, lean_object* v_addImportedEntry_244_, lean_object* v_as_245_, lean_object* v_sz_246_, lean_object* v_i_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
size_t v_sz_boxed_251_; size_t v_i_boxed_252_; lean_object* v_res_253_; 
v_sz_boxed_251_ = lean_unbox_usize(v_sz_246_);
lean_dec(v_sz_246_);
v_i_boxed_252_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedGlobals_spec__1(v_00_u03b1_240_, v_00_u03c3_241_, v_00_u03b2_242_, v_ofOLeanEntry_243_, v_addImportedEntry_244_, v_as_245_, v_sz_boxed_251_, v_i_boxed_252_, v_b_248_, v___y_249_);
lean_dec_ref(v___y_249_);
lean_dec_ref(v_as_245_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10));
v___x_281_ = l_Lean_mkAtom(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12);
v___x_283_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17));
v___x_294_ = l_Lean_mkAtom(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18);
v___x_296_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_297_ = lean_array_push(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19);
v___x_299_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16));
v___x_300_ = lean_box(2);
v___x_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
lean_ctor_set(v___x_301_, 2, v___x_298_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20);
v___x_303_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13);
v___x_304_ = lean_array_push(v___x_303_, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21);
v___x_306_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11));
v___x_307_ = lean_box(2);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_305_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22);
v___x_310_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_311_ = lean_array_push(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23);
v___x_313_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9));
v___x_314_ = lean_box(2);
v___x_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24);
v___x_317_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_318_ = lean_array_push(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25);
v___x_320_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7));
v___x_321_ = lean_box(2);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26);
v___x_324_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5));
v___x_325_ = lean_array_push(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27);
v___x_327_ = ((lean_object*)(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4));
v___x_328_ = lean_box(2);
v___x_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_326_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_330_;
}
}
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(lean_object* v_descr_331_){
_start:
{
uint8_t v_trackGen_332_; 
v_trackGen_332_ = lean_ctor_get_uint8(v_descr_331_, sizeof(void*)*10);
if (v_trackGen_332_ == 0)
{
uint8_t v_logWrites_333_; 
v_logWrites_333_ = lean_ctor_get_uint8(v_descr_331_, sizeof(void*)*10 + 1);
return v_logWrites_333_;
}
else
{
return v_trackGen_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg___boxed(lean_object* v_descr_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_334_);
lean_dec_ref(v_descr_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Lean_ScopedEnvExtension_Descr_tracksScopes(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_00_u03c3_339_, lean_object* v_descr_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_tracksScopes___boxed(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_00_u03c3_344_, lean_object* v_descr_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes(v_00_u03b1_342_, v_00_u03b2_343_, v_00_u03c3_344_, v_descr_345_);
lean_dec_ref(v_descr_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(lean_object* v_descr_348_, lean_object* v_s_349_, lean_object* v_b_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_348_);
if (v___x_351_ == 0)
{
lean_dec(v_b_350_);
lean_dec_ref(v_descr_348_);
return v_s_349_;
}
else
{
lean_object* v_entryDecl_x3f_352_; 
v_entryDecl_x3f_352_ = lean_ctor_get(v_descr_348_, 8);
lean_inc(v_entryDecl_x3f_352_);
lean_dec_ref(v_descr_348_);
if (lean_obj_tag(v_entryDecl_x3f_352_) == 0)
{
lean_object* v_state_353_; lean_object* v_activeScopes_354_; uint8_t v_delimitsLocal_355_; lean_object* v_scopeChangedDecls_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_b_350_);
v_state_353_ = lean_ctor_get(v_s_349_, 0);
v_activeScopes_354_ = lean_ctor_get(v_s_349_, 1);
v_delimitsLocal_355_ = lean_ctor_get_uint8(v_s_349_, sizeof(void*)*3);
v_scopeChangedDecls_356_ = lean_ctor_get(v_s_349_, 2);
v_isSharedCheck_363_ = !lean_is_exclusive(v_s_349_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v_s_349_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_scopeChangedDecls_356_);
lean_inc(v_activeScopes_354_);
lean_inc(v_state_353_);
lean_dec(v_s_349_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_state_353_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_activeScopes_354_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_scopeChangedDecls_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*3, v_delimitsLocal_355_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*3 + 1, v___x_351_);
return v___x_361_;
}
}
}
else
{
lean_object* v_state_364_; lean_object* v_activeScopes_365_; uint8_t v_delimitsLocal_366_; lean_object* v_scopeChangedDecls_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_state_364_ = lean_ctor_get(v_s_349_, 0);
v_activeScopes_365_ = lean_ctor_get(v_s_349_, 1);
v_delimitsLocal_366_ = lean_ctor_get_uint8(v_s_349_, sizeof(void*)*3);
v_scopeChangedDecls_367_ = lean_ctor_get(v_s_349_, 2);
v_isSharedCheck_377_ = !lean_is_exclusive(v_s_349_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v_s_349_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_scopeChangedDecls_367_);
lean_inc(v_activeScopes_365_);
lean_inc(v_state_364_);
lean_dec(v_s_349_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_val_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v_val_371_ = lean_ctor_get(v_entryDecl_x3f_352_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v_entryDecl_x3f_352_, 1);
v___x_372_ = lean_apply_1(v_val_371_, v_b_350_);
v___x_373_ = lean_array_push(v_scopeChangedDecls_367_, v___x_372_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_373_);
v___x_375_ = v___x_369_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_state_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_activeScopes_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_376_, sizeof(void*)*3, v_delimitsLocal_366_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*3 + 1, v___x_351_);
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_Descr_noteScopeChange(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_00_u03c3_380_, lean_object* v_descr_381_, lean_object* v_s_382_, lean_object* v_b_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_381_, v_s_382_, v_b_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(v_x_394_, v___y_395_, v___y_396_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v_x_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(lean_object* v_inst_399_, lean_object* v_x_400_){
_start:
{
lean_inc(v_inst_399_);
return v_inst_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(lean_object* v_inst_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_401_, v_x_402_);
lean_dec(v_x_402_);
lean_dec(v_inst_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(lean_object* v_s_404_, lean_object* v_x_405_){
_start:
{
lean_inc(v_s_404_);
return v_s_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(lean_object* v_s_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_406_, v_x_407_);
lean_dec(v_x_407_);
lean_dec(v_s_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(lean_object* v_x_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_a_410_);
lean_inc_ref_n(v___x_411_, 2);
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(lean_object* v_x_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_413_, v_a_414_);
lean_dec_ref(v_x_413_);
return v_res_415_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_instInhabitedError;
v___x_420_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, lean_box(0));
lean_closure_set(v___x_420_, 2, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5(void){
_start:
{
lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___f_422_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_423_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___x_424_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_425_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_425_, 0, lean_box(0));
lean_closure_set(v___x_425_, 1, lean_box(0));
lean_closure_set(v___x_425_, 2, lean_box(0));
lean_closure_set(v___x_425_, 3, v___x_424_);
lean_closure_set(v___x_425_, 4, v___f_423_);
lean_closure_set(v___x_425_, 5, v___f_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(lean_object* v_inst_426_){
_start:
{
lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___f_427_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_428_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_428_, 0, v_inst_426_);
v___f_429_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_430_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_431_ = lean_box(0);
v___x_432_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_433_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_434_ = 0;
v___x_435_ = lean_box(0);
v___x_436_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5);
v___x_437_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_437_, 0, v___x_431_);
lean_ctor_set(v___x_437_, 1, v___x_432_);
lean_ctor_set(v___x_437_, 2, v___f_427_);
lean_ctor_set(v___x_437_, 3, v___f_428_);
lean_ctor_set(v___x_437_, 4, v___f_429_);
lean_ctor_set(v___x_437_, 5, v___f_429_);
lean_ctor_set(v___x_437_, 6, v___x_433_);
lean_ctor_set(v___x_437_, 7, v___f_430_);
lean_ctor_set(v___x_437_, 8, v___x_435_);
lean_ctor_set(v___x_437_, 9, v___x_436_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*10, v___x_434_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*10 + 1, v___x_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_00_u03c3_440_, lean_object* v_inst_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg(lean_object* v_descr_445_){
_start:
{
lean_object* v_mkInitial_447_; lean_object* v___x_448_; 
v_mkInitial_447_ = lean_ctor_get(v_descr_445_, 1);
lean_inc_ref(v_mkInitial_447_);
lean_dec_ref(v_descr_445_);
v___x_448_ = lean_apply_1(v_mkInitial_447_, lean_box(0));
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_465_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_453_ = l_Lean_NameSet_empty;
v___x_454_ = 1;
v___x_455_ = 0;
v___x_456_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_457_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_457_, 0, v_a_449_);
lean_ctor_set(v___x_457_, 1, v___x_453_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 1, v___x_455_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v___x_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_ctor_set(v___x_461_, 2, v___x_458_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_461_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_a_466_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_448_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_448_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(lean_object* v_descr_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_00_u03c3_479_, lean_object* v_descr_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_mkInitial___boxed(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_00_u03c3_485_, lean_object* v_descr_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_ScopedEnvExtension_mkInitial(v_00_u03b1_483_, v_00_u03b2_484_, v_00_u03c3_485_, v_descr_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(lean_object* v_a_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_key_492_; lean_object* v_value_493_; lean_object* v_tail_494_; uint8_t v___x_495_; 
v_key_492_ = lean_ctor_get(v_x_490_, 0);
v_value_493_ = lean_ctor_get(v_x_490_, 1);
v_tail_494_ = lean_ctor_get(v_x_490_, 2);
v___x_495_ = lean_name_eq(v_key_492_, v_a_489_);
if (v___x_495_ == 0)
{
v_x_490_ = v_tail_494_;
goto _start;
}
else
{
lean_object* v___x_497_; 
lean_inc(v_value_493_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_value_493_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec(v_a_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_buckets_503_; lean_object* v___x_504_; uint64_t v___y_506_; 
v_buckets_503_ = lean_ctor_get(v_m_501_, 1);
v___x_504_ = lean_array_get_size(v_buckets_503_);
if (lean_obj_tag(v_a_502_) == 0)
{
uint64_t v___x_520_; 
v___x_520_ = 1723ULL;
v___y_506_ = v___x_520_;
goto v___jp_505_;
}
else
{
uint64_t v_hash_521_; 
v_hash_521_ = lean_ctor_get_uint64(v_a_502_, sizeof(void*)*2);
v___y_506_ = v_hash_521_;
goto v___jp_505_;
}
v___jp_505_:
{
uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v_fold_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_507_ = 32ULL;
v___x_508_ = lean_uint64_shift_right(v___y_506_, v___x_507_);
v_fold_509_ = lean_uint64_xor(v___y_506_, v___x_508_);
v___x_510_ = 16ULL;
v___x_511_ = lean_uint64_shift_right(v_fold_509_, v___x_510_);
v___x_512_ = lean_uint64_xor(v_fold_509_, v___x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = lean_usize_of_nat(v___x_504_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_sub(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_land(v___x_513_, v___x_516_);
v___x_518_ = lean_array_uget_borrowed(v_buckets_503_, v___x_517_);
v___x_519_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_502_, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_m_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_get_size(v_keys_525_);
v___x_530_ = lean_nat_dec_lt(v_i_527_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec(v_i_527_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v_k_x27_532_; uint8_t v___x_533_; 
v_k_x27_532_ = lean_array_fget_borrowed(v_keys_525_, v_i_527_);
v___x_533_ = lean_name_eq(v_k_528_, v_k_x27_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_i_527_, v___x_534_);
lean_dec(v_i_527_);
v_i_527_ = v___x_535_;
goto _start;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget_borrowed(v_vals_526_, v_i_527_);
lean_dec(v_i_527_);
lean_inc(v___x_537_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_539_, lean_object* v_vals_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_539_, v_vals_540_, v_i_541_, v_k_542_);
lean_dec(v_k_542_);
lean_dec_ref(v_vals_540_);
lean_dec_ref(v_keys_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_x_544_, size_t v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v___x_552_; 
v_es_547_ = lean_ctor_get(v_x_544_, 0);
v___x_548_ = lean_box(2);
v___x_549_ = ((size_t)31ULL);
v___x_550_ = lean_usize_land(v_x_545_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v___x_552_ = lean_array_get_borrowed(v___x_548_, v_es_547_, v_j_551_);
lean_dec(v_j_551_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; uint8_t v___x_555_; 
v_key_553_ = lean_ctor_get(v___x_552_, 0);
v_val_554_ = lean_ctor_get(v___x_552_, 1);
v___x_555_ = lean_name_eq(v_x_546_, v_key_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
lean_inc(v_val_554_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_val_554_);
return v___x_557_;
}
}
case 1:
{
lean_object* v_node_558_; size_t v___x_559_; size_t v___x_560_; 
v_node_558_ = lean_ctor_get(v___x_552_, 0);
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_usize_shift_right(v_x_545_, v___x_559_);
v_x_544_ = v_node_558_;
v_x_545_ = v___x_560_;
goto _start;
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
}
else
{
lean_object* v_ks_563_; lean_object* v_vs_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_ks_563_ = lean_ctor_get(v_x_544_, 0);
v_vs_564_ = lean_ctor_get(v_x_544_, 1);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_563_, v_vs_564_, v___x_565_, v_x_546_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
size_t v_x_1059__boxed_570_; lean_object* v_res_571_; 
v_x_1059__boxed_570_ = lean_unbox_usize(v_x_568_);
lean_dec(v_x_568_);
v_res_571_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_567_, v_x_1059__boxed_570_, v_x_569_);
lean_dec(v_x_569_);
lean_dec_ref(v_x_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
uint64_t v___y_575_; 
if (lean_obj_tag(v_x_573_) == 0)
{
uint64_t v___x_578_; 
v___x_578_ = 1723ULL;
v___y_575_ = v___x_578_;
goto v___jp_574_;
}
else
{
uint64_t v_hash_579_; 
v_hash_579_ = lean_ctor_get_uint64(v_x_573_, sizeof(void*)*2);
v___y_575_ = v_hash_579_;
goto v___jp_574_;
}
v___jp_574_:
{
size_t v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_uint64_to_usize(v___y_575_);
v___x_577_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_572_, v___x_576_, v_x_573_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec_ref(v_x_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
uint8_t v_stage_u2081_585_; 
v_stage_u2081_585_ = lean_ctor_get_uint8(v_x_583_, sizeof(void*)*2);
if (v_stage_u2081_585_ == 0)
{
lean_object* v_map_u2081_586_; lean_object* v_map_u2082_587_; lean_object* v___x_588_; 
v_map_u2081_586_ = lean_ctor_get(v_x_583_, 0);
v_map_u2082_587_ = lean_ctor_get(v_x_583_, 1);
v___x_588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_587_, v_x_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_586_, v_x_584_);
return v___x_589_;
}
else
{
return v___x_588_;
}
}
else
{
lean_object* v_map_u2081_590_; lean_object* v___x_591_; 
v_map_u2081_590_ = lean_ctor_get(v_x_583_, 0);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_590_, v_x_584_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_x_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(lean_object* v_a_595_, lean_object* v_b_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_dec(v_b_596_);
lean_dec(v_a_595_);
return v_x_597_;
}
else
{
lean_object* v_key_598_; lean_object* v_value_599_; lean_object* v_tail_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_612_; 
v_key_598_ = lean_ctor_get(v_x_597_, 0);
v_value_599_ = lean_ctor_get(v_x_597_, 1);
v_tail_600_ = lean_ctor_get(v_x_597_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_612_ == 0)
{
v___x_602_ = v_x_597_;
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_tail_600_);
lean_inc(v_value_599_);
lean_inc(v_key_598_);
lean_dec(v_x_597_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint8_t v___x_604_; 
v___x_604_ = lean_name_eq(v_key_598_, v_a_595_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_595_, v_b_596_, v_tail_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v___x_605_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_key_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_value_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_610_; 
lean_dec(v_value_599_);
lean_dec(v_key_598_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_b_596_);
lean_ctor_set(v___x_602_, 0, v_a_595_);
v___x_610_ = v___x_602_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_595_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_b_596_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_tail_600_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
return v_x_613_;
}
else
{
lean_object* v_key_615_; lean_object* v_value_616_; lean_object* v_tail_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_643_; 
v_key_615_ = lean_ctor_get(v_x_614_, 0);
v_value_616_ = lean_ctor_get(v_x_614_, 1);
v_tail_617_ = lean_ctor_get(v_x_614_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_614_);
if (v_isSharedCheck_643_ == 0)
{
v___x_619_ = v_x_614_;
v_isShared_620_ = v_isSharedCheck_643_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_tail_617_);
lean_inc(v_value_616_);
lean_inc(v_key_615_);
lean_dec(v_x_614_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_643_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint64_t v___y_623_; 
v___x_621_ = lean_array_get_size(v_x_613_);
if (lean_obj_tag(v_key_615_) == 0)
{
uint64_t v___x_641_; 
v___x_641_ = 1723ULL;
v___y_623_ = v___x_641_;
goto v___jp_622_;
}
else
{
uint64_t v_hash_642_; 
v_hash_642_ = lean_ctor_get_uint64(v_key_615_, sizeof(void*)*2);
v___y_623_ = v_hash_642_;
goto v___jp_622_;
}
v___jp_622_:
{
uint64_t v___x_624_; uint64_t v___x_625_; uint64_t v_fold_626_; uint64_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_624_ = 32ULL;
v___x_625_ = lean_uint64_shift_right(v___y_623_, v___x_624_);
v_fold_626_ = lean_uint64_xor(v___y_623_, v___x_625_);
v___x_627_ = 16ULL;
v___x_628_ = lean_uint64_shift_right(v_fold_626_, v___x_627_);
v___x_629_ = lean_uint64_xor(v_fold_626_, v___x_628_);
v___x_630_ = lean_uint64_to_usize(v___x_629_);
v___x_631_ = lean_usize_of_nat(v___x_621_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_sub(v___x_631_, v___x_632_);
v___x_634_ = lean_usize_land(v___x_630_, v___x_633_);
v___x_635_ = lean_array_uget_borrowed(v_x_613_, v___x_634_);
lean_inc(v___x_635_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 2, v___x_635_);
v___x_637_ = v___x_619_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_key_615_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_value_616_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_640_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_uset(v_x_613_, v___x_634_, v___x_637_);
v_x_613_ = v___x_638_;
v_x_614_ = v_tail_617_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_i_644_, lean_object* v_source_645_, lean_object* v_target_646_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_source_645_);
v___x_648_ = lean_nat_dec_lt(v_i_644_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_source_645_);
lean_dec(v_i_644_);
return v_target_646_;
}
else
{
lean_object* v_es_649_; lean_object* v___x_650_; lean_object* v_source_651_; lean_object* v_target_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_es_649_ = lean_array_fget(v_source_645_, v_i_644_);
v___x_650_ = lean_box(0);
v_source_651_ = lean_array_fset(v_source_645_, v_i_644_, v___x_650_);
v_target_652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_646_, v_es_649_);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_i_644_, v___x_653_);
lean_dec(v_i_644_);
v_i_644_ = v___x_654_;
v_source_645_ = v_source_651_;
v_target_646_ = v_target_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(lean_object* v_data_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_nbuckets_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_657_ = lean_array_get_size(v_data_656_);
v___x_658_ = lean_unsigned_to_nat(2u);
v_nbuckets_659_ = lean_nat_mul(v___x_657_, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_box(0);
v___x_662_ = lean_mk_array(v_nbuckets_659_, v___x_661_);
v___x_663_ = lean_array_propagate_mark(v_data_656_, v___x_662_);
v___x_664_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_660_, v_data_656_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(lean_object* v_a_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
else
{
lean_object* v_key_668_; lean_object* v_tail_669_; uint8_t v___x_670_; 
v_key_668_ = lean_ctor_get(v_x_666_, 0);
v_tail_669_ = lean_ctor_get(v_x_666_, 2);
v___x_670_ = lean_name_eq(v_key_668_, v_a_665_);
if (v___x_670_ == 0)
{
v_x_666_ = v_tail_669_;
goto _start;
}
else
{
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec(v_a_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(lean_object* v_m_676_, lean_object* v_a_677_, lean_object* v_b_678_){
_start:
{
lean_object* v_size_679_; lean_object* v_buckets_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_726_; 
v_size_679_ = lean_ctor_get(v_m_676_, 0);
v_buckets_680_ = lean_ctor_get(v_m_676_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_m_676_);
if (v_isSharedCheck_726_ == 0)
{
v___x_682_ = v_m_676_;
v_isShared_683_ = v_isSharedCheck_726_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_buckets_680_);
lean_inc(v_size_679_);
lean_dec(v_m_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_726_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; uint64_t v___y_686_; 
v___x_684_ = lean_array_get_size(v_buckets_680_);
if (lean_obj_tag(v_a_677_) == 0)
{
uint64_t v___x_724_; 
v___x_724_ = 1723ULL;
v___y_686_ = v___x_724_;
goto v___jp_685_;
}
else
{
uint64_t v_hash_725_; 
v_hash_725_ = lean_ctor_get_uint64(v_a_677_, sizeof(void*)*2);
v___y_686_ = v_hash_725_;
goto v___jp_685_;
}
v___jp_685_:
{
uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v_fold_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v_bkt_698_; uint8_t v___x_699_; 
v___x_687_ = 32ULL;
v___x_688_ = lean_uint64_shift_right(v___y_686_, v___x_687_);
v_fold_689_ = lean_uint64_xor(v___y_686_, v___x_688_);
v___x_690_ = 16ULL;
v___x_691_ = lean_uint64_shift_right(v_fold_689_, v___x_690_);
v___x_692_ = lean_uint64_xor(v_fold_689_, v___x_691_);
v___x_693_ = lean_uint64_to_usize(v___x_692_);
v___x_694_ = lean_usize_of_nat(v___x_684_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_sub(v___x_694_, v___x_695_);
v___x_697_ = lean_usize_land(v___x_693_, v___x_696_);
v_bkt_698_ = lean_array_uget_borrowed(v_buckets_680_, v___x_697_);
v___x_699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_677_, v_bkt_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v_size_x27_701_; lean_object* v___x_702_; lean_object* v_buckets_x27_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_700_ = lean_unsigned_to_nat(1u);
v_size_x27_701_ = lean_nat_add(v_size_679_, v___x_700_);
lean_dec(v_size_679_);
lean_inc(v_bkt_698_);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v_a_677_);
lean_ctor_set(v___x_702_, 1, v_b_678_);
lean_ctor_set(v___x_702_, 2, v_bkt_698_);
v_buckets_x27_703_ = lean_array_uset(v_buckets_680_, v___x_697_, v___x_702_);
v___x_704_ = lean_unsigned_to_nat(4u);
v___x_705_ = lean_nat_mul(v_size_x27_701_, v___x_704_);
v___x_706_ = lean_unsigned_to_nat(3u);
v___x_707_ = lean_nat_div(v___x_705_, v___x_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_array_get_size(v_buckets_x27_703_);
v___x_709_ = lean_nat_dec_le(v___x_707_, v___x_708_);
lean_dec(v___x_707_);
if (v___x_709_ == 0)
{
lean_object* v_val_710_; lean_object* v___x_712_; 
v_val_710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_703_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_val_710_);
lean_ctor_set(v___x_682_, 0, v_size_x27_701_);
v___x_712_ = v___x_682_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_size_x27_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_val_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_715_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_buckets_x27_703_);
lean_ctor_set(v___x_682_, 0, v_size_x27_701_);
v___x_715_ = v___x_682_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_size_x27_701_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_buckets_x27_703_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v___x_717_; lean_object* v_buckets_x27_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
lean_inc(v_bkt_698_);
v___x_717_ = lean_box(0);
v_buckets_x27_718_ = lean_array_uset(v_buckets_680_, v___x_697_, v___x_717_);
v___x_719_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_677_, v_b_678_, v_bkt_698_);
v___x_720_ = lean_array_uset(v_buckets_x27_718_, v___x_697_, v___x_719_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_720_);
v___x_722_ = v___x_682_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_size_679_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v_ks_731_; lean_object* v_vs_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_756_; 
v_ks_731_ = lean_ctor_get(v_x_727_, 0);
v_vs_732_ = lean_ctor_get(v_x_727_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_756_ == 0)
{
v___x_734_ = v_x_727_;
v_isShared_735_ = v_isSharedCheck_756_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_vs_732_);
lean_inc(v_ks_731_);
lean_dec(v_x_727_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_756_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_ks_731_);
v___x_737_ = lean_nat_dec_lt(v_x_728_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec(v_x_728_);
v___x_738_ = lean_array_push(v_ks_731_, v_x_729_);
v___x_739_ = lean_array_push(v_vs_732_, v_x_730_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_739_);
lean_ctor_set(v___x_734_, 0, v___x_738_);
v___x_741_ = v___x_734_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v_k_x27_743_; uint8_t v___x_744_; 
v_k_x27_743_ = lean_array_fget_borrowed(v_ks_731_, v_x_728_);
v___x_744_ = lean_name_eq(v_x_729_, v_k_x27_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_746_; 
if (v_isShared_735_ == 0)
{
v___x_746_ = v___x_734_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_ks_731_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_vs_732_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_x_728_, v___x_747_);
lean_dec(v_x_728_);
v_x_727_ = v___x_746_;
v_x_728_ = v___x_748_;
goto _start;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_array_fset(v_ks_731_, v_x_728_, v_x_729_);
v___x_752_ = lean_array_fset(v_vs_732_, v_x_728_, v_x_730_);
lean_dec(v_x_728_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_752_);
lean_ctor_set(v___x_734_, 0, v___x_751_);
v___x_754_ = v___x_734_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_n_757_, lean_object* v_k_758_, lean_object* v_v_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_757_, v___x_760_, v_k_758_, v_v_759_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(lean_object* v_x_763_, size_t v_x_764_, size_t v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v_es_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v_j_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_es_768_ = lean_ctor_get(v_x_763_, 0);
v___x_769_ = ((size_t)31ULL);
v___x_770_ = lean_usize_land(v_x_764_, v___x_769_);
v_j_771_ = lean_usize_to_nat(v___x_770_);
v___x_772_ = lean_array_get_size(v_es_768_);
v___x_773_ = lean_nat_dec_lt(v_j_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_j_771_);
lean_dec(v_x_767_);
lean_dec(v_x_766_);
return v_x_763_;
}
else
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_812_; 
lean_inc_ref(v_es_768_);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_x_763_, 0);
lean_dec(v_unused_813_);
v___x_775_ = v_x_763_;
v_isShared_776_ = v_isSharedCheck_812_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_x_763_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_812_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v_xs_x27_779_; lean_object* v___y_781_; 
v_v_777_ = lean_array_fget(v_es_768_, v_j_771_);
v___x_778_ = lean_box(0);
v_xs_x27_779_ = lean_array_fset(v_es_768_, v_j_771_, v___x_778_);
switch(lean_obj_tag(v_v_777_))
{
case 0:
{
lean_object* v_key_786_; lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_key_786_ = lean_ctor_get(v_v_777_, 0);
v_val_787_ = lean_ctor_get(v_v_777_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_v_777_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v_v_777_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_inc(v_key_786_);
lean_dec(v_v_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; 
v___x_791_ = lean_name_eq(v_x_766_, v_key_786_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_789_);
v___x_792_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_786_, v_val_787_, v_x_766_, v_x_767_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___y_781_ = v___x_793_;
goto v___jp_780_;
}
else
{
lean_object* v___x_795_; 
lean_dec(v_val_787_);
lean_dec(v_key_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v_x_767_);
lean_ctor_set(v___x_789_, 0, v_x_766_);
v___x_795_ = v___x_789_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_x_766_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_x_767_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_781_ = v___x_795_;
goto v___jp_780_;
}
}
}
}
case 1:
{
lean_object* v_node_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_node_798_ = lean_ctor_get(v_v_777_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_v_777_);
if (v_isSharedCheck_810_ == 0)
{
v___x_800_ = v_v_777_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_node_798_);
lean_dec(v_v_777_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_802_ = ((size_t)5ULL);
v___x_803_ = lean_usize_shift_right(v_x_764_, v___x_802_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_x_765_, v___x_804_);
v___x_806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_798_, v___x_803_, v___x_805_, v_x_766_, v_x_767_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v___y_781_ = v___x_808_;
goto v___jp_780_;
}
}
}
default: 
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_x_766_);
lean_ctor_set(v___x_811_, 1, v_x_767_);
v___y_781_ = v___x_811_;
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_array_fset(v_xs_x27_779_, v_j_771_, v___y_781_);
lean_dec(v_j_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_782_);
v___x_784_ = v___x_775_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
else
{
lean_object* v_ks_814_; lean_object* v_vs_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_833_; 
v_ks_814_ = lean_ctor_get(v_x_763_, 0);
v_vs_815_ = lean_ctor_get(v_x_763_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_833_ == 0)
{
v___x_817_ = v_x_763_;
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_vs_815_);
lean_inc(v_ks_814_);
lean_dec(v_x_763_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_ks_814_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_vs_815_);
v___x_820_ = v_reuseFailAlloc_832_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v_newNode_821_; size_t v___x_822_; uint8_t v___x_823_; 
v_newNode_821_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_820_, v_x_766_, v_x_767_);
v___x_822_ = ((size_t)7ULL);
v___x_823_ = lean_usize_dec_le(v___x_822_, v_x_765_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_824_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_821_);
v___x_825_ = lean_unsigned_to_nat(4u);
v___x_826_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
lean_dec(v___x_824_);
if (v___x_826_ == 0)
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_ks_827_ = lean_ctor_get(v_newNode_821_, 0);
lean_inc_ref(v_ks_827_);
v_vs_828_ = lean_ctor_get(v_newNode_821_, 1);
lean_inc_ref(v_vs_828_);
lean_dec_ref(v_newNode_821_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_765_, v_ks_827_, v_vs_828_, v___x_829_, v___x_830_);
lean_dec_ref(v_vs_828_);
lean_dec_ref(v_ks_827_);
return v___x_831_;
}
else
{
return v_newNode_821_;
}
}
else
{
return v_newNode_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(size_t v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_i_837_, lean_object* v_entries_838_){
_start:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v_keys_835_);
v___x_840_ = lean_nat_dec_lt(v_i_837_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_i_837_);
return v_entries_838_;
}
else
{
lean_object* v_k_841_; lean_object* v_v_842_; uint64_t v___y_844_; 
v_k_841_ = lean_array_fget_borrowed(v_keys_835_, v_i_837_);
v_v_842_ = lean_array_fget_borrowed(v_vals_836_, v_i_837_);
if (lean_obj_tag(v_k_841_) == 0)
{
uint64_t v___x_855_; 
v___x_855_ = 1723ULL;
v___y_844_ = v___x_855_;
goto v___jp_843_;
}
else
{
uint64_t v_hash_856_; 
v_hash_856_ = lean_ctor_get_uint64(v_k_841_, sizeof(void*)*2);
v___y_844_ = v_hash_856_;
goto v___jp_843_;
}
v___jp_843_:
{
size_t v_h_845_; size_t v___x_846_; lean_object* v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v_h_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_h_845_ = lean_uint64_to_usize(v___y_844_);
v___x_846_ = ((size_t)5ULL);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_sub(v_depth_834_, v___x_848_);
v___x_850_ = lean_usize_mul(v___x_846_, v___x_849_);
v_h_851_ = lean_usize_shift_right(v_h_845_, v___x_850_);
v___x_852_ = lean_nat_add(v_i_837_, v___x_847_);
lean_dec(v_i_837_);
lean_inc(v_v_842_);
lean_inc(v_k_841_);
v___x_853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_838_, v_h_851_, v_depth_834_, v_k_841_, v_v_842_);
v_i_837_ = v___x_852_;
v_entries_838_ = v___x_853_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_i_860_, lean_object* v_entries_861_){
_start:
{
size_t v_depth_boxed_862_; lean_object* v_res_863_; 
v_depth_boxed_862_ = lean_unbox_usize(v_depth_857_);
lean_dec(v_depth_857_);
v_res_863_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_862_, v_keys_858_, v_vals_859_, v_i_860_, v_entries_861_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v_x_1435__boxed_869_; size_t v_x_1436__boxed_870_; lean_object* v_res_871_; 
v_x_1435__boxed_869_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_x_1436__boxed_870_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_864_, v_x_1435__boxed_869_, v_x_1436__boxed_870_, v_x_867_, v_x_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
uint64_t v___y_876_; 
if (lean_obj_tag(v_x_873_) == 0)
{
uint64_t v___x_880_; 
v___x_880_ = 1723ULL;
v___y_876_ = v___x_880_;
goto v___jp_875_;
}
else
{
uint64_t v_hash_881_; 
v_hash_881_ = lean_ctor_get_uint64(v_x_873_, sizeof(void*)*2);
v___y_876_ = v_hash_881_;
goto v___jp_875_;
}
v___jp_875_:
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_uint64_to_usize(v___y_876_);
v___x_878_ = ((size_t)1ULL);
v___x_879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_872_, v___x_877_, v___x_878_, v_x_873_, v_x_874_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
uint8_t v_stage_u2081_885_; 
v_stage_u2081_885_ = lean_ctor_get_uint8(v_x_882_, sizeof(void*)*2);
if (v_stage_u2081_885_ == 0)
{
lean_object* v_map_u2081_886_; lean_object* v_map_u2082_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
v_map_u2081_886_ = lean_ctor_get(v_x_882_, 0);
v_map_u2082_887_ = lean_ctor_get(v_x_882_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_889_ = v_x_882_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_map_u2082_887_);
lean_inc(v_map_u2081_886_);
lean_dec(v_x_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_887_, v_x_883_, v_x_884_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_map_u2081_886_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*2, v_stage_u2081_885_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_map_u2081_896_; lean_object* v_map_u2082_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_map_u2081_896_ = lean_ctor_get(v_x_882_, 0);
v_map_u2082_897_ = lean_ctor_get(v_x_882_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v_x_882_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_map_u2082_897_);
lean_inc(v_map_u2081_896_);
lean_dec(v_x_882_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_896_, v_x_883_, v_x_884_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_map_u2082_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_904_, sizeof(void*)*2, v_stage_u2081_885_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_unsigned_to_nat(32u);
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1(void){
_start:
{
size_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_909_ = ((size_t)5ULL);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_unsigned_to_nat(32u);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_911_);
v___x_913_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0);
v___x_914_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_912_);
lean_ctor_set(v___x_914_, 2, v___x_910_);
lean_ctor_set(v___x_914_, 3, v___x_910_);
lean_ctor_set_usize(v___x_914_, 4, v___x_909_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(lean_object* v_scopedEntries_915_, lean_object* v_ns_916_, lean_object* v_b_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_915_, v_ns_916_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1, &l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1);
v___x_920_ = l_Lean_PersistentArray_push___redArg(v___x_919_, v_b_917_);
v___x_921_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_915_, v_ns_916_, v___x_920_);
return v___x_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_val_922_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v___x_918_, 1);
v___x_923_ = l_Lean_PersistentArray_push___redArg(v_val_922_, v_b_917_);
v___x_924_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_915_, v_ns_916_, v___x_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* v_00_u03b2_925_, lean_object* v_scopedEntries_926_, lean_object* v_ns_927_, lean_object* v_b_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_926_, v_ns_927_, v_b_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(v_00_u03b2_934_, v_x_935_, v_x_936_);
lean_dec(v_x_936_);
lean_dec_ref(v_x_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_x_939_, v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_947_, v_x_948_, v_x_949_);
lean_dec(v_x_949_);
lean_dec_ref(v_x_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_952_, v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b2_955_, lean_object* v_m_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_955_, v_m_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_m_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_960_, v_x_961_, v_x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(lean_object* v_00_u03b2_964_, lean_object* v_m_965_, lean_object* v_a_966_, lean_object* v_b_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_965_, v_a_966_, v_b_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_969_, lean_object* v_x_970_, size_t v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_970_, v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_1736__boxed_978_; lean_object* v_res_979_; 
v_x_1736__boxed_978_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_res_979_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_974_, v_x_975_, v_x_1736__boxed_978_, v_x_977_);
lean_dec(v_x_977_);
lean_dec_ref(v_x_975_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_980_, lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_984_, lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_984_, v_a_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec(v_a_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, size_t v_x_990_, size_t v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_989_, v_x_990_, v_x_991_, v_x_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
size_t v_x_1752__boxed_1001_; size_t v_x_1753__boxed_1002_; lean_object* v_res_1003_; 
v_x_1752__boxed_1001_ = lean_unbox_usize(v_x_997_);
lean_dec(v_x_997_);
v_x_1753__boxed_1002_ = lean_unbox_usize(v_x_998_);
lean_dec(v_x_998_);
v_res_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_995_, v_x_996_, v_x_1752__boxed_1001_, v_x_1753__boxed_1002_, v_x_999_, v_x_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_1005_, v_x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_a_1009_, lean_object* v_x_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_1008_, v_a_1009_, v_x_1010_);
lean_dec(v_x_1010_);
lean_dec(v_a_1009_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1013_, lean_object* v_data_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1016_, lean_object* v_a_1017_, lean_object* v_b_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_1017_, v_b_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1021_, lean_object* v_keys_1022_, lean_object* v_vals_1023_, lean_object* v_heq_1024_, lean_object* v_i_1025_, lean_object* v_k_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1022_, v_vals_1023_, v_i_1025_, v_k_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1028_, lean_object* v_keys_1029_, lean_object* v_vals_1030_, lean_object* v_heq_1031_, lean_object* v_i_1032_, lean_object* v_k_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1028_, v_keys_1029_, v_vals_1030_, v_heq_1031_, v_i_1032_, v_k_1033_);
lean_dec(v_k_1033_);
lean_dec_ref(v_vals_1030_);
lean_dec_ref(v_keys_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1035_, lean_object* v_n_1036_, lean_object* v_k_1037_, lean_object* v_v_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_1036_, v_k_1037_, v_v_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1040_, size_t v_depth_1041_, lean_object* v_keys_1042_, lean_object* v_vals_1043_, lean_object* v_heq_1044_, lean_object* v_i_1045_, lean_object* v_entries_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_1041_, v_keys_1042_, v_vals_1043_, v_i_1045_, v_entries_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1048_, lean_object* v_depth_1049_, lean_object* v_keys_1050_, lean_object* v_vals_1051_, lean_object* v_heq_1052_, lean_object* v_i_1053_, lean_object* v_entries_1054_){
_start:
{
size_t v_depth_boxed_1055_; lean_object* v_res_1056_; 
v_depth_boxed_1055_ = lean_unbox_usize(v_depth_1049_);
lean_dec(v_depth_1049_);
v_res_1056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_1048_, v_depth_boxed_1055_, v_keys_1050_, v_vals_1051_, v_heq_1052_, v_i_1053_, v_entries_1054_);
lean_dec_ref(v_vals_1051_);
lean_dec_ref(v_keys_1050_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_1057_, lean_object* v_i_1058_, lean_object* v_source_1059_, lean_object* v_target_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_1058_, v_source_1059_, v_target_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_1063_, v_x_1064_, v_x_1065_, v_x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_1069_, v_x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(lean_object* v_descr_1072_, lean_object* v_a_1073_, lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_a_1081_; uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_descr_1072_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_b_1077_);
return v___x_1086_;
}
else
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_array_uget_borrowed(v_as_1074_, v_i_1076_);
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v_ofOLeanEntry_1090_; lean_object* v___x_1091_; 
v_a_1088_ = lean_ctor_get(v_a_1087_, 0);
v_a_1089_ = lean_ctor_get(v_a_1087_, 1);
v_ofOLeanEntry_1090_ = lean_ctor_get(v_descr_1072_, 2);
lean_inc_ref(v_ofOLeanEntry_1090_);
lean_inc_ref(v___y_1078_);
lean_inc(v_a_1089_);
lean_inc(v_a_1073_);
v___x_1091_ = lean_apply_4(v_ofOLeanEntry_1090_, v_a_1073_, v_a_1089_, v___y_1078_, lean_box(0));
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
lean_inc(v_a_1088_);
v___x_1093_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_b_1077_, v_a_1088_, v_a_1092_);
v_a_1081_ = v___x_1093_;
goto v___jp_1080_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_b_1077_);
lean_dec(v_a_1073_);
lean_dec_ref(v_descr_1072_);
v_a_1094_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1091_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1091_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
v_a_1081_ = v_b_1077_;
goto v___jp_1080_;
}
}
v___jp_1080_:
{
size_t v___x_1082_; size_t v___x_1083_; 
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1076_, v___x_1082_);
v_i_1076_ = v___x_1083_;
v_b_1077_ = v_a_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(lean_object* v_descr_1102_, lean_object* v_a_1103_, lean_object* v_as_1104_, lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1102_, v_a_1103_, v_as_1104_, v_sz_boxed_1110_, v_i_boxed_1111_, v_b_1107_, v___y_1108_);
lean_dec_ref(v___y_1108_);
lean_dec_ref(v_as_1104_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(lean_object* v_descr_1113_, lean_object* v_a_1114_, lean_object* v_as_1115_, size_t v_sz_1116_, size_t v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_lt(v_i_1117_, v_sz_1116_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec(v_a_1114_);
lean_dec_ref(v_descr_1113_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_b_1118_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v_a_1123_ = lean_array_uget_borrowed(v_as_1115_, v_i_1117_);
v_sz_1124_ = lean_array_size(v_a_1123_);
v___x_1125_ = ((size_t)0ULL);
lean_inc(v_a_1114_);
lean_inc_ref(v_descr_1113_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1113_, v_a_1114_, v_a_1123_, v_sz_1124_, v___x_1125_, v_b_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; size_t v___x_1128_; size_t v___x_1129_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1117_, v___x_1128_);
v_i_1117_ = v___x_1129_;
v_b_1118_ = v_a_1127_;
goto _start;
}
else
{
lean_dec(v_a_1114_);
lean_dec_ref(v_descr_1113_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(lean_object* v_descr_1131_, lean_object* v_a_1132_, lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1131_, v_a_1132_, v_as_1133_, v_sz_boxed_1139_, v_i_boxed_1140_, v_b_1136_, v___y_1137_);
lean_dec_ref(v___y_1137_);
lean_dec_ref(v_as_1133_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg(lean_object* v_descr_1142_, lean_object* v_as_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_finalizeImport_1146_; lean_object* v_importGlobals_1147_; lean_object* v___x_1148_; 
v_finalizeImport_1146_ = lean_ctor_get(v_descr_1142_, 6);
lean_inc(v_finalizeImport_1146_);
v_importGlobals_1147_ = lean_ctor_get(v_descr_1142_, 9);
lean_inc_ref(v_importGlobals_1147_);
lean_inc_ref(v_a_1144_);
lean_inc_ref(v_as_1143_);
v___x_1148_ = lean_apply_3(v_importGlobals_1147_, v_as_1143_, v_a_1144_, lean_box(0));
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; size_t v_sz_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_n(v_a_1149_, 2);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = 1;
v___x_1151_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4, &l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___redArg___closed__4);
v_sz_1152_ = lean_array_size(v_as_1143_);
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1142_, v_a_1149_, v_as_1143_, v_sz_1152_, v___x_1153_, v___x_1151_, v_a_1144_);
lean_dec_ref(v_as_1143_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1170_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1170_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1170_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1159_ = lean_apply_1(v_finalizeImport_1146_, v_a_1149_);
v___x_1160_ = l_Lean_NameSet_empty;
v___x_1161_ = 0;
v___x_1162_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1163_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1163_, 0, v___x_1159_);
lean_ctor_set(v___x_1163_, 1, v___x_1160_);
lean_ctor_set(v___x_1163_, 2, v___x_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3, v___x_1150_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3 + 1, v___x_1161_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_a_1155_);
lean_ctor_set(v___x_1166_, 2, v___x_1164_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1166_);
v___x_1168_ = v___x_1157_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v_a_1149_);
lean_dec(v_finalizeImport_1146_);
v_a_1171_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1154_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1154_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
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
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_finalizeImport_1146_);
lean_dec_ref(v_as_1143_);
lean_dec_ref(v_descr_1142_);
v_a_1179_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1148_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1148_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(lean_object* v_descr_1187_, lean_object* v_as_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1187_, v_as_1188_, v_a_1189_);
lean_dec_ref(v_a_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_00_u03c3_1194_, lean_object* v_descr_1195_, lean_object* v_as_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_1195_, v_as_1196_, v_a_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addImportedFn___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_00_u03c3_1202_, lean_object* v_descr_1203_, lean_object* v_as_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_ScopedEnvExtension_addImportedFn(v_00_u03b1_1200_, v_00_u03b2_1201_, v_00_u03c3_1202_, v_descr_1203_, v_as_1204_, v_a_1205_);
lean_dec_ref(v_a_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(lean_object* v_00_u03b1_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_00_u03c3_1210_, lean_object* v_descr_1211_, lean_object* v_a_1212_, lean_object* v_as_1213_, size_t v_sz_1214_, size_t v_i_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_1211_, v_a_1212_, v_as_1213_, v_sz_1214_, v_i_1215_, v_b_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_00_u03c3_1222_, lean_object* v_descr_1223_, lean_object* v_a_1224_, lean_object* v_as_1225_, lean_object* v_sz_1226_, lean_object* v_i_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1226_);
lean_dec(v_sz_1226_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1227_);
lean_dec(v_i_1227_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_1220_, v_00_u03b2_1221_, v_00_u03c3_1222_, v_descr_1223_, v_a_1224_, v_as_1225_, v_sz_boxed_1231_, v_i_boxed_1232_, v_b_1228_, v___y_1229_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_as_1225_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_00_u03c3_1236_, lean_object* v_descr_1237_, lean_object* v_a_1238_, lean_object* v_as_1239_, size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_1237_, v_a_1238_, v_as_1239_, v_sz_1240_, v_i_1241_, v_b_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_00_u03c3_1248_, lean_object* v_descr_1249_, lean_object* v_a_1250_, lean_object* v_as_1251_, lean_object* v_sz_1252_, lean_object* v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1252_);
lean_dec(v_sz_1252_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1253_);
lean_dec(v_i_1253_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_1246_, v_00_u03b2_1247_, v_00_u03c3_1248_, v_descr_1249_, v_a_1250_, v_as_1251_, v_sz_boxed_1257_, v_i_boxed_1258_, v_b_1254_, v___y_1255_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_as_1251_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(lean_object* v_a_1260_, lean_object* v_descr_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
if (lean_obj_tag(v_a_1263_) == 0)
{
lean_object* v___x_1265_; 
lean_dec(v_a_1262_);
lean_dec_ref(v_descr_1261_);
v___x_1265_ = l_List_reverse___redArg(v_a_1264_);
return v___x_1265_;
}
else
{
lean_object* v_head_1266_; lean_object* v_tail_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1296_; 
v_head_1266_ = lean_ctor_get(v_a_1263_, 0);
v_tail_1267_ = lean_ctor_get(v_a_1263_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1263_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1269_ = v_a_1263_;
v_isShared_1270_ = v_isSharedCheck_1296_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_tail_1267_);
lean_inc(v_head_1266_);
lean_dec(v_a_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1296_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___y_1272_; lean_object* v_state_1277_; lean_object* v_activeScopes_1278_; uint8_t v_delimitsLocal_1279_; uint8_t v_scopeChanged_1280_; lean_object* v_scopeChangedDecls_1281_; uint8_t v___x_1282_; 
v_state_1277_ = lean_ctor_get(v_head_1266_, 0);
v_activeScopes_1278_ = lean_ctor_get(v_head_1266_, 1);
v_delimitsLocal_1279_ = lean_ctor_get_uint8(v_head_1266_, sizeof(void*)*3);
v_scopeChanged_1280_ = lean_ctor_get_uint8(v_head_1266_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1281_ = lean_ctor_get(v_head_1266_, 2);
v___x_1282_ = l_Lean_NameSet_contains(v_activeScopes_1278_, v_a_1260_);
if (v___x_1282_ == 0)
{
v___y_1272_ = v_head_1266_;
goto v___jp_1271_;
}
else
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1292_; 
lean_inc_ref(v_scopeChangedDecls_1281_);
lean_inc(v_activeScopes_1278_);
lean_inc(v_state_1277_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_head_1266_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; 
v_unused_1293_ = lean_ctor_get(v_head_1266_, 2);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_head_1266_, 1);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_head_1266_, 0);
lean_dec(v_unused_1295_);
v___x_1284_ = v_head_1266_;
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v_head_1266_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_addEntry_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v_addEntry_1286_ = lean_ctor_get(v_descr_1261_, 4);
lean_inc(v_addEntry_1286_);
lean_inc(v_a_1262_);
v___x_1287_ = lean_apply_2(v_addEntry_1286_, v_state_1277_, v_a_1262_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_activeScopes_1278_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_scopeChangedDecls_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*3, v_delimitsLocal_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*3 + 1, v_scopeChanged_1280_);
v___x_1289_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; 
lean_inc(v_a_1262_);
lean_inc_ref(v_descr_1261_);
v___x_1290_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_1261_, v___x_1289_, v_a_1262_);
v___y_1272_ = v___x_1290_;
goto v___jp_1271_;
}
}
}
v___jp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_a_1264_);
lean_ctor_set(v___x_1269_, 0, v___y_1272_);
v___x_1274_ = v___x_1269_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___y_1272_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_a_1264_);
v___x_1274_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_a_1263_ = v_tail_1267_;
v_a_1264_ = v___x_1274_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(lean_object* v_a_1297_, lean_object* v_descr_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1297_, v_descr_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(lean_object* v_descr_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
if (lean_obj_tag(v_a_1305_) == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_a_1304_);
lean_dec_ref(v_descr_1303_);
v___x_1307_ = l_List_reverse___redArg(v_a_1306_);
return v___x_1307_;
}
else
{
lean_object* v_head_1308_; lean_object* v_tail_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1331_; 
v_head_1308_ = lean_ctor_get(v_a_1305_, 0);
v_tail_1309_ = lean_ctor_get(v_a_1305_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_a_1305_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1311_ = v_a_1305_;
v_isShared_1312_ = v_isSharedCheck_1331_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_tail_1309_);
lean_inc(v_head_1308_);
lean_dec(v_a_1305_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1331_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_addEntry_1313_; lean_object* v_state_1314_; lean_object* v_activeScopes_1315_; uint8_t v_delimitsLocal_1316_; uint8_t v_scopeChanged_1317_; lean_object* v_scopeChangedDecls_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1330_; 
v_addEntry_1313_ = lean_ctor_get(v_descr_1303_, 4);
v_state_1314_ = lean_ctor_get(v_head_1308_, 0);
v_activeScopes_1315_ = lean_ctor_get(v_head_1308_, 1);
v_delimitsLocal_1316_ = lean_ctor_get_uint8(v_head_1308_, sizeof(void*)*3);
v_scopeChanged_1317_ = lean_ctor_get_uint8(v_head_1308_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1318_ = lean_ctor_get(v_head_1308_, 2);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_head_1308_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1320_ = v_head_1308_;
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_scopeChangedDecls_1318_);
lean_inc(v_activeScopes_1315_);
lean_inc(v_state_1314_);
lean_dec(v_head_1308_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_inc(v_addEntry_1313_);
lean_inc(v_a_1304_);
v___x_1322_ = lean_apply_2(v_addEntry_1313_, v_state_1314_, v_a_1304_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_activeScopes_1315_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_scopeChangedDecls_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*3, v_delimitsLocal_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*3 + 1, v_scopeChanged_1317_);
v___x_1324_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v_a_1306_);
lean_ctor_set(v___x_1311_, 0, v___x_1324_);
v___x_1326_ = v___x_1311_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_a_1306_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
v_a_1305_ = v_tail_1309_;
v_a_1306_ = v___x_1326_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn___redArg(lean_object* v_descr_1332_, lean_object* v_s_1333_, lean_object* v_e_1334_){
_start:
{
if (lean_obj_tag(v_e_1334_) == 0)
{
lean_object* v_stateStack_1335_; lean_object* v_scopedEntries_1336_; lean_object* v_newEntries_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1357_; 
v_stateStack_1335_ = lean_ctor_get(v_s_1333_, 0);
v_scopedEntries_1336_ = lean_ctor_get(v_s_1333_, 1);
v_newEntries_1337_ = lean_ctor_get(v_s_1333_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1339_ = v_s_1333_;
v_isShared_1340_ = v_isSharedCheck_1357_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_newEntries_1337_);
lean_inc(v_scopedEntries_1336_);
lean_inc(v_stateStack_1335_);
lean_dec(v_s_1333_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1357_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_a_1341_ = lean_ctor_get(v_e_1334_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_e_1334_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1343_ = v_e_1334_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v_e_1334_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_toOLeanEntry_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_toOLeanEntry_1345_ = lean_ctor_get(v_descr_1332_, 3);
lean_inc(v_toOLeanEntry_1345_);
v___x_1346_ = lean_box(0);
lean_inc(v_a_1341_);
v___x_1347_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1332_, v_a_1341_, v_stateStack_1335_, v___x_1346_);
v___x_1348_ = lean_apply_1(v_toOLeanEntry_1345_, v_a_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1348_);
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v_newEntries_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 2, v___x_1351_);
lean_ctor_set(v___x_1339_, 0, v___x_1347_);
v___x_1353_ = v___x_1339_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_scopedEntries_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_object* v_stateStack_1358_; lean_object* v_scopedEntries_1359_; lean_object* v_newEntries_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1382_; 
v_stateStack_1358_ = lean_ctor_get(v_s_1333_, 0);
v_scopedEntries_1359_ = lean_ctor_get(v_s_1333_, 1);
v_newEntries_1360_ = lean_ctor_get(v_s_1333_, 2);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1362_ = v_s_1333_;
v_isShared_1363_ = v_isSharedCheck_1382_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_newEntries_1360_);
lean_inc(v_scopedEntries_1359_);
lean_inc(v_stateStack_1358_);
lean_dec(v_s_1333_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1382_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_a_1364_; lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1381_; 
v_a_1364_ = lean_ctor_get(v_e_1334_, 0);
v_a_1365_ = lean_ctor_get(v_e_1334_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_e_1334_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1367_ = v_e_1334_;
v_isShared_1368_ = v_isSharedCheck_1381_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_inc(v_a_1364_);
lean_dec(v_e_1334_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1381_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_toOLeanEntry_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v_toOLeanEntry_1369_ = lean_ctor_get(v_descr_1332_, 3);
lean_inc(v_toOLeanEntry_1369_);
v___x_1370_ = lean_box(0);
lean_inc_n(v_a_1365_, 2);
v___x_1371_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1364_, v_descr_1332_, v_a_1365_, v_stateStack_1358_, v___x_1370_);
lean_inc(v_a_1364_);
v___x_1372_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(v_scopedEntries_1359_, v_a_1364_, v_a_1365_);
v___x_1373_ = lean_apply_1(v_toOLeanEntry_1369_, v_a_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1373_);
v___x_1375_ = v___x_1367_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1364_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v_newEntries_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 2, v___x_1376_);
lean_ctor_set(v___x_1362_, 1, v___x_1372_);
lean_ctor_set(v___x_1362_, 0, v___x_1371_);
v___x_1378_ = v___x_1362_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_00_u03c3_1385_, lean_object* v_descr_1386_, lean_object* v_s_1387_, lean_object* v_e_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_1386_, v_s_1387_, v_e_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(lean_object* v_00_u03c3_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_00_u03b1_1392_, lean_object* v_descr_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(v_descr_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(lean_object* v_00_u03c3_1398_, lean_object* v_a_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_00_u03b1_1401_, lean_object* v_descr_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(v_a_1399_, v_descr_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(lean_object* v_00_u03c3_1407_, lean_object* v_a_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_00_u03b1_1410_, lean_object* v_descr_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(v_00_u03c3_1407_, v_a_1408_, v_00_u03b2_1409_, v_00_u03b1_1410_, v_descr_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1408_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(lean_object* v_descr_1416_, lean_object* v_env_1417_, lean_object* v_as_1418_, size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v_a_1423_; uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
if (v___x_1427_ == 0)
{
lean_dec_ref(v_env_1417_);
lean_dec_ref(v_descr_1416_);
return v_b_1421_;
}
else
{
lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1529_; 
v_snd_1428_ = lean_ctor_get(v_b_1421_, 1);
v_fst_1429_ = lean_ctor_get(v_b_1421_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_b_1421_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1431_ = v_b_1421_;
v_isShared_1432_ = v_isSharedCheck_1529_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1428_);
lean_inc(v_fst_1429_);
lean_dec(v_b_1421_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1529_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1528_; 
v_fst_1433_ = lean_ctor_get(v_snd_1428_, 0);
v_snd_1434_ = lean_ctor_get(v_snd_1428_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_snd_1428_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1436_ = v_snd_1428_;
v_isShared_1437_ = v_isSharedCheck_1528_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_inc(v_fst_1433_);
lean_dec(v_snd_1428_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1528_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_a_1438_; 
v_a_1438_ = lean_array_uget(v_as_1418_, v_i_1420_);
if (lean_obj_tag(v_a_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1488_; 
v_a_1439_ = lean_ctor_get(v_a_1438_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1441_ = v_a_1438_;
v_isShared_1442_ = v_isSharedCheck_1488_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v_a_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1488_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_exportEntry_x3f_1443_; lean_object* v___x_1444_; lean_object* v_exported_1445_; lean_object* v_server_1446_; lean_object* v_private_1447_; lean_object* v___y_1449_; lean_object* v_server_1450_; lean_object* v_exported_1469_; 
v_exportEntry_x3f_1443_ = lean_ctor_get(v_descr_1416_, 7);
lean_inc_ref(v_exportEntry_x3f_1443_);
lean_inc_ref(v_env_1417_);
v___x_1444_ = lean_apply_2(v_exportEntry_x3f_1443_, v_env_1417_, v_a_1439_);
v_exported_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_exported_1445_);
v_server_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_server_1446_);
v_private_1447_ = lean_ctor_get(v___x_1444_, 2);
lean_inc(v_private_1447_);
lean_dec_ref(v___x_1444_);
if (lean_obj_tag(v_exported_1445_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1487_; 
v_val_1479_ = lean_ctor_get(v_exported_1445_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_exported_1445_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1481_ = v_exported_1445_;
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v_exported_1445_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 0);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_val_1479_);
v___x_1484_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_array_push(v_fst_1429_, v___x_1484_);
v_exported_1469_ = v___x_1485_;
goto v___jp_1468_;
}
}
}
else
{
lean_dec(v_exported_1445_);
v_exported_1469_ = v_fst_1429_;
goto v___jp_1468_;
}
v___jp_1448_:
{
if (lean_obj_tag(v_private_1447_) == 1)
{
lean_object* v_val_1451_; lean_object* v___x_1453_; 
v_val_1451_ = lean_ctor_get(v_private_1447_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v_private_1447_, 1);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v_val_1451_);
v___x_1453_ = v___x_1441_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_val_1451_);
v___x_1453_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_array_push(v_snd_1434_, v___x_1453_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1454_);
lean_ctor_set(v___x_1436_, 0, v_server_1450_);
v___x_1456_ = v___x_1436_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_server_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1456_);
lean_ctor_set(v___x_1431_, 0, v___y_1449_);
v___x_1458_ = v___x_1431_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___y_1449_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v_a_1423_ = v___x_1458_;
goto v___jp_1422_;
}
}
}
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_private_1447_);
lean_del_object(v___x_1441_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_server_1450_);
v___x_1463_ = v___x_1436_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_server_1450_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_snd_1434_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1463_);
lean_ctor_set(v___x_1431_, 0, v___y_1449_);
v___x_1465_ = v___x_1431_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___y_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
v_a_1423_ = v___x_1465_;
goto v___jp_1422_;
}
}
}
}
v___jp_1468_:
{
if (lean_obj_tag(v_server_1446_) == 1)
{
lean_object* v_val_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_val_1470_ = lean_ctor_get(v_server_1446_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_server_1446_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v_server_1446_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_val_1470_);
lean_dec(v_server_1446_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 0);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_val_1470_);
v___x_1475_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_array_push(v_fst_1433_, v___x_1475_);
v___y_1449_ = v_exported_1469_;
v_server_1450_ = v___x_1476_;
goto v___jp_1448_;
}
}
}
else
{
lean_dec(v_server_1446_);
v___y_1449_ = v_exported_1469_;
v_server_1450_ = v_fst_1433_;
goto v___jp_1448_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1527_; 
v_a_1489_ = lean_ctor_get(v_a_1438_, 0);
v_a_1490_ = lean_ctor_get(v_a_1438_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1492_ = v_a_1438_;
v_isShared_1493_ = v_isSharedCheck_1527_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_inc(v_a_1489_);
lean_dec(v_a_1438_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1527_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_exportEntry_x3f_1494_; lean_object* v___x_1495_; lean_object* v_exported_1496_; lean_object* v_server_1497_; lean_object* v_private_1498_; lean_object* v___y_1500_; lean_object* v_server_1501_; lean_object* v_exported_1520_; 
v_exportEntry_x3f_1494_ = lean_ctor_get(v_descr_1416_, 7);
lean_inc_ref(v_exportEntry_x3f_1494_);
lean_inc_ref(v_env_1417_);
v___x_1495_ = lean_apply_2(v_exportEntry_x3f_1494_, v_env_1417_, v_a_1490_);
v_exported_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_exported_1496_);
v_server_1497_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_server_1497_);
v_private_1498_ = lean_ctor_get(v___x_1495_, 2);
lean_inc(v_private_1498_);
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v_exported_1496_) == 1)
{
lean_object* v_val_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_val_1524_ = lean_ctor_get(v_exported_1496_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v_exported_1496_, 1);
lean_inc(v_a_1489_);
v___x_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1489_);
lean_ctor_set(v___x_1525_, 1, v_val_1524_);
v___x_1526_ = lean_array_push(v_fst_1429_, v___x_1525_);
v_exported_1520_ = v___x_1526_;
goto v___jp_1519_;
}
else
{
lean_dec(v_exported_1496_);
v_exported_1520_ = v_fst_1429_;
goto v___jp_1519_;
}
v___jp_1499_:
{
if (lean_obj_tag(v_private_1498_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1504_; 
v_val_1502_ = lean_ctor_get(v_private_1498_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_private_1498_, 1);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v_val_1502_);
v___x_1504_ = v___x_1492_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1489_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_val_1502_);
v___x_1504_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_array_push(v_snd_1434_, v___x_1504_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1505_);
lean_ctor_set(v___x_1436_, 0, v_server_1501_);
v___x_1507_ = v___x_1436_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_server_1501_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1507_);
lean_ctor_set(v___x_1431_, 0, v___y_1500_);
v___x_1509_ = v___x_1431_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___y_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
v_a_1423_ = v___x_1509_;
goto v___jp_1422_;
}
}
}
}
else
{
lean_object* v___x_1514_; 
lean_dec(v_private_1498_);
lean_del_object(v___x_1492_);
lean_dec(v_a_1489_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_server_1501_);
v___x_1514_ = v___x_1436_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_server_1501_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_snd_1434_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1514_);
lean_ctor_set(v___x_1431_, 0, v___y_1500_);
v___x_1516_ = v___x_1431_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___y_1500_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1423_ = v___x_1516_;
goto v___jp_1422_;
}
}
}
}
v___jp_1519_:
{
if (lean_obj_tag(v_server_1497_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_val_1521_ = lean_ctor_get(v_server_1497_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v_server_1497_, 1);
lean_inc(v_a_1489_);
v___x_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_a_1489_);
lean_ctor_set(v___x_1522_, 1, v_val_1521_);
v___x_1523_ = lean_array_push(v_fst_1433_, v___x_1522_);
v___y_1500_ = v_exported_1520_;
v_server_1501_ = v___x_1523_;
goto v___jp_1499_;
}
else
{
lean_dec(v_server_1497_);
v___y_1500_ = v_exported_1520_;
v_server_1501_ = v_fst_1433_;
goto v___jp_1499_;
}
}
}
}
}
}
}
v___jp_1422_:
{
size_t v___x_1424_; size_t v___x_1425_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1420_, v___x_1424_);
v_i_1420_ = v___x_1425_;
v_b_1421_ = v_a_1423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(lean_object* v_descr_1530_, lean_object* v_env_1531_, lean_object* v_as_1532_, lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_b_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1530_, v_env_1531_, v_as_1532_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1535_);
lean_dec_ref(v_as_1532_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(lean_object* v_descr_1546_, lean_object* v_env_1547_, lean_object* v_s_1548_){
_start:
{
lean_object* v_newEntries_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1566_; 
v_newEntries_1549_ = lean_ctor_get(v_s_1548_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_s_1548_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; 
v_unused_1567_ = lean_ctor_get(v_s_1548_, 1);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_s_1548_, 0);
lean_dec(v_unused_1568_);
v___x_1551_ = v_s_1548_;
v_isShared_1552_ = v_isSharedCheck_1566_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_newEntries_1549_);
lean_dec(v_s_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1566_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; size_t v_sz_1556_; size_t v___x_1557_; lean_object* v___x_1558_; lean_object* v_snd_1559_; lean_object* v_fst_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1564_; 
v___x_1553_ = lean_array_mk(v_newEntries_1549_);
v___x_1554_ = l_Array_reverse___redArg(v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2));
v_sz_1556_ = lean_array_size(v___x_1554_);
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1546_, v_env_1547_, v___x_1554_, v_sz_1556_, v___x_1557_, v___x_1555_);
lean_dec_ref(v___x_1554_);
v_snd_1559_ = lean_ctor_get(v___x_1558_, 1);
lean_inc(v_snd_1559_);
v_fst_1560_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_fst_1560_);
lean_dec_ref(v___x_1558_);
v_fst_1561_ = lean_ctor_get(v_snd_1559_, 0);
lean_inc(v_fst_1561_);
v_snd_1562_ = lean_ctor_get(v_snd_1559_, 1);
lean_inc(v_snd_1562_);
lean_dec(v_snd_1559_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 2, v_snd_1562_);
lean_ctor_set(v___x_1551_, 1, v_fst_1561_);
lean_ctor_set(v___x_1551_, 0, v_fst_1560_);
v___x_1564_ = v___x_1551_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_fst_1561_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_snd_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_00_u03c3_1571_, lean_object* v_descr_1572_, lean_object* v_env_1573_, lean_object* v_s_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_1572_, v_env_1573_, v_s_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(lean_object* v_00_u03b1_1576_, lean_object* v_00_u03b2_1577_, lean_object* v_00_u03c3_1578_, lean_object* v_descr_1579_, lean_object* v_env_1580_, lean_object* v_as_1581_, size_t v_sz_1582_, size_t v_i_1583_, lean_object* v_b_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_1579_, v_env_1580_, v_as_1581_, v_sz_1582_, v_i_1583_, v_b_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_00_u03c3_1588_, lean_object* v_descr_1589_, lean_object* v_env_1590_, lean_object* v_as_1591_, lean_object* v_sz_1592_, lean_object* v_i_1593_, lean_object* v_b_1594_){
_start:
{
size_t v_sz_boxed_1595_; size_t v_i_boxed_1596_; lean_object* v_res_1597_; 
v_sz_boxed_1595_ = lean_unbox_usize(v_sz_1592_);
lean_dec(v_sz_1592_);
v_i_boxed_1596_ = lean_unbox_usize(v_i_1593_);
lean_dec(v_i_1593_);
v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_1586_, v_00_u03b2_1587_, v_00_u03c3_1588_, v_descr_1589_, v_env_1590_, v_as_1591_, v_sz_boxed_1595_, v_i_boxed_1596_, v_b_1594_);
lean_dec_ref(v_as_1591_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(lean_object* v_x_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1));
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(lean_object* v_x_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_1603_, v___y_1604_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_x_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(lean_object* v_s_1607_, lean_object* v_x_1608_){
_start:
{
lean_inc_ref(v_s_1607_);
return v_s_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(lean_object* v_s_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_1609_, v_x_1610_);
lean_dec_ref(v_x_1610_);
lean_dec_ref(v_s_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0));
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_1617_, v_x_1618_);
lean_dec_ref(v_x_1618_);
lean_dec_ref(v_x_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_box(0);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(lean_object* v_x_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_1622_);
lean_dec_ref(v_x_1622_);
return v_res_1623_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5(void){
_start:
{
lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___f_1629_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3));
v___f_1630_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2));
v___f_1631_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1));
v___f_1632_ = ((lean_object*)(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0));
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4);
v___x_1635_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___x_1633_);
lean_ctor_set(v___x_1635_, 2, v___f_1632_);
lean_ctor_set(v___x_1635_, 3, v___f_1631_);
lean_ctor_set(v___x_1635_, 4, v___f_1630_);
lean_ctor_set(v___x_1635_, 5, v___f_1629_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default___redArg(lean_object* v_inst_1636_){
_start:
{
lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___f_1637_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0));
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1638_, 0, v_inst_1636_);
v___f_1639_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1));
v___f_1640_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2));
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3);
v___x_1643_ = ((lean_object*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4));
v___x_1644_ = 0;
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5, &l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__5);
v___x_1647_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1647_, 0, v___x_1641_);
lean_ctor_set(v___x_1647_, 1, v___x_1642_);
lean_ctor_set(v___x_1647_, 2, v___f_1637_);
lean_ctor_set(v___x_1647_, 3, v___f_1638_);
lean_ctor_set(v___x_1647_, 4, v___f_1639_);
lean_ctor_set(v___x_1647_, 5, v___f_1639_);
lean_ctor_set(v___x_1647_, 6, v___x_1643_);
lean_ctor_set(v___x_1647_, 7, v___f_1640_);
lean_ctor_set(v___x_1647_, 8, v___x_1645_);
lean_ctor_set(v___x_1647_, 9, v___x_1646_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*10, v___x_1644_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*10 + 1, v___x_1644_);
v___x_1648_ = lean_obj_once(&l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5, &l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once, _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension_default(lean_object* v_00_u03b1_1650_, lean_object* v_00_u03b2_1651_, lean_object* v_00_u03c3_1652_, lean_object* v_inst_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension___redArg(lean_object* v_inst_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* v_a_1657_, lean_object* v_inst_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_1658_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_));
v___x_1666_ = lean_st_mk_ref(v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0));
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_x_1672_);
lean_dec_ref(v_x_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(lean_object* v_s_1677_){
_start:
{
lean_object* v_newEntries_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_newEntries_1678_ = lean_ctor_get(v_s_1677_, 2);
v___x_1679_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___closed__1));
v___x_1680_ = l_List_lengthTR___redArg(v_newEntries_1678_);
v___x_1681_ = l_Nat_reprFast(v___x_1680_);
v___x_1682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1679_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(lean_object* v_s_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_s_1684_);
lean_dec_ref(v_s_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object* v_descr_1690_){
_start:
{
lean_object* v_name_1692_; uint8_t v_trackGen_1693_; uint8_t v_logWrites_1694_; lean_object* v_entryDecl_x3f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; 
v_name_1692_ = lean_ctor_get(v_descr_1690_, 0);
v_trackGen_1693_ = lean_ctor_get_uint8(v_descr_1690_, sizeof(void*)*10);
v_logWrites_1694_ = lean_ctor_get_uint8(v_descr_1690_, sizeof(void*)*10 + 1);
v_entryDecl_x3f_1695_ = lean_ctor_get(v_descr_1690_, 8);
v___f_1696_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0));
v___f_1697_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1));
if (v_logWrites_1694_ == 0)
{
goto v___jp_1698_;
}
else
{
if (lean_obj_tag(v_entryDecl_x3f_1695_) == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_inc(v_name_1692_);
lean_dec_ref(v_descr_1690_);
v___x_1729_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__2));
v___x_1730_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1692_, v_logWrites_1694_);
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = ((lean_object*)(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__3));
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
v___x_1734_ = lean_mk_io_user_error(v___x_1733_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
else
{
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_inc_ref_n(v_descr_1690_, 4);
v___x_1699_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___boxed), 5, 4);
lean_closure_set(v___x_1699_, 0, lean_box(0));
lean_closure_set(v___x_1699_, 1, lean_box(0));
lean_closure_set(v___x_1699_, 2, lean_box(0));
lean_closure_set(v___x_1699_, 3, v_descr_1690_);
v___x_1700_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___boxed), 7, 4);
lean_closure_set(v___x_1700_, 0, lean_box(0));
lean_closure_set(v___x_1700_, 1, lean_box(0));
lean_closure_set(v___x_1700_, 2, lean_box(0));
lean_closure_set(v___x_1700_, 3, v_descr_1690_);
v___x_1701_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn), 6, 4);
lean_closure_set(v___x_1701_, 0, lean_box(0));
lean_closure_set(v___x_1701_, 1, lean_box(0));
lean_closure_set(v___x_1701_, 2, lean_box(0));
lean_closure_set(v___x_1701_, 3, v_descr_1690_);
v___x_1702_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn), 6, 4);
lean_closure_set(v___x_1702_, 0, lean_box(0));
lean_closure_set(v___x_1702_, 1, lean_box(0));
lean_closure_set(v___x_1702_, 2, lean_box(0));
lean_closure_set(v___x_1702_, 3, v_descr_1690_);
v___x_1703_ = lean_box(2);
v___x_1704_ = lean_box(0);
lean_inc(v_name_1692_);
v___x_1705_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1705_, 0, v_name_1692_);
lean_ctor_set(v___x_1705_, 1, v___x_1699_);
lean_ctor_set(v___x_1705_, 2, v___x_1700_);
lean_ctor_set(v___x_1705_, 3, v___x_1701_);
lean_ctor_set(v___x_1705_, 4, v___x_1702_);
lean_ctor_set(v___x_1705_, 5, v___f_1697_);
lean_ctor_set(v___x_1705_, 6, v___x_1703_);
lean_ctor_set(v___x_1705_, 7, v___x_1704_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*8, v_trackGen_1693_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*8 + 1, v_logWrites_1694_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___f_1696_);
v___x_1707_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1720_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1720_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_descr_1690_);
lean_ctor_set(v___x_1712_, 1, v_a_1708_);
v___x_1713_ = l_Lean_scopedEnvExtensionsRef;
v___x_1714_ = lean_st_ref_take(v___x_1713_);
lean_inc_ref(v___x_1712_);
v___x_1715_ = lean_array_push(v___x_1714_, v___x_1712_);
v___x_1716_ = lean_st_ref_put(v___x_1713_, v___x_1715_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1712_);
v___x_1718_ = v___x_1710_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1712_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_descr_1690_);
v_a_1721_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1707_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1707_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(lean_object* v_descr_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_00_u03c3_1741_, lean_object* v_descr_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerScopedEnvExtensionUnsafe___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_00_u03c3_1747_, lean_object* v_descr_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_registerScopedEnvExtensionUnsafe(v_00_u03b1_1745_, v_00_u03b2_1746_, v_00_u03c3_1747_, v_descr_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0(lean_object* v_f_1751_, lean_object* v_ps_1752_){
_start:
{
lean_object* v_importedEntries_1753_; lean_object* v_state_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_importedEntries_1753_ = lean_ctor_get(v_ps_1752_, 0);
v_state_1754_ = lean_ctor_get(v_ps_1752_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_ps_1752_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v_ps_1752_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_state_1754_);
lean_inc(v_importedEntries_1753_);
lean_dec(v_ps_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_apply_1(v_f_1751_, v_state_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_importedEntries_1753_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(lean_object* v_as_1763_, size_t v_i_1764_, size_t v_stop_1765_, lean_object* v_b_1766_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_eq(v_i_1764_, v_stop_1765_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; 
v___x_1768_ = lean_array_uget_borrowed(v_as_1763_, v_i_1764_);
lean_inc(v___x_1768_);
v___x_1769_ = l_Lean_Environment_logDeclChange(v_b_1766_, v___x_1768_);
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = lean_usize_add(v_i_1764_, v___x_1770_);
v_i_1764_ = v___x_1771_;
v_b_1766_ = v___x_1769_;
goto _start;
}
else
{
return v_b_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0___boxed(lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_stop_1775_, lean_object* v_b_1776_){
_start:
{
size_t v_i_boxed_1777_; size_t v_stop_boxed_1778_; lean_object* v_res_1779_; 
v_i_boxed_1777_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_stop_boxed_1778_ = lean_unbox_usize(v_stop_1775_);
lean_dec(v_stop_1775_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_as_1773_, v_i_boxed_1777_, v_stop_boxed_1778_, v_b_1776_);
lean_dec_ref(v_as_1773_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(lean_object* v_ext_1780_, lean_object* v_env_1781_, uint8_t v_changed_1782_, lean_object* v_f_1783_, lean_object* v_changedDecls_1784_){
_start:
{
lean_object* v___f_1785_; uint8_t v___y_1787_; lean_object* v___y_1788_; 
v___f_1785_ = lean_alloc_closure((void*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1785_, 0, v_f_1783_);
if (v_changed_1782_ == 0)
{
v___y_1787_ = v_changed_1782_;
v___y_1788_ = v_env_1781_;
goto v___jp_1786_;
}
else
{
lean_object* v_descr_1794_; uint8_t v___x_1795_; 
v_descr_1794_ = lean_ctor_get(v_ext_1780_, 0);
v___x_1795_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_1794_);
if (v___x_1795_ == 0)
{
v___y_1787_ = v___x_1795_;
v___y_1788_ = v_env_1781_;
goto v___jp_1786_;
}
else
{
uint8_t v_logWrites_1796_; 
v_logWrites_1796_ = lean_ctor_get_uint8(v_descr_1794_, sizeof(void*)*10 + 1);
if (v_logWrites_1796_ == 0)
{
v___y_1787_ = v___x_1795_;
v___y_1788_ = v_env_1781_;
goto v___jp_1786_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_array_get_size(v_changedDecls_1784_);
v___x_1799_ = lean_nat_dec_lt(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
v___y_1787_ = v___x_1795_;
v___y_1788_ = v_env_1781_;
goto v___jp_1786_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1798_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes_spec__0(v_changedDecls_1784_, v___x_1800_, v___x_1801_, v_env_1781_);
v___y_1787_ = v___x_1795_;
v___y_1788_ = v___x_1802_;
goto v___jp_1786_;
}
}
}
}
v___jp_1786_:
{
lean_object* v_ext_1789_; lean_object* v_toEnvExtension_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_ext_1789_ = lean_ctor_get(v_ext_1780_, 1);
lean_inc_ref(v_ext_1789_);
lean_dec_ref(v_ext_1780_);
v_toEnvExtension_1790_ = lean_ctor_get(v_ext_1789_, 0);
lean_inc_ref(v_toEnvExtension_1790_);
lean_dec_ref(v_ext_1789_);
v___x_1791_ = lean_box(1);
v___x_1792_ = lean_box(0);
v___x_1793_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1790_, v___y_1788_, v___f_1785_, v___x_1791_, v___x_1792_, v___y_1787_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg___boxed(lean_object* v_ext_1803_, lean_object* v_env_1804_, lean_object* v_changed_1805_, lean_object* v_f_1806_, lean_object* v_changedDecls_1807_){
_start:
{
uint8_t v_changed_boxed_1808_; lean_object* v_res_1809_; 
v_changed_boxed_1808_ = lean_unbox(v_changed_1805_);
v_res_1809_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1803_, v_env_1804_, v_changed_boxed_1808_, v_f_1806_, v_changedDecls_1807_);
lean_dec_ref(v_changedDecls_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(lean_object* v_00_u03b1_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_00_u03c3_1812_, lean_object* v_ext_1813_, lean_object* v_env_1814_, uint8_t v_changed_1815_, lean_object* v_f_1816_, lean_object* v_changedDecls_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1813_, v_env_1814_, v_changed_1815_, v_f_1816_, v_changedDecls_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_00_u03c3_1821_, lean_object* v_ext_1822_, lean_object* v_env_1823_, lean_object* v_changed_1824_, lean_object* v_f_1825_, lean_object* v_changedDecls_1826_){
_start:
{
uint8_t v_changed_boxed_1827_; lean_object* v_res_1828_; 
v_changed_boxed_1827_ = lean_unbox(v_changed_1824_);
v_res_1828_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes(v_00_u03b1_1819_, v_00_u03b2_1820_, v_00_u03c3_1821_, v_ext_1822_, v_env_1823_, v_changed_boxed_1827_, v_f_1825_, v_changedDecls_1826_);
lean_dec_ref(v_changedDecls_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(uint8_t v___x_1829_, lean_object* v_s_1830_){
_start:
{
lean_object* v_stateStack_1831_; 
v_stateStack_1831_ = lean_ctor_get(v_s_1830_, 0);
if (lean_obj_tag(v_stateStack_1831_) == 0)
{
return v_s_1830_;
}
else
{
lean_object* v_head_1832_; lean_object* v_scopedEntries_1833_; lean_object* v_newEntries_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1854_; 
lean_inc_ref(v_stateStack_1831_);
v_head_1832_ = lean_ctor_get(v_stateStack_1831_, 0);
lean_inc(v_head_1832_);
v_scopedEntries_1833_ = lean_ctor_get(v_s_1830_, 1);
v_newEntries_1834_ = lean_ctor_get(v_s_1830_, 2);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_s_1830_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_s_1830_, 0);
lean_dec(v_unused_1855_);
v___x_1836_ = v_s_1830_;
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_newEntries_1834_);
lean_inc(v_scopedEntries_1833_);
lean_dec(v_s_1830_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_state_1838_; lean_object* v_activeScopes_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1852_; 
v_state_1838_ = lean_ctor_get(v_head_1832_, 0);
v_activeScopes_1839_ = lean_ctor_get(v_head_1832_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_head_1832_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v_head_1832_, 2);
lean_dec(v_unused_1853_);
v___x_1841_ = v_head_1832_;
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_activeScopes_1839_);
lean_inc(v_state_1838_);
lean_dec(v_head_1832_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1843_ = 1;
v___x_1844_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 2, v___x_1844_);
v___x_1846_ = v___x_1841_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_state_1838_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_activeScopes_1839_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3, v___x_1843_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3 + 1, v___x_1829_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v_stateStack_1831_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1847_);
v___x_1849_ = v___x_1836_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_scopedEntries_1833_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_newEntries_1834_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0___boxed(lean_object* v___x_1856_, lean_object* v_s_1857_){
_start:
{
uint8_t v___x_59__boxed_1858_; lean_object* v_res_1859_; 
v___x_59__boxed_1858_ = lean_unbox(v___x_1856_);
v_res_1859_ = l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(v___x_59__boxed_1858_, v_s_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object* v_ext_1863_, lean_object* v_env_1864_){
_start:
{
uint8_t v___x_1865_; lean_object* v___f_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = 0;
v___f_1866_ = ((lean_object*)(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0));
v___x_1867_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1868_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1863_, v_env_1864_, v___x_1865_, v___f_1866_, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_00_u03c3_1871_, lean_object* v_ext_1872_, lean_object* v_env_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_1872_, v_env_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(lean_object* v_tail_1875_, lean_object* v_s_1876_){
_start:
{
lean_object* v_scopedEntries_1877_; lean_object* v_newEntries_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_scopedEntries_1877_ = lean_ctor_get(v_s_1876_, 1);
v_newEntries_1878_ = lean_ctor_get(v_s_1876_, 2);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_s_1876_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_s_1876_, 0);
lean_dec(v_unused_1886_);
v___x_1880_ = v_s_1876_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_newEntries_1878_);
lean_inc(v_scopedEntries_1877_);
lean_dec(v_s_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_tail_1875_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_tail_1875_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_scopedEntries_1877_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_newEntries_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object* v_ext_1887_, lean_object* v_env_1888_){
_start:
{
lean_object* v_ext_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v_stateStack_1895_; 
v_ext_1889_ = lean_ctor_get(v_ext_1887_, 1);
v___x_1890_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_1891_ = lean_box(1);
v___x_1892_ = lean_box(0);
v___x_1893_ = 0;
lean_inc_ref(v_env_1888_);
v___x_1894_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1890_, v_ext_1889_, v_env_1888_, v___x_1891_, v___x_1892_, v___x_1893_);
v_stateStack_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_stateStack_1895_);
lean_dec(v___x_1894_);
if (lean_obj_tag(v_stateStack_1895_) == 1)
{
lean_object* v_tail_1896_; 
v_tail_1896_ = lean_ctor_get(v_stateStack_1895_, 1);
lean_inc(v_tail_1896_);
if (lean_obj_tag(v_tail_1896_) == 1)
{
lean_object* v_head_1897_; uint8_t v_scopeChanged_1898_; lean_object* v_scopeChangedDecls_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v_head_1897_ = lean_ctor_get(v_stateStack_1895_, 0);
lean_inc(v_head_1897_);
lean_dec_ref_known(v_stateStack_1895_, 2);
v_scopeChanged_1898_ = lean_ctor_get_uint8(v_head_1897_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1899_ = lean_ctor_get(v_head_1897_, 2);
lean_inc_ref(v_scopeChangedDecls_1899_);
lean_dec(v_head_1897_);
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1900_, 0, v_tail_1896_);
v___x_1901_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1887_, v_env_1888_, v_scopeChanged_1898_, v___f_1900_, v_scopeChangedDecls_1899_);
lean_dec_ref(v_scopeChangedDecls_1899_);
return v___x_1901_;
}
else
{
lean_dec_ref_known(v_stateStack_1895_, 2);
lean_dec(v_tail_1896_);
lean_dec_ref(v_ext_1887_);
return v_env_1888_;
}
}
else
{
lean_dec(v_stateStack_1895_);
lean_dec_ref(v_ext_1887_);
return v_env_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* v_00_u03b1_1902_, lean_object* v_00_u03b2_1903_, lean_object* v_00_u03c3_1904_, lean_object* v_ext_1905_, lean_object* v_env_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_1905_, v_env_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_zero_1910_; uint8_t v_isZero_1911_; 
v_zero_1910_ = lean_unsigned_to_nat(0u);
v_isZero_1911_ = lean_nat_dec_eq(v_a_1908_, v_zero_1910_);
if (v_isZero_1911_ == 1)
{
return v_a_1909_;
}
else
{
if (lean_obj_tag(v_a_1909_) == 0)
{
return v_a_1909_;
}
else
{
lean_object* v_head_1912_; lean_object* v_tail_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1934_; 
v_head_1912_ = lean_ctor_get(v_a_1909_, 0);
v_tail_1913_ = lean_ctor_get(v_a_1909_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1909_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1915_ = v_a_1909_;
v_isShared_1916_ = v_isSharedCheck_1934_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_tail_1913_);
lean_inc(v_head_1912_);
lean_dec(v_a_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1934_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_state_1917_; lean_object* v_activeScopes_1918_; uint8_t v_scopeChanged_1919_; lean_object* v_scopeChangedDecls_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1933_; 
v_state_1917_ = lean_ctor_get(v_head_1912_, 0);
v_activeScopes_1918_ = lean_ctor_get(v_head_1912_, 1);
v_scopeChanged_1919_ = lean_ctor_get_uint8(v_head_1912_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_1920_ = lean_ctor_get(v_head_1912_, 2);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_head_1912_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1922_ = v_head_1912_;
v_isShared_1923_ = v_isSharedCheck_1933_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_scopeChangedDecls_1920_);
lean_inc(v_activeScopes_1918_);
lean_inc(v_state_1917_);
lean_dec(v_head_1912_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1933_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_one_1924_; lean_object* v_n_1925_; lean_object* v___x_1927_; 
v_one_1924_ = lean_unsigned_to_nat(1u);
v_n_1925_ = lean_nat_sub(v_a_1908_, v_one_1924_);
if (v_isShared_1923_ == 0)
{
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_state_1917_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_activeScopes_1918_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_scopeChangedDecls_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*3 + 1, v_scopeChanged_1919_);
v___x_1927_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*3, v_isZero_1911_);
v___x_1928_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_1925_, v_tail_1913_);
lean_dec(v_n_1925_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1928_);
lean_ctor_set(v___x_1915_, 0, v___x_1927_);
v___x_1930_ = v___x_1915_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1935_, v_a_1936_);
lean_dec(v_a_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(lean_object* v_00_u03c3_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_a_1939_, v_a_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(lean_object* v_00_u03c3_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(v_00_u03c3_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(lean_object* v_depth_1946_, lean_object* v_s_1947_){
_start:
{
lean_object* v_stateStack_1948_; lean_object* v_scopedEntries_1949_; lean_object* v_newEntries_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_stateStack_1948_ = lean_ctor_get(v_s_1947_, 0);
v_scopedEntries_1949_ = lean_ctor_get(v_s_1947_, 1);
v_newEntries_1950_ = lean_ctor_get(v_s_1947_, 2);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_s_1947_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1952_ = v_s_1947_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_newEntries_1950_);
lean_inc(v_scopedEntries_1949_);
lean_inc(v_stateStack_1948_);
lean_dec(v_s_1947_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_1946_, v_stateStack_1948_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_scopedEntries_1949_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_newEntries_1950_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(lean_object* v_depth_1959_, lean_object* v_s_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_1959_, v_s_1960_);
lean_dec(v_depth_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(lean_object* v_ext_1962_, lean_object* v_env_1963_, lean_object* v_depth_1964_){
_start:
{
lean_object* v___f_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1965_, 0, v_depth_1964_);
v___x_1966_ = 0;
v___x_1967_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___x_1968_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_1962_, v_env_1963_, v___x_1966_, v___f_1965_, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_setDelimitsLocal(lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_00_u03c3_1971_, lean_object* v_ext_1972_, lean_object* v_env_1973_, lean_object* v_depth_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_ext_1972_, v_env_1973_, v_depth_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg(lean_object* v_ext_1978_, lean_object* v_b_1979_){
_start:
{
lean_object* v_descr_1980_; lean_object* v_entryDecl_x3f_1981_; 
v_descr_1980_ = lean_ctor_get(v_ext_1978_, 0);
lean_inc_ref(v_descr_1980_);
lean_dec_ref(v_ext_1978_);
v_entryDecl_x3f_1981_ = lean_ctor_get(v_descr_1980_, 8);
lean_inc(v_entryDecl_x3f_1981_);
lean_dec_ref(v_descr_1980_);
if (lean_obj_tag(v_entryDecl_x3f_1981_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
v_val_1982_ = lean_ctor_get(v_entryDecl_x3f_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_entryDecl_x3f_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v_entryDecl_x3f_1981_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v_entryDecl_x3f_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_apply_1(v_val_1982_, v_b_1979_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_entryDecl_x3f_1981_);
lean_dec(v_b_1979_);
v___x_1991_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog(lean_object* v_00_u03b1_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_00_u03c3_1994_, lean_object* v_ext_1995_, lean_object* v_b_1996_){
_start:
{
lean_object* v_descr_1997_; lean_object* v_entryDecl_x3f_1998_; 
v_descr_1997_ = lean_ctor_get(v_ext_1995_, 0);
lean_inc_ref(v_descr_1997_);
lean_dec_ref(v_ext_1995_);
v_entryDecl_x3f_1998_ = lean_ctor_get(v_descr_1997_, 8);
lean_inc(v_entryDecl_x3f_1998_);
lean_dec_ref(v_descr_1997_);
if (lean_obj_tag(v_entryDecl_x3f_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_val_1999_ = lean_ctor_get(v_entryDecl_x3f_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_entryDecl_x3f_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2001_ = v_entryDecl_x3f_1998_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v_entryDecl_x3f_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_apply_1(v_val_1999_, v_b_1996_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_entryDecl_x3f_1998_);
lean_dec(v_b_1996_);
v___x_2008_ = ((lean_object*)(l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_writeLog___redArg___closed__0));
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0(lean_object* v_addEntryFn_2009_, lean_object* v___x_2010_, lean_object* v_s_2011_){
_start:
{
lean_object* v_importedEntries_2012_; lean_object* v_state_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
v_importedEntries_2012_ = lean_ctor_get(v_s_2011_, 0);
v_state_2013_ = lean_ctor_get(v_s_2011_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_s_2011_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2015_ = v_s_2011_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_state_2013_);
lean_inc(v_importedEntries_2012_);
lean_dec(v_s_2011_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_state_2017_; lean_object* v___x_2019_; 
v_state_2017_ = lean_apply_2(v_addEntryFn_2009_, v_state_2013_, v___x_2010_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_state_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_importedEntries_2012_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_state_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object* v_ext_2022_, lean_object* v_env_2023_, lean_object* v_b_2024_){
_start:
{
lean_object* v_ext_2025_; lean_object* v_toEnvExtension_2026_; lean_object* v_descr_2027_; lean_object* v_addEntryFn_2028_; lean_object* v_asyncMode_2029_; uint8_t v_logWrites_2030_; lean_object* v_entryDecl_x3f_2031_; lean_object* v___x_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v_declName_2036_; 
v_ext_2025_ = lean_ctor_get(v_ext_2022_, 1);
lean_inc_ref(v_ext_2025_);
v_toEnvExtension_2026_ = lean_ctor_get(v_ext_2025_, 0);
lean_inc_ref(v_toEnvExtension_2026_);
v_descr_2027_ = lean_ctor_get(v_ext_2022_, 0);
lean_inc_ref(v_descr_2027_);
lean_dec_ref(v_ext_2022_);
v_addEntryFn_2028_ = lean_ctor_get(v_ext_2025_, 3);
lean_inc(v_addEntryFn_2028_);
lean_dec_ref(v_ext_2025_);
v_asyncMode_2029_ = lean_ctor_get(v_toEnvExtension_2026_, 2);
lean_inc(v_asyncMode_2029_);
v_logWrites_2030_ = lean_ctor_get_uint8(v_toEnvExtension_2026_, sizeof(void*)*6);
v_entryDecl_x3f_2031_ = lean_ctor_get(v_descr_2027_, 8);
lean_inc(v_entryDecl_x3f_2031_);
lean_dec_ref(v_descr_2027_);
lean_inc(v_b_2024_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_b_2024_);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2033_, 0, v_addEntryFn_2028_);
lean_closure_set(v___f_2033_, 1, v___x_2032_);
v___x_2034_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_2031_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2042_; 
v_val_2041_ = lean_ctor_get(v_entryDecl_x3f_2031_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v_entryDecl_x3f_2031_, 1);
v___x_2042_ = lean_apply_1(v_val_2041_, v_b_2024_);
v_declName_2036_ = v___x_2042_;
goto v___jp_2035_;
}
else
{
lean_dec(v_entryDecl_x3f_2031_);
lean_dec(v_b_2024_);
v_declName_2036_ = v___x_2034_;
goto v___jp_2035_;
}
v___jp_2035_:
{
uint8_t v___x_2037_; 
v___x_2037_ = 1;
if (v_logWrites_2030_ == 0)
{
lean_object* v___x_2038_; 
lean_dec(v_declName_2036_);
v___x_2038_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2026_, v_env_2023_, v___f_2033_, v_asyncMode_2029_, v___x_2034_, v___x_2037_);
lean_dec(v_asyncMode_2029_);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = l_Lean_Environment_logDeclChange(v_env_2023_, v_declName_2036_);
v___x_2040_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2026_, v___x_2039_, v___f_2033_, v_asyncMode_2029_, v___x_2034_, v___x_2037_);
lean_dec(v_asyncMode_2029_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* v_00_u03b1_2043_, lean_object* v_00_u03b2_2044_, lean_object* v_00_u03c3_2045_, lean_object* v_ext_2046_, lean_object* v_env_2047_, lean_object* v_b_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_2046_, v_env_2047_, v_b_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___redArg(lean_object* v_ext_2050_, lean_object* v_env_2051_, lean_object* v_namespaceName_2052_, lean_object* v_b_2053_){
_start:
{
lean_object* v_ext_2054_; lean_object* v_toEnvExtension_2055_; lean_object* v_descr_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2077_; 
v_ext_2054_ = lean_ctor_get(v_ext_2050_, 1);
lean_inc_ref(v_ext_2054_);
v_toEnvExtension_2055_ = lean_ctor_get(v_ext_2054_, 0);
lean_inc_ref(v_toEnvExtension_2055_);
v_descr_2056_ = lean_ctor_get(v_ext_2050_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_ext_2050_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_ext_2050_, 1);
lean_dec(v_unused_2078_);
v___x_2058_ = v_ext_2050_;
v_isShared_2059_ = v_isSharedCheck_2077_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_descr_2056_);
lean_dec(v_ext_2050_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2077_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_addEntryFn_2060_; lean_object* v_asyncMode_2061_; uint8_t v_logWrites_2062_; lean_object* v_entryDecl_x3f_2063_; lean_object* v___x_2065_; 
v_addEntryFn_2060_ = lean_ctor_get(v_ext_2054_, 3);
lean_inc(v_addEntryFn_2060_);
lean_dec_ref(v_ext_2054_);
v_asyncMode_2061_ = lean_ctor_get(v_toEnvExtension_2055_, 2);
lean_inc(v_asyncMode_2061_);
v_logWrites_2062_ = lean_ctor_get_uint8(v_toEnvExtension_2055_, sizeof(void*)*6);
v_entryDecl_x3f_2063_ = lean_ctor_get(v_descr_2056_, 8);
lean_inc(v_entryDecl_x3f_2063_);
lean_dec_ref(v_descr_2056_);
lean_inc(v_b_2053_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
lean_ctor_set(v___x_2058_, 1, v_b_2053_);
lean_ctor_set(v___x_2058_, 0, v_namespaceName_2052_);
v___x_2065_ = v___x_2058_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_namespaceName_2052_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_b_2053_);
v___x_2065_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v_declName_2069_; 
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2066_, 0, v_addEntryFn_2060_);
lean_closure_set(v___f_2066_, 1, v___x_2065_);
v___x_2067_ = lean_box(0);
if (lean_obj_tag(v_entryDecl_x3f_2063_) == 1)
{
lean_object* v_val_2074_; lean_object* v___x_2075_; 
v_val_2074_ = lean_ctor_get(v_entryDecl_x3f_2063_, 0);
lean_inc(v_val_2074_);
lean_dec_ref_known(v_entryDecl_x3f_2063_, 1);
v___x_2075_ = lean_apply_1(v_val_2074_, v_b_2053_);
v_declName_2069_ = v___x_2075_;
goto v___jp_2068_;
}
else
{
lean_dec(v_entryDecl_x3f_2063_);
lean_dec(v_b_2053_);
v_declName_2069_ = v___x_2067_;
goto v___jp_2068_;
}
v___jp_2068_:
{
uint8_t v___x_2070_; 
v___x_2070_ = 1;
if (v_logWrites_2062_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_declName_2069_);
v___x_2071_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2055_, v_env_2051_, v___f_2066_, v_asyncMode_2061_, v___x_2067_, v___x_2070_);
lean_dec(v_asyncMode_2061_);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = l_Lean_Environment_logDeclChange(v_env_2051_, v_declName_2069_);
v___x_2073_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2055_, v___x_2072_, v___f_2066_, v_asyncMode_2061_, v___x_2067_, v___x_2070_);
lean_dec(v_asyncMode_2061_);
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* v_00_u03b1_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_00_u03c3_2081_, lean_object* v_ext_2082_, lean_object* v_env_2083_, lean_object* v_namespaceName_2084_, lean_object* v_b_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2082_, v_env_2083_, v_namespaceName_2084_, v_b_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify___redArg(lean_object* v_ext_2087_, lean_object* v_states_2088_, lean_object* v_b_2089_){
_start:
{
if (lean_obj_tag(v_states_2088_) == 0)
{
lean_dec(v_b_2089_);
lean_dec_ref(v_ext_2087_);
return v_states_2088_;
}
else
{
lean_object* v_descr_2090_; lean_object* v_head_2091_; lean_object* v_tail_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2119_; 
v_descr_2090_ = lean_ctor_get(v_ext_2087_, 0);
v_head_2091_ = lean_ctor_get(v_states_2088_, 0);
v_tail_2092_ = lean_ctor_get(v_states_2088_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_states_2088_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2094_ = v_states_2088_;
v_isShared_2095_ = v_isSharedCheck_2119_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_tail_2092_);
lean_inc(v_head_2091_);
lean_dec(v_states_2088_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2119_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_addEntry_2096_; lean_object* v_state_2097_; lean_object* v_activeScopes_2098_; uint8_t v_delimitsLocal_2099_; uint8_t v_scopeChanged_2100_; lean_object* v_scopeChangedDecls_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2118_; 
v_addEntry_2096_ = lean_ctor_get(v_descr_2090_, 4);
v_state_2097_ = lean_ctor_get(v_head_2091_, 0);
v_activeScopes_2098_ = lean_ctor_get(v_head_2091_, 1);
v_delimitsLocal_2099_ = lean_ctor_get_uint8(v_head_2091_, sizeof(void*)*3);
v_scopeChanged_2100_ = lean_ctor_get_uint8(v_head_2091_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2101_ = lean_ctor_get(v_head_2091_, 2);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_head_2091_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2103_ = v_head_2091_;
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_scopeChangedDecls_2101_);
lean_inc(v_activeScopes_2098_);
lean_inc(v_state_2097_);
lean_dec(v_head_2091_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_inc(v_addEntry_2096_);
lean_inc(v_b_2089_);
v___x_2105_ = lean_apply_2(v_addEntry_2096_, v_state_2097_, v_b_2089_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_activeScopes_2098_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_scopeChangedDecls_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*3, v_delimitsLocal_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*3 + 1, v_scopeChanged_2100_);
v___x_2107_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v_top_2108_; uint8_t v_delimitsLocal_2109_; 
lean_inc(v_b_2089_);
lean_inc_ref(v_descr_2090_);
v_top_2108_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2090_, v___x_2107_, v_b_2089_);
v_delimitsLocal_2109_ = lean_ctor_get_uint8(v_top_2108_, sizeof(void*)*3);
if (v_delimitsLocal_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = l_Lean_stateStackModify___redArg(v_ext_2087_, v_tail_2092_, v_b_2089_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2110_);
lean_ctor_set(v___x_2094_, 0, v_top_2108_);
v___x_2112_ = v___x_2094_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_top_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_b_2089_);
lean_dec_ref(v_ext_2087_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_top_2108_);
v___x_2115_ = v___x_2094_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_top_2108_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_tail_2092_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_stateStackModify(lean_object* v_00_u03b1_2120_, lean_object* v_00_u03b2_2121_, lean_object* v_00_u03c3_2122_, lean_object* v_ext_2123_, lean_object* v_states_2124_, lean_object* v_b_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_stateStackModify___redArg(v_ext_2123_, v_states_2124_, v_b_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(lean_object* v_ext_2127_, lean_object* v_b_2128_, lean_object* v_ps_2129_){
_start:
{
lean_object* v_state_2130_; lean_object* v_importedEntries_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2149_; 
v_state_2130_ = lean_ctor_get(v_ps_2129_, 1);
v_importedEntries_2131_ = lean_ctor_get(v_ps_2129_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_ps_2129_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2133_ = v_ps_2129_;
v_isShared_2134_ = v_isSharedCheck_2149_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_state_2130_);
lean_inc(v_importedEntries_2131_);
lean_dec(v_ps_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2149_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_stateStack_2135_; lean_object* v_scopedEntries_2136_; lean_object* v_newEntries_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2148_; 
v_stateStack_2135_ = lean_ctor_get(v_state_2130_, 0);
v_scopedEntries_2136_ = lean_ctor_get(v_state_2130_, 1);
v_newEntries_2137_ = lean_ctor_get(v_state_2130_, 2);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_state_2130_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2139_ = v_state_2130_;
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_newEntries_2137_);
lean_inc(v_scopedEntries_2136_);
lean_inc(v_stateStack_2135_);
lean_dec(v_state_2130_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = l_Lean_stateStackModify___redArg(v_ext_2127_, v_stateStack_2135_, v_b_2128_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_scopedEntries_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_newEntries_2137_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2145_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2143_);
v___x_2145_ = v___x_2133_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_importedEntries_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___redArg(lean_object* v_ext_2150_, lean_object* v_env_2151_, lean_object* v_b_2152_){
_start:
{
lean_object* v_descr_2153_; lean_object* v_ext_2154_; lean_object* v_entryDecl_x3f_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v_declName_2161_; 
v_descr_2153_ = lean_ctor_get(v_ext_2150_, 0);
v_ext_2154_ = lean_ctor_get(v_ext_2150_, 1);
lean_inc_ref(v_ext_2154_);
v_entryDecl_x3f_2155_ = lean_ctor_get(v_descr_2153_, 8);
lean_inc(v_entryDecl_x3f_2155_);
lean_inc(v_b_2152_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2156_, 0, v_ext_2150_);
lean_closure_set(v___f_2156_, 1, v_b_2152_);
v___x_2157_ = lean_box(1);
v___x_2158_ = lean_box(0);
v___x_2159_ = 1;
if (lean_obj_tag(v_entryDecl_x3f_2155_) == 1)
{
lean_object* v_val_2167_; lean_object* v___x_2168_; 
v_val_2167_ = lean_ctor_get(v_entryDecl_x3f_2155_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v_entryDecl_x3f_2155_, 1);
v___x_2168_ = lean_apply_1(v_val_2167_, v_b_2152_);
v_declName_2161_ = v___x_2168_;
goto v___jp_2160_;
}
else
{
lean_dec(v_entryDecl_x3f_2155_);
lean_dec(v_b_2152_);
v_declName_2161_ = v___x_2158_;
goto v___jp_2160_;
}
v___jp_2160_:
{
lean_object* v_toEnvExtension_2162_; uint8_t v_logWrites_2163_; 
v_toEnvExtension_2162_ = lean_ctor_get(v_ext_2154_, 0);
lean_inc_ref(v_toEnvExtension_2162_);
lean_dec_ref(v_ext_2154_);
v_logWrites_2163_ = lean_ctor_get_uint8(v_toEnvExtension_2162_, sizeof(void*)*6);
if (v_logWrites_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_dec(v_declName_2161_);
v___x_2164_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2162_, v_env_2151_, v___f_2156_, v___x_2157_, v___x_2158_, v___x_2159_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = l_Lean_Environment_logDeclChange(v_env_2151_, v_declName_2161_);
v___x_2166_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2162_, v___x_2165_, v___f_2156_, v___x_2157_, v___x_2158_, v___x_2159_);
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* v_00_u03b1_2169_, lean_object* v_00_u03b2_2170_, lean_object* v_00_u03c3_2171_, lean_object* v_ext_2172_, lean_object* v_env_2173_, lean_object* v_b_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2172_, v_env_2173_, v_b_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object* v_env_2176_, lean_object* v_ext_2177_, lean_object* v_b_2178_, uint8_t v_kind_2179_, lean_object* v_namespaceName_2180_){
_start:
{
switch(v_kind_2179_)
{
case 0:
{
lean_object* v___x_2181_; 
lean_dec(v_namespaceName_2180_);
v___x_2181_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_2177_, v_env_2176_, v_b_2178_);
return v___x_2181_;
}
case 1:
{
lean_object* v___x_2182_; 
lean_dec(v_namespaceName_2180_);
v___x_2182_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_2177_, v_env_2176_, v_b_2178_);
return v___x_2182_;
}
default: 
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(v_ext_2177_, v_env_2176_, v_namespaceName_2180_, v_b_2178_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___redArg___boxed(lean_object* v_env_2184_, lean_object* v_ext_2185_, lean_object* v_b_2186_, lean_object* v_kind_2187_, lean_object* v_namespaceName_2188_){
_start:
{
uint8_t v_kind_boxed_2189_; lean_object* v_res_2190_; 
v_kind_boxed_2189_ = lean_unbox(v_kind_2187_);
v_res_2190_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2184_, v_ext_2185_, v_b_2186_, v_kind_boxed_2189_, v_namespaceName_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore(lean_object* v_00_u03b1_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_00_u03c3_2193_, lean_object* v_env_2194_, lean_object* v_ext_2195_, lean_object* v_b_2196_, uint8_t v_kind_2197_, lean_object* v_namespaceName_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2194_, v_ext_2195_, v_b_2196_, v_kind_2197_, v_namespaceName_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_addCore___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_00_u03c3_2202_, lean_object* v_env_2203_, lean_object* v_ext_2204_, lean_object* v_b_2205_, lean_object* v_kind_2206_, lean_object* v_namespaceName_2207_){
_start:
{
uint8_t v_kind_boxed_2208_; lean_object* v_res_2209_; 
v_kind_boxed_2208_ = lean_unbox(v_kind_2206_);
v_res_2209_ = l_Lean_ScopedEnvExtension_addCore(v_00_u03b1_2200_, v_00_u03b2_2201_, v_00_u03c3_2202_, v_env_2203_, v_ext_2204_, v_b_2205_, v_kind_boxed_2208_, v_namespaceName_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0(lean_object* v_ext_2210_, lean_object* v_b_2211_, uint8_t v_kind_2212_, lean_object* v_ns_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_x_2214_, v_ext_2210_, v_b_2211_, v_kind_2212_, v_ns_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(lean_object* v_ext_2216_, lean_object* v_b_2217_, lean_object* v_kind_2218_, lean_object* v_ns_2219_, lean_object* v_x_2220_){
_start:
{
uint8_t v_kind_boxed_2221_; lean_object* v_res_2222_; 
v_kind_boxed_2221_ = lean_unbox(v_kind_2218_);
v_res_2222_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(v_ext_2216_, v_b_2217_, v_kind_boxed_2221_, v_ns_2219_, v_x_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1(lean_object* v_inst_2223_, lean_object* v_ext_2224_, lean_object* v_b_2225_, uint8_t v_kind_2226_, lean_object* v_ns_2227_){
_start:
{
lean_object* v_modifyEnv_2228_; lean_object* v___x_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; 
v_modifyEnv_2228_ = lean_ctor_get(v_inst_2223_, 1);
lean_inc(v_modifyEnv_2228_);
lean_dec_ref(v_inst_2223_);
v___x_2229_ = lean_box(v_kind_2226_);
v___f_2230_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2230_, 0, v_ext_2224_);
lean_closure_set(v___f_2230_, 1, v_b_2225_);
lean_closure_set(v___f_2230_, 2, v___x_2229_);
lean_closure_set(v___f_2230_, 3, v_ns_2227_);
v___x_2231_ = lean_apply_1(v_modifyEnv_2228_, v___f_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(lean_object* v_inst_2232_, lean_object* v_ext_2233_, lean_object* v_b_2234_, lean_object* v_kind_2235_, lean_object* v_ns_2236_){
_start:
{
uint8_t v_kind_boxed_2237_; lean_object* v_res_2238_; 
v_kind_boxed_2237_ = lean_unbox(v_kind_2235_);
v_res_2238_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(v_inst_2232_, v_ext_2233_, v_b_2234_, v_kind_boxed_2237_, v_ns_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg(lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_ext_2242_, lean_object* v_b_2243_, uint8_t v_kind_2244_){
_start:
{
lean_object* v_toBind_2245_; lean_object* v_getCurrNamespace_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; 
v_toBind_2245_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2245_);
lean_dec_ref(v_inst_2239_);
v_getCurrNamespace_2246_ = lean_ctor_get(v_inst_2240_, 0);
lean_inc(v_getCurrNamespace_2246_);
lean_dec_ref(v_inst_2240_);
v___x_2247_ = lean_box(v_kind_2244_);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2248_, 0, v_inst_2241_);
lean_closure_set(v___f_2248_, 1, v_ext_2242_);
lean_closure_set(v___f_2248_, 2, v_b_2243_);
lean_closure_set(v___f_2248_, 3, v___x_2247_);
v___x_2249_ = lean_apply_4(v_toBind_2245_, lean_box(0), lean_box(0), v_getCurrNamespace_2246_, v___f_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___redArg___boxed(lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_ext_2253_, lean_object* v_b_2254_, lean_object* v_kind_2255_){
_start:
{
uint8_t v_kind_boxed_2256_; lean_object* v_res_2257_; 
v_kind_boxed_2256_ = lean_unbox(v_kind_2255_);
v_res_2257_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2250_, v_inst_2251_, v_inst_2252_, v_ext_2253_, v_b_2254_, v_kind_boxed_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add(lean_object* v_m_2258_, lean_object* v_00_u03b1_2259_, lean_object* v_00_u03b2_2260_, lean_object* v_00_u03c3_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_ext_2265_, lean_object* v_b_2266_, uint8_t v_kind_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_ScopedEnvExtension_add___redArg(v_inst_2262_, v_inst_2263_, v_inst_2264_, v_ext_2265_, v_b_2266_, v_kind_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___boxed(lean_object* v_m_2269_, lean_object* v_00_u03b1_2270_, lean_object* v_00_u03b2_2271_, lean_object* v_00_u03c3_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_ext_2276_, lean_object* v_b_2277_, lean_object* v_kind_2278_){
_start:
{
uint8_t v_kind_boxed_2279_; lean_object* v_res_2280_; 
v_kind_boxed_2279_ = lean_unbox(v_kind_2278_);
v_res_2280_ = l_Lean_ScopedEnvExtension_add(v_m_2269_, v_00_u03b1_2270_, v_00_u03b2_2271_, v_00_u03c3_2272_, v_inst_2273_, v_inst_2274_, v_inst_2275_, v_ext_2276_, v_b_2277_, v_kind_boxed_2279_);
return v_res_2280_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2284_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__2));
v___x_2285_ = lean_unsigned_to_nat(16u);
v___x_2286_ = lean_unsigned_to_nat(303u);
v___x_2287_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__1));
v___x_2288_ = ((lean_object*)(l_Lean_ScopedEnvExtension_getState___redArg___closed__0));
v___x_2289_ = l_mkPanicMessageWithDecl(v___x_2288_, v___x_2287_, v___x_2286_, v___x_2285_, v___x_2284_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object* v_inst_2290_, lean_object* v_ext_2291_, lean_object* v_env_2292_, lean_object* v_asyncMode_2293_, uint8_t v_genRecorded_2294_){
_start:
{
lean_object* v_ext_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_stateStack_2299_; 
v_ext_2295_ = lean_ctor_get(v_ext_2291_, 1);
v___x_2296_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2297_ = lean_box(0);
v___x_2298_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2296_, v_ext_2295_, v_env_2292_, v_asyncMode_2293_, v___x_2297_, v_genRecorded_2294_);
v_stateStack_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_stateStack_2299_);
lean_dec(v___x_2298_);
if (lean_obj_tag(v_stateStack_2299_) == 1)
{
lean_object* v_head_2300_; lean_object* v_state_2301_; 
v_head_2300_ = lean_ctor_get(v_stateStack_2299_, 0);
lean_inc(v_head_2300_);
lean_dec_ref_known(v_stateStack_2299_, 2);
v_state_2301_ = lean_ctor_get(v_head_2300_, 0);
lean_inc(v_state_2301_);
lean_dec(v_head_2300_);
return v_state_2301_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec(v_stateStack_2299_);
v___x_2302_ = lean_obj_once(&l_Lean_ScopedEnvExtension_getState___redArg___closed__3, &l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3);
v___x_2303_ = l_panic___redArg(v_inst_2290_, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___redArg___boxed(lean_object* v_inst_2304_, lean_object* v_ext_2305_, lean_object* v_env_2306_, lean_object* v_asyncMode_2307_, lean_object* v_genRecorded_2308_){
_start:
{
uint8_t v_genRecorded_boxed_2309_; lean_object* v_res_2310_; 
v_genRecorded_boxed_2309_ = lean_unbox(v_genRecorded_2308_);
v_res_2310_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2304_, v_ext_2305_, v_env_2306_, v_asyncMode_2307_, v_genRecorded_boxed_2309_);
lean_dec(v_asyncMode_2307_);
lean_dec_ref(v_ext_2305_);
lean_dec(v_inst_2304_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* v_00_u03c3_2311_, lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_inst_2314_, lean_object* v_ext_2315_, lean_object* v_env_2316_, lean_object* v_asyncMode_2317_, uint8_t v_genRecorded_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_ScopedEnvExtension_getState___redArg(v_inst_2314_, v_ext_2315_, v_env_2316_, v_asyncMode_2317_, v_genRecorded_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_getState___boxed(lean_object* v_00_u03c3_2320_, lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b2_2322_, lean_object* v_inst_2323_, lean_object* v_ext_2324_, lean_object* v_env_2325_, lean_object* v_asyncMode_2326_, lean_object* v_genRecorded_2327_){
_start:
{
uint8_t v_genRecorded_boxed_2328_; lean_object* v_res_2329_; 
v_genRecorded_boxed_2328_ = lean_unbox(v_genRecorded_2327_);
v_res_2329_ = l_Lean_ScopedEnvExtension_getState(v_00_u03c3_2320_, v_00_u03b1_2321_, v_00_u03b2_2322_, v_inst_2323_, v_ext_2324_, v_env_2325_, v_asyncMode_2326_, v_genRecorded_boxed_2328_);
lean_dec(v_asyncMode_2326_);
lean_dec_ref(v_ext_2324_);
lean_dec(v_inst_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(lean_object* v___y_2330_, lean_object* v_tail_2331_, lean_object* v_s_2332_){
_start:
{
lean_object* v_scopedEntries_2333_; lean_object* v_newEntries_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
v_scopedEntries_2333_ = lean_ctor_get(v_s_2332_, 1);
v_newEntries_2334_ = lean_ctor_get(v_s_2332_, 2);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_s_2332_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_s_2332_, 0);
lean_dec(v_unused_2343_);
v___x_2336_ = v_s_2332_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_newEntries_2334_);
lean_inc(v_scopedEntries_2333_);
lean_dec(v_s_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___y_2330_);
lean_ctor_set(v___x_2338_, 1, v_tail_2331_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_scopedEntries_2333_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_newEntries_2334_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(lean_object* v_ext_2344_, lean_object* v_as_2345_, size_t v_i_2346_, size_t v_stop_2347_, lean_object* v_b_2348_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_eq(v_i_2346_, v_stop_2347_);
if (v___x_2349_ == 0)
{
lean_object* v_descr_2350_; lean_object* v_addEntry_2351_; lean_object* v_state_2352_; lean_object* v_activeScopes_2353_; uint8_t v_delimitsLocal_2354_; uint8_t v_scopeChanged_2355_; lean_object* v_scopeChangedDecls_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2369_; 
v_descr_2350_ = lean_ctor_get(v_ext_2344_, 0);
v_addEntry_2351_ = lean_ctor_get(v_descr_2350_, 4);
v_state_2352_ = lean_ctor_get(v_b_2348_, 0);
v_activeScopes_2353_ = lean_ctor_get(v_b_2348_, 1);
v_delimitsLocal_2354_ = lean_ctor_get_uint8(v_b_2348_, sizeof(void*)*3);
v_scopeChanged_2355_ = lean_ctor_get_uint8(v_b_2348_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2356_ = lean_ctor_get(v_b_2348_, 2);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_b_2348_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2358_ = v_b_2348_;
v_isShared_2359_ = v_isSharedCheck_2369_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_scopeChangedDecls_2356_);
lean_inc(v_activeScopes_2353_);
lean_inc(v_state_2352_);
lean_dec(v_b_2348_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2369_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2360_ = lean_array_uget_borrowed(v_as_2345_, v_i_2346_);
lean_inc(v_addEntry_2351_);
lean_inc(v___x_2360_);
v___x_2361_ = lean_apply_2(v_addEntry_2351_, v_state_2352_, v___x_2360_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2361_);
v___x_2363_ = v___x_2358_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_activeScopes_2353_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_scopeChangedDecls_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*3, v_delimitsLocal_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*3 + 1, v_scopeChanged_2355_);
v___x_2363_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; 
lean_inc(v___x_2360_);
lean_inc_ref(v_descr_2350_);
v___x_2364_ = l_Lean_ScopedEnvExtension_Descr_noteScopeChange___redArg(v_descr_2350_, v___x_2363_, v___x_2360_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2346_, v___x_2365_);
v_i_2346_ = v___x_2366_;
v_b_2348_ = v___x_2364_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_ext_2344_);
return v_b_2348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg___boxed(lean_object* v_ext_2370_, lean_object* v_as_2371_, lean_object* v_i_2372_, lean_object* v_stop_2373_, lean_object* v_b_2374_){
_start:
{
size_t v_i_boxed_2375_; size_t v_stop_boxed_2376_; lean_object* v_res_2377_; 
v_i_boxed_2375_ = lean_unbox_usize(v_i_2372_);
lean_dec(v_i_2372_);
v_stop_boxed_2376_ = lean_unbox_usize(v_stop_2373_);
lean_dec(v_stop_2373_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2370_, v_as_2371_, v_i_boxed_2375_, v_stop_boxed_2376_, v_b_2374_);
lean_dec_ref(v_as_2371_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(lean_object* v_ext_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
lean_object* v_cs_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_cs_2381_ = lean_ctor_get(v_x_2379_, 0);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_array_get_size(v_cs_2381_);
v___x_2384_ = lean_nat_dec_lt(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_dec_ref(v_ext_2378_);
return v_x_2380_;
}
else
{
size_t v___x_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = lean_usize_of_nat(v___x_2383_);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2378_, v_cs_2381_, v___x_2385_, v___x_2386_, v_x_2380_);
return v___x_2387_;
}
}
else
{
lean_object* v_vs_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_vs_2388_ = lean_ctor_get(v_x_2379_, 0);
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_array_get_size(v_vs_2388_);
v___x_2391_ = lean_nat_dec_lt(v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_dec_ref(v_ext_2378_);
return v_x_2380_;
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = lean_usize_of_nat(v___x_2390_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2378_, v_vs_2388_, v___x_2392_, v___x_2393_, v_x_2380_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(lean_object* v_ext_2395_, lean_object* v_as_2396_, size_t v_i_2397_, size_t v_stop_2398_, lean_object* v_b_2399_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_usize_dec_eq(v_i_2397_, v_stop_2398_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; size_t v___x_2403_; size_t v___x_2404_; 
v___x_2401_ = lean_array_uget_borrowed(v_as_2396_, v_i_2397_);
lean_inc_ref(v_ext_2395_);
v___x_2402_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2395_, v___x_2401_, v_b_2399_);
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2397_, v___x_2403_);
v_i_2397_ = v___x_2404_;
v_b_2399_ = v___x_2402_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2395_);
return v_b_2399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ext_2406_, lean_object* v_as_2407_, lean_object* v_i_2408_, lean_object* v_stop_2409_, lean_object* v_b_2410_){
_start:
{
size_t v_i_boxed_2411_; size_t v_stop_boxed_2412_; lean_object* v_res_2413_; 
v_i_boxed_2411_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_stop_boxed_2412_ = lean_unbox_usize(v_stop_2409_);
lean_dec(v_stop_2409_);
v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2406_, v_as_2407_, v_i_boxed_2411_, v_stop_boxed_2412_, v_b_2410_);
lean_dec_ref(v_as_2407_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg___boxed(lean_object* v_ext_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2414_, v_x_2415_, v_x_2416_);
lean_dec_ref(v_x_2415_);
return v_res_2417_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(lean_object* v_ext_2419_, lean_object* v_x_2420_, size_t v_x_2421_, size_t v_x_2422_, lean_object* v_x_2423_){
_start:
{
if (lean_obj_tag(v_x_2420_) == 0)
{
lean_object* v_cs_2424_; lean_object* v___x_2425_; size_t v___x_2426_; lean_object* v_j_2427_; lean_object* v___x_2428_; size_t v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_cs_2424_ = lean_ctor_get(v_x_2420_, 0);
v___x_2425_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2426_ = lean_usize_shift_right(v_x_2421_, v_x_2422_);
v_j_2427_ = lean_usize_to_nat(v___x_2426_);
v___x_2428_ = lean_array_get_borrowed(v___x_2425_, v_cs_2424_, v_j_2427_);
v___x_2429_ = ((size_t)1ULL);
v___x_2430_ = lean_usize_shift_left(v___x_2429_, v_x_2422_);
v___x_2431_ = lean_usize_sub(v___x_2430_, v___x_2429_);
v___x_2432_ = lean_usize_land(v_x_2421_, v___x_2431_);
v___x_2433_ = ((size_t)5ULL);
v___x_2434_ = lean_usize_sub(v_x_2422_, v___x_2433_);
lean_inc_ref(v_ext_2419_);
v___x_2435_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2419_, v___x_2428_, v___x_2432_, v___x_2434_, v_x_2423_);
v___x_2436_ = lean_unsigned_to_nat(1u);
v___x_2437_ = lean_nat_add(v_j_2427_, v___x_2436_);
lean_dec(v_j_2427_);
v___x_2438_ = lean_array_get_size(v_cs_2424_);
v___x_2439_ = lean_nat_dec_lt(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec(v___x_2437_);
lean_dec_ref(v_ext_2419_);
return v___x_2435_;
}
else
{
size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = lean_usize_of_nat(v___x_2437_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_usize_of_nat(v___x_2438_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2419_, v_cs_2424_, v___x_2440_, v___x_2441_, v___x_2435_);
return v___x_2442_;
}
}
else
{
lean_object* v_vs_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v_vs_2443_ = lean_ctor_get(v_x_2420_, 0);
v___x_2444_ = lean_usize_to_nat(v_x_2421_);
v___x_2445_ = lean_array_get_size(v_vs_2443_);
v___x_2446_ = lean_nat_dec_lt(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec(v___x_2444_);
lean_dec_ref(v_ext_2419_);
return v_x_2423_;
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_usize_of_nat(v___x_2444_);
lean_dec(v___x_2444_);
v___x_2448_ = lean_usize_of_nat(v___x_2445_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2419_, v_vs_2443_, v___x_2447_, v___x_2448_, v_x_2423_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___boxed(lean_object* v_ext_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_x_2454_){
_start:
{
size_t v_x_2633__boxed_2455_; size_t v_x_2634__boxed_2456_; lean_object* v_res_2457_; 
v_x_2633__boxed_2455_ = lean_unbox_usize(v_x_2452_);
lean_dec(v_x_2452_);
v_x_2634__boxed_2456_ = lean_unbox_usize(v_x_2453_);
lean_dec(v_x_2453_);
v_res_2457_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2450_, v_x_2451_, v_x_2633__boxed_2455_, v_x_2634__boxed_2456_, v_x_2454_);
lean_dec_ref(v_x_2451_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(lean_object* v_ext_2458_, lean_object* v_t_2459_, lean_object* v_init_2460_, lean_object* v_start_2461_){
_start:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_nat_dec_eq(v_start_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v_root_2464_; lean_object* v_tail_2465_; size_t v_shift_2466_; lean_object* v_tailOff_2467_; uint8_t v___x_2468_; 
v_root_2464_ = lean_ctor_get(v_t_2459_, 0);
v_tail_2465_ = lean_ctor_get(v_t_2459_, 1);
v_shift_2466_ = lean_ctor_get_usize(v_t_2459_, 4);
v_tailOff_2467_ = lean_ctor_get(v_t_2459_, 3);
v___x_2468_ = lean_nat_dec_le(v_tailOff_2467_, v_start_2461_);
if (v___x_2468_ == 0)
{
size_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2469_ = lean_usize_of_nat(v_start_2461_);
lean_inc_ref(v_ext_2458_);
v___x_2470_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2458_, v_root_2464_, v___x_2469_, v_shift_2466_, v_init_2460_);
v___x_2471_ = lean_array_get_size(v_tail_2465_);
v___x_2472_ = lean_nat_dec_lt(v___x_2462_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v_ext_2458_);
return v___x_2470_;
}
else
{
size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((size_t)0ULL);
v___x_2474_ = lean_usize_of_nat(v___x_2471_);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2458_, v_tail_2465_, v___x_2473_, v___x_2474_, v___x_2470_);
return v___x_2475_;
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = lean_nat_sub(v_start_2461_, v_tailOff_2467_);
v___x_2477_ = lean_array_get_size(v_tail_2465_);
v___x_2478_ = lean_nat_dec_lt(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_dec(v___x_2476_);
lean_dec_ref(v_ext_2458_);
return v_init_2460_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_usize_of_nat(v___x_2476_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_usize_of_nat(v___x_2477_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2458_, v_tail_2465_, v___x_2479_, v___x_2480_, v_init_2460_);
return v___x_2481_;
}
}
}
else
{
lean_object* v_root_2482_; lean_object* v_tail_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_root_2482_ = lean_ctor_get(v_t_2459_, 0);
v_tail_2483_ = lean_ctor_get(v_t_2459_, 1);
lean_inc_ref(v_ext_2458_);
v___x_2484_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2458_, v_root_2482_, v_init_2460_);
v___x_2485_ = lean_array_get_size(v_tail_2483_);
v___x_2486_ = lean_nat_dec_lt(v___x_2462_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v_ext_2458_);
return v___x_2484_;
}
else
{
size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = lean_usize_of_nat(v___x_2485_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2458_, v_tail_2483_, v___x_2487_, v___x_2488_, v___x_2484_);
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg___boxed(lean_object* v_ext_2490_, lean_object* v_t_2491_, lean_object* v_init_2492_, lean_object* v_start_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2490_, v_t_2491_, v_init_2492_, v_start_2493_);
lean_dec(v_start_2493_);
lean_dec_ref(v_t_2491_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(lean_object* v_val_2495_, lean_object* v_as_2496_, size_t v_i_2497_, size_t v_stop_2498_, lean_object* v_b_2499_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_eq(v_i_2497_, v_stop_2498_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; 
v___x_2501_ = lean_array_uget_borrowed(v_as_2496_, v_i_2497_);
lean_inc_ref(v_val_2495_);
lean_inc(v___x_2501_);
v___x_2502_ = lean_apply_1(v_val_2495_, v___x_2501_);
v___x_2503_ = lean_array_push(v_b_2499_, v___x_2502_);
v___x_2504_ = ((size_t)1ULL);
v___x_2505_ = lean_usize_add(v_i_2497_, v___x_2504_);
v_i_2497_ = v___x_2505_;
v_b_2499_ = v___x_2503_;
goto _start;
}
else
{
lean_dec_ref(v_val_2495_);
return v_b_2499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(lean_object* v_val_2507_, lean_object* v_as_2508_, lean_object* v_i_2509_, lean_object* v_stop_2510_, lean_object* v_b_2511_){
_start:
{
size_t v_i_boxed_2512_; size_t v_stop_boxed_2513_; lean_object* v_res_2514_; 
v_i_boxed_2512_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_stop_boxed_2513_ = lean_unbox_usize(v_stop_2510_);
lean_dec(v_stop_2510_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2507_, v_as_2508_, v_i_boxed_2512_, v_stop_boxed_2513_, v_b_2511_);
lean_dec_ref(v_as_2508_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(lean_object* v_val_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_cs_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_cs_2518_ = lean_ctor_get(v_x_2516_, 0);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_array_get_size(v_cs_2518_);
v___x_2521_ = lean_nat_dec_lt(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_dec_ref(v_val_2515_);
return v_x_2517_;
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2520_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2515_, v_cs_2518_, v___x_2522_, v___x_2523_, v_x_2517_);
return v___x_2524_;
}
}
else
{
lean_object* v_vs_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v_vs_2525_ = lean_ctor_get(v_x_2516_, 0);
v___x_2526_ = lean_unsigned_to_nat(0u);
v___x_2527_ = lean_array_get_size(v_vs_2525_);
v___x_2528_ = lean_nat_dec_lt(v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_dec_ref(v_val_2515_);
return v_x_2517_;
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2527_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2515_, v_vs_2525_, v___x_2529_, v___x_2530_, v_x_2517_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(lean_object* v_val_2532_, lean_object* v_as_2533_, size_t v_i_2534_, size_t v_stop_2535_, lean_object* v_b_2536_){
_start:
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_usize_dec_eq(v_i_2534_, v_stop_2535_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; 
v___x_2538_ = lean_array_uget_borrowed(v_as_2533_, v_i_2534_);
lean_inc_ref(v_val_2532_);
v___x_2539_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2532_, v___x_2538_, v_b_2536_);
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2534_, v___x_2540_);
v_i_2534_ = v___x_2541_;
v_b_2536_ = v___x_2539_;
goto _start;
}
else
{
lean_dec_ref(v_val_2532_);
return v_b_2536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_val_2543_, lean_object* v_as_2544_, lean_object* v_i_2545_, lean_object* v_stop_2546_, lean_object* v_b_2547_){
_start:
{
size_t v_i_boxed_2548_; size_t v_stop_boxed_2549_; lean_object* v_res_2550_; 
v_i_boxed_2548_ = lean_unbox_usize(v_i_2545_);
lean_dec(v_i_2545_);
v_stop_boxed_2549_ = lean_unbox_usize(v_stop_2546_);
lean_dec(v_stop_2546_);
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2543_, v_as_2544_, v_i_boxed_2548_, v_stop_boxed_2549_, v_b_2547_);
lean_dec_ref(v_as_2544_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg___boxed(lean_object* v_val_2551_, lean_object* v_x_2552_, lean_object* v_x_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2551_, v_x_2552_, v_x_2553_);
lean_dec_ref(v_x_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(lean_object* v_val_2555_, lean_object* v_x_2556_, size_t v_x_2557_, size_t v_x_2558_, lean_object* v_x_2559_){
_start:
{
if (lean_obj_tag(v_x_2556_) == 0)
{
lean_object* v_cs_2560_; lean_object* v___x_2561_; size_t v___x_2562_; lean_object* v_j_2563_; lean_object* v___x_2564_; size_t v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_cs_2560_ = lean_ctor_get(v_x_2556_, 0);
v___x_2561_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg___closed__0);
v___x_2562_ = lean_usize_shift_right(v_x_2557_, v_x_2558_);
v_j_2563_ = lean_usize_to_nat(v___x_2562_);
v___x_2564_ = lean_array_get_borrowed(v___x_2561_, v_cs_2560_, v_j_2563_);
v___x_2565_ = ((size_t)1ULL);
v___x_2566_ = lean_usize_shift_left(v___x_2565_, v_x_2558_);
v___x_2567_ = lean_usize_sub(v___x_2566_, v___x_2565_);
v___x_2568_ = lean_usize_land(v_x_2557_, v___x_2567_);
v___x_2569_ = ((size_t)5ULL);
v___x_2570_ = lean_usize_sub(v_x_2558_, v___x_2569_);
lean_inc_ref(v_val_2555_);
v___x_2571_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2555_, v___x_2564_, v___x_2568_, v___x_2570_, v_x_2559_);
v___x_2572_ = lean_unsigned_to_nat(1u);
v___x_2573_ = lean_nat_add(v_j_2563_, v___x_2572_);
lean_dec(v_j_2563_);
v___x_2574_ = lean_array_get_size(v_cs_2560_);
v___x_2575_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_dec(v___x_2573_);
lean_dec_ref(v_val_2555_);
return v___x_2571_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_usize_of_nat(v___x_2573_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_usize_of_nat(v___x_2574_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2555_, v_cs_2560_, v___x_2576_, v___x_2577_, v___x_2571_);
return v___x_2578_;
}
}
else
{
lean_object* v_vs_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_vs_2579_ = lean_ctor_get(v_x_2556_, 0);
v___x_2580_ = lean_usize_to_nat(v_x_2557_);
v___x_2581_ = lean_array_get_size(v_vs_2579_);
v___x_2582_ = lean_nat_dec_lt(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_dec(v___x_2580_);
lean_dec_ref(v_val_2555_);
return v_x_2559_;
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_usize_of_nat(v___x_2580_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_usize_of_nat(v___x_2581_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2555_, v_vs_2579_, v___x_2583_, v___x_2584_, v_x_2559_);
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(lean_object* v_val_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
size_t v_x_2811__boxed_2591_; size_t v_x_2812__boxed_2592_; lean_object* v_res_2593_; 
v_x_2811__boxed_2591_ = lean_unbox_usize(v_x_2588_);
lean_dec(v_x_2588_);
v_x_2812__boxed_2592_ = lean_unbox_usize(v_x_2589_);
lean_dec(v_x_2589_);
v_res_2593_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2586_, v_x_2587_, v_x_2811__boxed_2591_, v_x_2812__boxed_2592_, v_x_2590_);
lean_dec_ref(v_x_2587_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(lean_object* v_val_2594_, lean_object* v_t_2595_, lean_object* v_init_2596_, lean_object* v_start_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2599_ = lean_nat_dec_eq(v_start_2597_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v_root_2600_; lean_object* v_tail_2601_; size_t v_shift_2602_; lean_object* v_tailOff_2603_; uint8_t v___x_2604_; 
v_root_2600_ = lean_ctor_get(v_t_2595_, 0);
v_tail_2601_ = lean_ctor_get(v_t_2595_, 1);
v_shift_2602_ = lean_ctor_get_usize(v_t_2595_, 4);
v_tailOff_2603_ = lean_ctor_get(v_t_2595_, 3);
v___x_2604_ = lean_nat_dec_le(v_tailOff_2603_, v_start_2597_);
if (v___x_2604_ == 0)
{
size_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2605_ = lean_usize_of_nat(v_start_2597_);
lean_inc_ref(v_val_2594_);
v___x_2606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2594_, v_root_2600_, v___x_2605_, v_shift_2602_, v_init_2596_);
v___x_2607_ = lean_array_get_size(v_tail_2601_);
v___x_2608_ = lean_nat_dec_lt(v___x_2598_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec_ref(v_val_2594_);
return v___x_2606_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2607_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2594_, v_tail_2601_, v___x_2609_, v___x_2610_, v___x_2606_);
return v___x_2611_;
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = lean_nat_sub(v_start_2597_, v_tailOff_2603_);
v___x_2613_ = lean_array_get_size(v_tail_2601_);
v___x_2614_ = lean_nat_dec_lt(v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2612_);
lean_dec_ref(v_val_2594_);
return v_init_2596_;
}
else
{
size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_usize_of_nat(v___x_2612_);
lean_dec(v___x_2612_);
v___x_2616_ = lean_usize_of_nat(v___x_2613_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2594_, v_tail_2601_, v___x_2615_, v___x_2616_, v_init_2596_);
return v___x_2617_;
}
}
}
else
{
lean_object* v_root_2618_; lean_object* v_tail_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_root_2618_ = lean_ctor_get(v_t_2595_, 0);
v_tail_2619_ = lean_ctor_get(v_t_2595_, 1);
lean_inc_ref(v_val_2594_);
v___x_2620_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2594_, v_root_2618_, v_init_2596_);
v___x_2621_ = lean_array_get_size(v_tail_2619_);
v___x_2622_ = lean_nat_dec_lt(v___x_2598_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v_val_2594_);
return v___x_2620_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = lean_usize_of_nat(v___x_2621_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2594_, v_tail_2619_, v___x_2623_, v___x_2624_, v___x_2620_);
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(lean_object* v_val_2626_, lean_object* v_t_2627_, lean_object* v_init_2628_, lean_object* v_start_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2626_, v_t_2627_, v_init_2628_, v_start_2629_);
lean_dec(v_start_2629_);
lean_dec_ref(v_t_2627_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object* v_ext_2631_, lean_object* v_env_2632_, lean_object* v_namespaceName_2633_){
_start:
{
lean_object* v_descr_2634_; lean_object* v_ext_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v_s_2640_; lean_object* v_stateStack_2641_; 
v_descr_2634_ = lean_ctor_get(v_ext_2631_, 0);
v_ext_2635_ = lean_ctor_get(v_ext_2631_, 1);
v___x_2636_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
v___x_2637_ = lean_box(1);
v___x_2638_ = lean_box(0);
v___x_2639_ = 0;
lean_inc_ref(v_env_2632_);
v_s_2640_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2636_, v_ext_2635_, v_env_2632_, v___x_2637_, v___x_2638_, v___x_2639_);
v_stateStack_2641_ = lean_ctor_get(v_s_2640_, 0);
lean_inc(v_stateStack_2641_);
if (lean_obj_tag(v_stateStack_2641_) == 1)
{
lean_object* v_head_2642_; lean_object* v_scopedEntries_2643_; lean_object* v_tail_2644_; lean_object* v_state_2645_; lean_object* v_activeScopes_2646_; uint8_t v_delimitsLocal_2647_; uint8_t v_scopeChanged_2648_; lean_object* v_scopeChangedDecls_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2684_; 
v_head_2642_ = lean_ctor_get(v_stateStack_2641_, 0);
lean_inc(v_head_2642_);
v_scopedEntries_2643_ = lean_ctor_get(v_s_2640_, 1);
lean_inc_ref(v_scopedEntries_2643_);
lean_dec(v_s_2640_);
v_tail_2644_ = lean_ctor_get(v_stateStack_2641_, 1);
lean_inc(v_tail_2644_);
lean_dec_ref_known(v_stateStack_2641_, 2);
v_state_2645_ = lean_ctor_get(v_head_2642_, 0);
v_activeScopes_2646_ = lean_ctor_get(v_head_2642_, 1);
v_delimitsLocal_2647_ = lean_ctor_get_uint8(v_head_2642_, sizeof(void*)*3);
v_scopeChanged_2648_ = lean_ctor_get_uint8(v_head_2642_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2649_ = lean_ctor_get(v_head_2642_, 2);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_head_2642_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2651_ = v_head_2642_;
v_isShared_2652_ = v_isSharedCheck_2684_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_scopeChangedDecls_2649_);
lean_inc(v_activeScopes_2646_);
lean_inc(v_state_2645_);
lean_dec(v_head_2642_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2684_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
uint8_t v___x_2653_; 
v___x_2653_ = l_Lean_NameSet_contains(v_activeScopes_2646_, v_namespaceName_2633_);
if (v___x_2653_ == 0)
{
lean_object* v_activeScopes_2654_; lean_object* v_bs_x3f_2655_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2663_; lean_object* v___y_2666_; 
lean_inc(v_namespaceName_2633_);
v_activeScopes_2654_ = l_Lean_NameSet_insert(v_activeScopes_2646_, v_namespaceName_2633_);
v_bs_x3f_2655_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_2643_, v_namespaceName_2633_);
lean_dec(v_namespaceName_2633_);
lean_dec_ref(v_scopedEntries_2643_);
if (lean_obj_tag(v_bs_x3f_2655_) == 1)
{
lean_object* v_val_2674_; uint8_t v___x_2675_; lean_object* v___x_2677_; 
v_val_2674_ = lean_ctor_get(v_bs_x3f_2655_, 0);
v___x_2675_ = 1;
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_activeScopes_2654_);
v___x_2677_ = v___x_2651_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_state_2645_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_activeScopes_2654_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_scopeChangedDecls_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2680_, sizeof(void*)*3 + 1, v_scopeChanged_2648_);
v___x_2677_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*3, v___x_2675_);
v___x_2678_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ext_2631_);
v___x_2679_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2631_, v_val_2674_, v___x_2677_, v___x_2678_);
v___y_2666_ = v___x_2679_;
goto v___jp_2665_;
}
}
else
{
lean_object* v___x_2682_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_activeScopes_2654_);
v___x_2682_ = v___x_2651_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_state_2645_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_activeScopes_2654_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_scopeChangedDecls_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*3, v_delimitsLocal_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*3 + 1, v_scopeChanged_2648_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
v___y_2666_ = v___x_2682_;
goto v___jp_2665_;
}
}
v___jp_2656_:
{
if (lean_obj_tag(v_bs_x3f_2655_) == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2631_, v_env_2632_, v___x_2653_, v___y_2657_, v___y_2658_);
lean_dec_ref(v___y_2658_);
return v___x_2659_;
}
else
{
uint8_t v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref_known(v_bs_x3f_2655_, 1);
v___x_2660_ = 1;
v___x_2661_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_modifyScopes___redArg(v_ext_2631_, v_env_2632_, v___x_2660_, v___y_2657_, v___y_2658_);
lean_dec_ref(v___y_2658_);
return v___x_2661_;
}
}
v___jp_2662_:
{
lean_object* v___x_2664_; 
v___x_2664_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
v___y_2657_ = v___y_2663_;
v___y_2658_ = v___x_2664_;
goto v___jp_2656_;
}
v___jp_2665_:
{
lean_object* v___f_2667_; 
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2667_, 0, v___y_2666_);
lean_closure_set(v___f_2667_, 1, v_tail_2644_);
if (lean_obj_tag(v_bs_x3f_2655_) == 1)
{
lean_object* v_entryDecl_x3f_2668_; 
v_entryDecl_x3f_2668_ = lean_ctor_get(v_descr_2634_, 8);
if (lean_obj_tag(v_entryDecl_x3f_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v_val_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_val_2669_ = lean_ctor_get(v_bs_x3f_2655_, 0);
v_val_2670_ = lean_ctor_get(v_entryDecl_x3f_2668_, 0);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = ((lean_object*)(l_Lean_ScopedEnvExtension_mkInitial___redArg___closed__0));
lean_inc(v_val_2670_);
v___x_2673_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2670_, v_val_2669_, v___x_2672_, v___x_2671_);
v___y_2657_ = v___f_2667_;
v___y_2658_ = v___x_2673_;
goto v___jp_2656_;
}
else
{
v___y_2663_ = v___f_2667_;
goto v___jp_2662_;
}
}
else
{
v___y_2663_ = v___f_2667_;
goto v___jp_2662_;
}
}
}
else
{
lean_del_object(v___x_2651_);
lean_dec_ref(v_scopeChangedDecls_2649_);
lean_dec(v_activeScopes_2646_);
lean_dec(v_state_2645_);
lean_dec(v_tail_2644_);
lean_dec_ref(v_scopedEntries_2643_);
lean_dec(v_namespaceName_2633_);
lean_dec_ref(v_ext_2631_);
return v_env_2632_;
}
}
}
else
{
lean_dec(v_stateStack_2641_);
lean_dec(v_s_2640_);
lean_dec(v_namespaceName_2633_);
lean_dec_ref(v_ext_2631_);
return v_env_2632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* v_00_u03b1_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_00_u03c3_2687_, lean_object* v_ext_2688_, lean_object* v_env_2689_, lean_object* v_namespaceName_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_ext_2688_, v_env_2689_, v_namespaceName_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(lean_object* v_00_u03b2_2692_, lean_object* v_val_2693_, lean_object* v_t_2694_, lean_object* v_init_2695_, lean_object* v_start_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_val_2693_, v_t_2694_, v_init_2695_, v_start_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(lean_object* v_00_u03b2_2698_, lean_object* v_val_2699_, lean_object* v_t_2700_, lean_object* v_init_2701_, lean_object* v_start_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(v_00_u03b2_2698_, v_val_2699_, v_t_2700_, v_init_2701_, v_start_2702_);
lean_dec(v_start_2702_);
lean_dec_ref(v_t_2700_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(lean_object* v_00_u03b2_2704_, lean_object* v_00_u03c3_2705_, lean_object* v_00_u03b1_2706_, lean_object* v_ext_2707_, lean_object* v_t_2708_, lean_object* v_init_2709_, lean_object* v_start_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___redArg(v_ext_2707_, v_t_2708_, v_init_2709_, v_start_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1___boxed(lean_object* v_00_u03b2_2712_, lean_object* v_00_u03c3_2713_, lean_object* v_00_u03b1_2714_, lean_object* v_ext_2715_, lean_object* v_t_2716_, lean_object* v_init_2717_, lean_object* v_start_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1(v_00_u03b2_2712_, v_00_u03c3_2713_, v_00_u03b1_2714_, v_ext_2715_, v_t_2716_, v_init_2717_, v_start_2718_);
lean_dec(v_start_2718_);
lean_dec_ref(v_t_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(lean_object* v_00_u03b2_2720_, lean_object* v_val_2721_, lean_object* v_x_2722_, size_t v_x_2723_, size_t v_x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_val_2721_, v_x_2722_, v_x_2723_, v_x_2724_, v_x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2727_, lean_object* v_val_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
size_t v_x_3015__boxed_2733_; size_t v_x_3016__boxed_2734_; lean_object* v_res_2735_; 
v_x_3015__boxed_2733_ = lean_unbox_usize(v_x_2730_);
lean_dec(v_x_2730_);
v_x_3016__boxed_2734_ = lean_unbox_usize(v_x_2731_);
lean_dec(v_x_2731_);
v_res_2735_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_2727_, v_val_2728_, v_x_2729_, v_x_3015__boxed_2733_, v_x_3016__boxed_2734_, v_x_2732_);
lean_dec_ref(v_x_2729_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(lean_object* v_00_u03b2_2736_, lean_object* v_val_2737_, lean_object* v_as_2738_, size_t v_i_2739_, size_t v_stop_2740_, lean_object* v_b_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_val_2737_, v_as_2738_, v_i_2739_, v_stop_2740_, v_b_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2743_, lean_object* v_val_2744_, lean_object* v_as_2745_, lean_object* v_i_2746_, lean_object* v_stop_2747_, lean_object* v_b_2748_){
_start:
{
size_t v_i_boxed_2749_; size_t v_stop_boxed_2750_; lean_object* v_res_2751_; 
v_i_boxed_2749_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_stop_boxed_2750_ = lean_unbox_usize(v_stop_2747_);
lean_dec(v_stop_2747_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_2743_, v_val_2744_, v_as_2745_, v_i_boxed_2749_, v_stop_boxed_2750_, v_b_2748_);
lean_dec_ref(v_as_2745_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(lean_object* v_00_u03b2_2752_, lean_object* v_val_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___redArg(v_val_2753_, v_x_2754_, v_x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2757_, lean_object* v_val_2758_, lean_object* v_x_2759_, lean_object* v_x_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__2(v_00_u03b2_2757_, v_val_2758_, v_x_2759_, v_x_2760_);
lean_dec_ref(v_x_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(lean_object* v_00_u03b2_2762_, lean_object* v_00_u03c3_2763_, lean_object* v_00_u03b1_2764_, lean_object* v_ext_2765_, lean_object* v_x_2766_, size_t v_x_2767_, size_t v_x_2768_, lean_object* v_x_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___redArg(v_ext_2765_, v_x_2766_, v_x_2767_, v_x_2768_, v_x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2771_, lean_object* v_00_u03c3_2772_, lean_object* v_00_u03b1_2773_, lean_object* v_ext_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
size_t v_x_3047__boxed_2779_; size_t v_x_3048__boxed_2780_; lean_object* v_res_2781_; 
v_x_3047__boxed_2779_ = lean_unbox_usize(v_x_2776_);
lean_dec(v_x_2776_);
v_x_3048__boxed_2780_ = lean_unbox_usize(v_x_2777_);
lean_dec(v_x_2777_);
v_res_2781_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4(v_00_u03b2_2771_, v_00_u03c3_2772_, v_00_u03b1_2773_, v_ext_2774_, v_x_2775_, v_x_3047__boxed_2779_, v_x_3048__boxed_2780_, v_x_2778_);
lean_dec_ref(v_x_2775_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(lean_object* v_00_u03b2_2782_, lean_object* v_00_u03c3_2783_, lean_object* v_00_u03b1_2784_, lean_object* v_ext_2785_, lean_object* v_as_2786_, size_t v_i_2787_, size_t v_stop_2788_, lean_object* v_b_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___redArg(v_ext_2785_, v_as_2786_, v_i_2787_, v_stop_2788_, v_b_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2791_, lean_object* v_00_u03c3_2792_, lean_object* v_00_u03b1_2793_, lean_object* v_ext_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_){
_start:
{
size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_i_boxed_2799_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__5(v_00_u03b2_2791_, v_00_u03c3_2792_, v_00_u03b1_2793_, v_ext_2794_, v_as_2795_, v_i_boxed_2799_, v_stop_boxed_2800_, v_b_2798_);
lean_dec_ref(v_as_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(lean_object* v_00_u03b2_2802_, lean_object* v_00_u03c3_2803_, lean_object* v_00_u03b1_2804_, lean_object* v_ext_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___redArg(v_ext_2805_, v_x_2806_, v_x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_00_u03c3_2810_, lean_object* v_00_u03b1_2811_, lean_object* v_ext_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__6(v_00_u03b2_2809_, v_00_u03c3_2810_, v_00_u03b1_2811_, v_ext_2812_, v_x_2813_, v_x_2814_);
lean_dec_ref(v_x_2813_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2816_, lean_object* v_val_2817_, lean_object* v_as_2818_, size_t v_i_2819_, size_t v_stop_2820_, lean_object* v_b_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_val_2817_, v_as_2818_, v_i_2819_, v_stop_2820_, v_b_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2823_, lean_object* v_val_2824_, lean_object* v_as_2825_, lean_object* v_i_2826_, lean_object* v_stop_2827_, lean_object* v_b_2828_){
_start:
{
size_t v_i_boxed_2829_; size_t v_stop_boxed_2830_; lean_object* v_res_2831_; 
v_i_boxed_2829_ = lean_unbox_usize(v_i_2826_);
lean_dec(v_i_2826_);
v_stop_boxed_2830_ = lean_unbox_usize(v_stop_2827_);
lean_dec(v_stop_2827_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_2823_, v_val_2824_, v_as_2825_, v_i_boxed_2829_, v_stop_boxed_2830_, v_b_2828_);
lean_dec_ref(v_as_2825_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_2832_, lean_object* v_00_u03c3_2833_, lean_object* v_00_u03b1_2834_, lean_object* v_ext_2835_, lean_object* v_as_2836_, size_t v_i_2837_, size_t v_stop_2838_, lean_object* v_b_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___redArg(v_ext_2835_, v_as_2836_, v_i_2837_, v_stop_2838_, v_b_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2841_, lean_object* v_00_u03c3_2842_, lean_object* v_00_u03b1_2843_, lean_object* v_ext_2844_, lean_object* v_as_2845_, lean_object* v_i_2846_, lean_object* v_stop_2847_, lean_object* v_b_2848_){
_start:
{
size_t v_i_boxed_2849_; size_t v_stop_boxed_2850_; lean_object* v_res_2851_; 
v_i_boxed_2849_ = lean_unbox_usize(v_i_2846_);
lean_dec(v_i_2846_);
v_stop_boxed_2850_ = lean_unbox_usize(v_stop_2847_);
lean_dec(v_stop_2847_);
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_ScopedEnvExtension_activateScoped_spec__1_spec__4_spec__6(v_00_u03b2_2841_, v_00_u03c3_2842_, v_00_u03b1_2843_, v_ext_2844_, v_as_2845_, v_i_boxed_2849_, v_stop_boxed_2850_, v_b_2848_);
lean_dec_ref(v_as_2845_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(lean_object* v_f_2852_, lean_object* v_descr_2853_, lean_object* v_ps_2854_){
_start:
{
lean_object* v_state_2855_; lean_object* v_stateStack_2856_; 
v_state_2855_ = lean_ctor_get(v_ps_2854_, 1);
lean_inc(v_state_2855_);
v_stateStack_2856_ = lean_ctor_get(v_state_2855_, 0);
lean_inc(v_stateStack_2856_);
if (lean_obj_tag(v_stateStack_2856_) == 1)
{
lean_object* v_head_2857_; lean_object* v_importedEntries_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2900_; 
v_head_2857_ = lean_ctor_get(v_stateStack_2856_, 0);
lean_inc(v_head_2857_);
v_importedEntries_2858_ = lean_ctor_get(v_ps_2854_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_ps_2854_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v_ps_2854_, 1);
lean_dec(v_unused_2901_);
v___x_2860_ = v_ps_2854_;
v_isShared_2861_ = v_isSharedCheck_2900_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_importedEntries_2858_);
lean_dec(v_ps_2854_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2900_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_scopedEntries_2862_; lean_object* v_newEntries_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2898_; 
v_scopedEntries_2862_ = lean_ctor_get(v_state_2855_, 1);
v_newEntries_2863_ = lean_ctor_get(v_state_2855_, 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_state_2855_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v_state_2855_, 0);
lean_dec(v_unused_2899_);
v___x_2865_ = v_state_2855_;
v_isShared_2866_ = v_isSharedCheck_2898_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_newEntries_2863_);
lean_inc(v_scopedEntries_2862_);
lean_dec(v_state_2855_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2898_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v_tail_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2896_; 
v_tail_2867_ = lean_ctor_get(v_stateStack_2856_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_stateStack_2856_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v_stateStack_2856_, 0);
lean_dec(v_unused_2897_);
v___x_2869_ = v_stateStack_2856_;
v_isShared_2870_ = v_isSharedCheck_2896_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_tail_2867_);
lean_dec(v_stateStack_2856_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2896_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_state_2871_; lean_object* v_activeScopes_2872_; uint8_t v_delimitsLocal_2873_; uint8_t v_scopeChanged_2874_; lean_object* v_scopeChangedDecls_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2895_; 
v_state_2871_ = lean_ctor_get(v_head_2857_, 0);
v_activeScopes_2872_ = lean_ctor_get(v_head_2857_, 1);
v_delimitsLocal_2873_ = lean_ctor_get_uint8(v_head_2857_, sizeof(void*)*3);
v_scopeChanged_2874_ = lean_ctor_get_uint8(v_head_2857_, sizeof(void*)*3 + 1);
v_scopeChangedDecls_2875_ = lean_ctor_get(v_head_2857_, 2);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_head_2857_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2877_ = v_head_2857_;
v_isShared_2878_ = v_isSharedCheck_2895_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_scopeChangedDecls_2875_);
lean_inc(v_activeScopes_2872_);
lean_inc(v_state_2871_);
lean_dec(v_head_2857_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2895_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
uint8_t v___y_2880_; 
if (v_scopeChanged_2874_ == 0)
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_ScopedEnvExtension_Descr_tracksScopes___redArg(v_descr_2853_);
v___y_2880_ = v___x_2894_;
goto v___jp_2879_;
}
else
{
v___y_2880_ = v_scopeChanged_2874_;
goto v___jp_2879_;
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_apply_1(v_f_2852_, v_state_2871_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2881_);
v___x_2883_ = v___x_2877_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_activeScopes_2872_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_scopeChangedDecls_2875_);
lean_ctor_set_uint8(v_reuseFailAlloc_2893_, sizeof(void*)*3, v_delimitsLocal_2873_);
v___x_2883_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*3 + 1, v___y_2880_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2883_);
v___x_2885_ = v___x_2869_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_tail_2867_);
v___x_2885_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2887_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2885_);
v___x_2887_ = v___x_2865_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_scopedEntries_2862_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_newEntries_2863_);
v___x_2887_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2887_);
v___x_2889_ = v___x_2860_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_importedEntries_2858_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
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
lean_object* v_importedEntries_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_stateStack_2856_);
lean_dec(v_f_2852_);
v_importedEntries_2902_ = lean_ctor_get(v_ps_2854_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_ps_2854_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; 
v_unused_2910_ = lean_ctor_get(v_ps_2854_, 1);
lean_dec(v_unused_2910_);
v___x_2904_ = v_ps_2854_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_importedEntries_2902_);
lean_dec(v_ps_2854_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_importedEntries_2902_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_state_2855_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed(lean_object* v_f_2911_, lean_object* v_descr_2912_, lean_object* v_ps_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(v_f_2911_, v_descr_2912_, v_ps_2913_);
lean_dec_ref(v_descr_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object* v_ext_2915_, lean_object* v_env_2916_, lean_object* v_f_2917_){
_start:
{
lean_object* v_ext_2918_; lean_object* v_toEnvExtension_2919_; lean_object* v_descr_2920_; lean_object* v_asyncMode_2921_; uint8_t v_logWrites_2922_; lean_object* v___f_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_ext_2918_ = lean_ctor_get(v_ext_2915_, 1);
v_toEnvExtension_2919_ = lean_ctor_get(v_ext_2918_, 0);
lean_inc_ref(v_toEnvExtension_2919_);
v_descr_2920_ = lean_ctor_get(v_ext_2915_, 0);
lean_inc_ref(v_descr_2920_);
lean_dec_ref(v_ext_2915_);
v_asyncMode_2921_ = lean_ctor_get(v_toEnvExtension_2919_, 2);
lean_inc(v_asyncMode_2921_);
v_logWrites_2922_ = lean_ctor_get_uint8(v_toEnvExtension_2919_, sizeof(void*)*6);
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2923_, 0, v_f_2917_);
lean_closure_set(v___f_2923_, 1, v_descr_2920_);
v___x_2924_ = lean_box(0);
v___x_2925_ = 1;
if (v_logWrites_2922_ == 0)
{
lean_object* v___x_2926_; 
v___x_2926_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2919_, v_env_2916_, v___f_2923_, v_asyncMode_2921_, v___x_2924_, v___x_2925_);
lean_dec(v_asyncMode_2921_);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_inc_ref(v_toEnvExtension_2919_);
v___x_2927_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2919_, v_env_2916_);
lean_dec_ref(v_env_2916_);
v___x_2928_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2919_, v___x_2927_, v___f_2923_, v_asyncMode_2921_, v___x_2924_, v___x_2925_);
lean_dec(v_asyncMode_2921_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_modifyState(lean_object* v_00_u03b1_2929_, lean_object* v_00_u03b2_2930_, lean_object* v_00_u03c3_2931_, lean_object* v_ext_2932_, lean_object* v_env_2933_, lean_object* v_f_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2932_, v_env_2933_, v_f_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__0(lean_object* v_toPure_2936_, lean_object* v_____s_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_apply_2(v_toPure_2936_, lean_box(0), v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__1(lean_object* v___x_2940_, lean_object* v_toPure_2941_, lean_object* v_r_2942_){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2940_);
v___x_2944_ = lean_apply_2(v_toPure_2941_, lean_box(0), v___x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__2(lean_object* v_inst_2945_, lean_object* v_toBind_2946_, lean_object* v___f_2947_, lean_object* v_a_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_modifyEnv_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_modifyEnv_2951_ = lean_ctor_get(v_inst_2945_, 1);
lean_inc(v_modifyEnv_2951_);
lean_dec_ref(v_inst_2945_);
v___x_2952_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_2952_, 0, lean_box(0));
lean_closure_set(v___x_2952_, 1, lean_box(0));
lean_closure_set(v___x_2952_, 2, lean_box(0));
lean_closure_set(v___x_2952_, 3, v_a_2948_);
v___x_2953_ = lean_apply_1(v_modifyEnv_2951_, v___x_2952_);
v___x_2954_ = lean_apply_4(v_toBind_2946_, lean_box(0), lean_box(0), v___x_2953_, v___f_2947_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg___lam__3(lean_object* v_toPure_2955_, lean_object* v_inst_2956_, lean_object* v_toBind_2957_, lean_object* v_inst_2958_, lean_object* v___f_2959_, lean_object* v_____do__lift_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___f_2962_; lean_object* v___f_2963_; size_t v_sz_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2961_ = lean_box(0);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2962_, 0, v___x_2961_);
lean_closure_set(v___f_2962_, 1, v_toPure_2955_);
lean_inc(v_toBind_2957_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2963_, 0, v_inst_2956_);
lean_closure_set(v___f_2963_, 1, v_toBind_2957_);
lean_closure_set(v___f_2963_, 2, v___f_2962_);
v_sz_2964_ = lean_array_size(v_____do__lift_2960_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2958_, v_____do__lift_2960_, v___f_2963_, v_sz_2964_, v___x_2965_, v___x_2961_);
v___x_2967_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2966_, v___f_2959_);
return v___x_2967_;
}
}
static lean_object* _init_l_Lean_pushScope___redArg___closed__0(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_scopedEnvExtensionsRef;
v___x_2969_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2969_, 0, lean_box(0));
lean_closure_set(v___x_2969_, 1, lean_box(0));
lean_closure_set(v___x_2969_, 2, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___redArg(lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_){
_start:
{
lean_object* v_toApplicative_2973_; lean_object* v_toBind_2974_; lean_object* v_toPure_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; 
v_toApplicative_2973_ = lean_ctor_get(v_inst_2970_, 0);
v_toBind_2974_ = lean_ctor_get(v_inst_2970_, 1);
lean_inc_n(v_toBind_2974_, 2);
v_toPure_2975_ = lean_ctor_get(v_toApplicative_2973_, 1);
lean_inc_n(v_toPure_2975_, 2);
v___x_2976_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_2977_ = lean_apply_2(v_inst_2972_, lean_box(0), v___x_2976_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2978_, 0, v_toPure_2975_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2979_, 0, v_toPure_2975_);
lean_closure_set(v___f_2979_, 1, v_inst_2971_);
lean_closure_set(v___f_2979_, 2, v_toBind_2974_);
lean_closure_set(v___f_2979_, 3, v_inst_2970_);
lean_closure_set(v___f_2979_, 4, v___f_2978_);
v___x_2980_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2977_, v___f_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope(lean_object* v_m_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_pushScope___redArg(v_inst_2982_, v_inst_2983_, v_inst_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__2(lean_object* v_inst_2986_, lean_object* v_toBind_2987_, lean_object* v___f_2988_, lean_object* v_a_2989_, lean_object* v_x_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_modifyEnv_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_modifyEnv_2992_ = lean_ctor_get(v_inst_2986_, 1);
lean_inc(v_modifyEnv_2992_);
lean_dec_ref(v_inst_2986_);
v___x_2993_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_2993_, 0, lean_box(0));
lean_closure_set(v___x_2993_, 1, lean_box(0));
lean_closure_set(v___x_2993_, 2, lean_box(0));
lean_closure_set(v___x_2993_, 3, v_a_2989_);
v___x_2994_ = lean_apply_1(v_modifyEnv_2992_, v___x_2993_);
v___x_2995_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2994_, v___f_2988_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg___lam__0(lean_object* v_toPure_2996_, lean_object* v_inst_2997_, lean_object* v_toBind_2998_, lean_object* v_inst_2999_, lean_object* v___f_3000_, lean_object* v_____do__lift_3001_){
_start:
{
lean_object* v___x_3002_; lean_object* v___f_3003_; lean_object* v___f_3004_; size_t v_sz_3005_; size_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3002_ = lean_box(0);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3003_, 0, v___x_3002_);
lean_closure_set(v___f_3003_, 1, v_toPure_2996_);
lean_inc(v_toBind_2998_);
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__2), 6, 3);
lean_closure_set(v___f_3004_, 0, v_inst_2997_);
lean_closure_set(v___f_3004_, 1, v_toBind_2998_);
lean_closure_set(v___f_3004_, 2, v___f_3003_);
v_sz_3005_ = lean_array_size(v_____do__lift_3001_);
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2999_, v_____do__lift_3001_, v___f_3004_, v_sz_3005_, v___x_3006_, v___x_3002_);
v___x_3008_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3007_, v___f_3000_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___redArg(lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_){
_start:
{
lean_object* v_toApplicative_3012_; lean_object* v_toBind_3013_; lean_object* v_toPure_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; 
v_toApplicative_3012_ = lean_ctor_get(v_inst_3009_, 0);
v_toBind_3013_ = lean_ctor_get(v_inst_3009_, 1);
lean_inc_n(v_toBind_3013_, 2);
v_toPure_3014_ = lean_ctor_get(v_toApplicative_3012_, 1);
lean_inc_n(v_toPure_3014_, 2);
v___x_3015_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_3016_ = lean_apply_2(v_inst_3011_, lean_box(0), v___x_3015_);
v___f_3017_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3017_, 0, v_toPure_3014_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_popScope___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3018_, 0, v_toPure_3014_);
lean_closure_set(v___f_3018_, 1, v_inst_3010_);
lean_closure_set(v___f_3018_, 2, v_toBind_3013_);
lean_closure_set(v___f_3018_, 3, v_inst_3009_);
lean_closure_set(v___f_3018_, 4, v___f_3017_);
v___x_3019_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v___x_3016_, v___f_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope(lean_object* v_m_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_popScope___redArg(v_inst_3021_, v_inst_3022_, v_inst_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__2(lean_object* v_a_3025_, lean_object* v_depth_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_3025_, v_x_3027_, v_depth_3026_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__0(lean_object* v_inst_3029_, lean_object* v_depth_3030_, lean_object* v_toBind_3031_, lean_object* v___f_3032_, lean_object* v_a_3033_, lean_object* v_x_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_modifyEnv_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v_modifyEnv_3036_ = lean_ctor_get(v_inst_3029_, 1);
lean_inc(v_modifyEnv_3036_);
lean_dec_ref(v_inst_3029_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3037_, 0, v_a_3033_);
lean_closure_set(v___f_3037_, 1, v_depth_3030_);
v___x_3038_ = lean_apply_1(v_modifyEnv_3036_, v___f_3037_);
v___x_3039_ = lean_apply_4(v_toBind_3031_, lean_box(0), lean_box(0), v___x_3038_, v___f_3032_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg___lam__1(lean_object* v_toPure_3040_, lean_object* v_inst_3041_, lean_object* v_depth_3042_, lean_object* v_toBind_3043_, lean_object* v_inst_3044_, lean_object* v___f_3045_, lean_object* v_____do__lift_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; size_t v_sz_3050_; size_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3047_ = lean_box(0);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3048_, 0, v___x_3047_);
lean_closure_set(v___f_3048_, 1, v_toPure_3040_);
lean_inc(v_toBind_3043_);
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__0), 7, 4);
lean_closure_set(v___f_3049_, 0, v_inst_3041_);
lean_closure_set(v___f_3049_, 1, v_depth_3042_);
lean_closure_set(v___f_3049_, 2, v_toBind_3043_);
lean_closure_set(v___f_3049_, 3, v___f_3048_);
v_sz_3050_ = lean_array_size(v_____do__lift_3046_);
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3044_, v_____do__lift_3046_, v___f_3049_, v_sz_3050_, v___x_3051_, v___x_3047_);
v___x_3053_ = lean_apply_4(v_toBind_3043_, lean_box(0), lean_box(0), v___x_3052_, v___f_3045_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal___redArg(lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_depth_3057_){
_start:
{
lean_object* v_toApplicative_3058_; lean_object* v_toBind_3059_; lean_object* v_toPure_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; 
v_toApplicative_3058_ = lean_ctor_get(v_inst_3054_, 0);
v_toBind_3059_ = lean_ctor_get(v_inst_3054_, 1);
lean_inc_n(v_toBind_3059_, 2);
v_toPure_3060_ = lean_ctor_get(v_toApplicative_3058_, 1);
lean_inc_n(v_toPure_3060_, 2);
v___x_3061_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_3062_ = lean_apply_2(v_inst_3056_, lean_box(0), v___x_3061_);
v___f_3063_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3063_, 0, v_toPure_3060_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_setDelimitsLocal___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3064_, 0, v_toPure_3060_);
lean_closure_set(v___f_3064_, 1, v_inst_3055_);
lean_closure_set(v___f_3064_, 2, v_depth_3057_);
lean_closure_set(v___f_3064_, 3, v_toBind_3059_);
lean_closure_set(v___f_3064_, 4, v_inst_3054_);
lean_closure_set(v___f_3064_, 5, v___f_3063_);
v___x_3065_ = lean_apply_4(v_toBind_3059_, lean_box(0), lean_box(0), v___x_3062_, v___f_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDelimitsLocal(lean_object* v_m_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_depth_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_setDelimitsLocal___redArg(v_inst_3067_, v_inst_3068_, v_inst_3069_, v_depth_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__2(lean_object* v_a_3072_, lean_object* v_namespaceName_3073_, lean_object* v_x_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v_a_3072_, v_x_3074_, v_namespaceName_3073_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__0(lean_object* v_inst_3076_, lean_object* v_namespaceName_3077_, lean_object* v_toBind_3078_, lean_object* v___f_3079_, lean_object* v_a_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_modifyEnv_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_modifyEnv_3083_ = lean_ctor_get(v_inst_3076_, 1);
lean_inc(v_modifyEnv_3083_);
lean_dec_ref(v_inst_3076_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3084_, 0, v_a_3080_);
lean_closure_set(v___f_3084_, 1, v_namespaceName_3077_);
v___x_3085_ = lean_apply_1(v_modifyEnv_3083_, v___f_3084_);
v___x_3086_ = lean_apply_4(v_toBind_3078_, lean_box(0), lean_box(0), v___x_3085_, v___f_3079_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg___lam__1(lean_object* v_toPure_3087_, lean_object* v_inst_3088_, lean_object* v_namespaceName_3089_, lean_object* v_toBind_3090_, lean_object* v_inst_3091_, lean_object* v___f_3092_, lean_object* v_____do__lift_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3094_ = lean_box(0);
v___f_3095_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3095_, 0, v___x_3094_);
lean_closure_set(v___f_3095_, 1, v_toPure_3087_);
lean_inc(v_toBind_3090_);
v___f_3096_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__0), 7, 4);
lean_closure_set(v___f_3096_, 0, v_inst_3088_);
lean_closure_set(v___f_3096_, 1, v_namespaceName_3089_);
lean_closure_set(v___f_3096_, 2, v_toBind_3090_);
lean_closure_set(v___f_3096_, 3, v___f_3095_);
v_sz_3097_ = lean_array_size(v_____do__lift_3093_);
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3091_, v_____do__lift_3093_, v___f_3096_, v_sz_3097_, v___x_3098_, v___x_3094_);
v___x_3100_ = lean_apply_4(v_toBind_3090_, lean_box(0), lean_box(0), v___x_3099_, v___f_3092_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___redArg(lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_namespaceName_3104_){
_start:
{
lean_object* v_toApplicative_3105_; lean_object* v_toBind_3106_; lean_object* v_toPure_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___f_3110_; lean_object* v___f_3111_; lean_object* v___x_3112_; 
v_toApplicative_3105_ = lean_ctor_get(v_inst_3101_, 0);
v_toBind_3106_ = lean_ctor_get(v_inst_3101_, 1);
lean_inc_n(v_toBind_3106_, 2);
v_toPure_3107_ = lean_ctor_get(v_toApplicative_3105_, 1);
lean_inc_n(v_toPure_3107_, 2);
v___x_3108_ = lean_obj_once(&l_Lean_pushScope___redArg___closed__0, &l_Lean_pushScope___redArg___closed__0_once, _init_l_Lean_pushScope___redArg___closed__0);
v___x_3109_ = lean_apply_2(v_inst_3103_, lean_box(0), v___x_3108_);
v___f_3110_ = lean_alloc_closure((void*)(l_Lean_pushScope___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3110_, 0, v_toPure_3107_);
v___f_3111_ = lean_alloc_closure((void*)(l_Lean_activateScoped___redArg___lam__1), 7, 6);
lean_closure_set(v___f_3111_, 0, v_toPure_3107_);
lean_closure_set(v___f_3111_, 1, v_inst_3102_);
lean_closure_set(v___f_3111_, 2, v_namespaceName_3104_);
lean_closure_set(v___f_3111_, 3, v_toBind_3106_);
lean_closure_set(v___f_3111_, 4, v_inst_3101_);
lean_closure_set(v___f_3111_, 5, v___f_3110_);
v___x_3112_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3109_, v___f_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped(lean_object* v_m_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_namespaceName_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_activateScoped___redArg(v_inst_3114_, v_inst_3115_, v_inst_3116_, v_namespaceName_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam(void){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_obj_once(&l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28, &l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once, _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(lean_object* v___y_3120_){
_start:
{
lean_inc(v___y_3120_);
return v___y_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_3121_);
lean_dec(v___y_3121_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(lean_object* v_x_3123_, lean_object* v_a_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_a_3124_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(lean_object* v_x_3128_, lean_object* v_a_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(v_x_3128_, v_a_3129_, v___y_3130_);
lean_dec_ref(v___y_3130_);
lean_dec(v_x_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(lean_object* v_initial_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_initial_3133_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(lean_object* v_initial_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object* v_descr_3141_){
_start:
{
lean_object* v_name_3143_; lean_object* v_addEntry_3144_; lean_object* v_addImportedEntry_3145_; lean_object* v_initial_3146_; lean_object* v_finalizeImport_3147_; lean_object* v_exportEntry_x3f_3148_; uint8_t v_trackGen_3149_; uint8_t v_logWrites_3150_; lean_object* v_entryDecl_x3f_3151_; lean_object* v_importGlobals_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_name_3143_ = lean_ctor_get(v_descr_3141_, 0);
lean_inc(v_name_3143_);
v_addEntry_3144_ = lean_ctor_get(v_descr_3141_, 1);
lean_inc(v_addEntry_3144_);
v_addImportedEntry_3145_ = lean_ctor_get(v_descr_3141_, 2);
lean_inc(v_addImportedEntry_3145_);
v_initial_3146_ = lean_ctor_get(v_descr_3141_, 3);
lean_inc(v_initial_3146_);
v_finalizeImport_3147_ = lean_ctor_get(v_descr_3141_, 4);
lean_inc(v_finalizeImport_3147_);
v_exportEntry_x3f_3148_ = lean_ctor_get(v_descr_3141_, 5);
lean_inc_ref(v_exportEntry_x3f_3148_);
v_trackGen_3149_ = lean_ctor_get_uint8(v_descr_3141_, sizeof(void*)*8);
v_logWrites_3150_ = lean_ctor_get_uint8(v_descr_3141_, sizeof(void*)*8 + 1);
v_entryDecl_x3f_3151_ = lean_ctor_get(v_descr_3141_, 6);
lean_inc(v_entryDecl_x3f_3151_);
v_importGlobals_3152_ = lean_ctor_get(v_descr_3141_, 7);
lean_inc_ref(v_importGlobals_3152_);
lean_dec_ref(v_descr_3141_);
v___f_3153_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0));
v___f_3154_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1));
v___f_3155_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3155_, 0, v_initial_3146_);
v___x_3156_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3156_, 0, v_name_3143_);
lean_ctor_set(v___x_3156_, 1, v___f_3155_);
lean_ctor_set(v___x_3156_, 2, v___f_3154_);
lean_ctor_set(v___x_3156_, 3, v___f_3153_);
lean_ctor_set(v___x_3156_, 4, v_addEntry_3144_);
lean_ctor_set(v___x_3156_, 5, v_addImportedEntry_3145_);
lean_ctor_set(v___x_3156_, 6, v_finalizeImport_3147_);
lean_ctor_set(v___x_3156_, 7, v_exportEntry_x3f_3148_);
lean_ctor_set(v___x_3156_, 8, v_entryDecl_x3f_3151_);
lean_ctor_set(v___x_3156_, 9, v_importGlobals_3152_);
lean_ctor_set_uint8(v___x_3156_, sizeof(void*)*10, v_trackGen_3149_);
lean_ctor_set_uint8(v___x_3156_, sizeof(void*)*10 + 1, v_logWrites_3150_);
v___x_3157_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(lean_object* v_descr_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3158_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* v_00_u03b1_3161_, lean_object* v_00_u03c3_3162_, lean_object* v_descr_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtension___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_00_u03c3_3167_, lean_object* v_descr_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_3166_, v_00_u03c3_3167_, v_descr_3168_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___redArg(lean_object* v_summary_x3f_3171_){
_start:
{
lean_inc(v_summary_x3f_3171_);
return v_summary_x3f_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___redArg___boxed(lean_object* v_summary_x3f_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___redArg(v_summary_x3f_3172_);
lean_dec(v_summary_x3f_3172_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1(lean_object* v_00_u03b9_3174_, lean_object* v_summary_x3f_3175_){
_start:
{
lean_inc(v_summary_x3f_3175_);
return v_summary_x3f_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1___boxed(lean_object* v_00_u03b9_3176_, lean_object* v_summary_x3f_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_ScopedEnvExtension_0__Lean_registerSimpleScopedEnvExtensionWithSummaries_unsafe__1(v_00_u03b9_3176_, v_summary_x3f_3177_);
lean_dec(v_summary_x3f_3177_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__0(lean_object* v_s_3179_, lean_object* v_x_3180_){
_start:
{
return v_s_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__1(lean_object* v_x_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_box(0);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2(lean_object* v_x_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0));
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0(lean_object* v_summaryName_3190_, lean_object* v_as_3191_, size_t v_sz_3192_, size_t v_i_3193_, lean_object* v_b_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_lt(v_i_3193_, v_sz_3192_);
if (v___x_3195_ == 0)
{
lean_inc_ref(v_b_3194_);
return v_b_3194_;
}
else
{
lean_object* v_a_3196_; lean_object* v_name_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_a_3196_ = lean_array_uget_borrowed(v_as_3191_, v_i_3193_);
v_name_3197_ = lean_ctor_get(v_a_3196_, 1);
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_name_eq(v_name_3197_, v_summaryName_3190_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; size_t v___x_3201_; size_t v___x_3202_; 
v___x_3200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___closed__0));
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3193_, v___x_3201_);
v_i_3193_ = v___x_3202_;
v_b_3194_ = v___x_3200_;
goto _start;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_inc(v_a_3196_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_a_3196_);
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3198_);
return v___x_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___boxed(lean_object* v_summaryName_3207_, lean_object* v_as_3208_, lean_object* v_sz_3209_, lean_object* v_i_3210_, lean_object* v_b_3211_){
_start:
{
size_t v_sz_boxed_3212_; size_t v_i_boxed_3213_; lean_object* v_res_3214_; 
v_sz_boxed_3212_ = lean_unbox_usize(v_sz_3209_);
lean_dec(v_sz_3209_);
v_i_boxed_3213_ = lean_unbox_usize(v_i_3210_);
lean_dec(v_i_3210_);
v_res_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0(v_summaryName_3207_, v_as_3208_, v_sz_boxed_3212_, v_i_boxed_3213_, v_b_3211_);
lean_dec_ref(v_b_3211_);
lean_dec_ref(v_as_3208_);
lean_dec(v_summaryName_3207_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg(lean_object* v_val_3215_, lean_object* v___x_3216_, size_t v_sz_3217_, size_t v_i_3218_, lean_object* v_bs_3219_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3218_, v_sz_3217_);
if (v___x_3220_ == 0)
{
return v_bs_3219_;
}
else
{
lean_object* v___x_3221_; lean_object* v_v_3222_; lean_object* v___x_3223_; lean_object* v_bs_x27_3224_; lean_object* v___y_3226_; lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3221_ = l_Lean_instInhabitedEnvExtensionState;
v_v_3222_ = lean_array_uget(v_bs_3219_, v_i_3218_);
v___x_3223_ = lean_unsigned_to_nat(0u);
v_bs_x27_3224_ = lean_array_uset(v_bs_3219_, v_i_3218_, v___x_3223_);
v___x_3231_ = lean_usize_to_nat(v_i_3218_);
v___x_3232_ = 0;
v___x_3233_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3221_, v_val_3215_, v___x_3216_, v___x_3231_, v___x_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_array_get_size(v___x_3233_);
v___x_3235_ = lean_nat_dec_lt(v___x_3223_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec_ref(v___x_3233_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v_v_3222_);
v___y_3226_ = v___x_3237_;
goto v___jp_3225_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_array_fget(v___x_3233_, v___x_3223_);
lean_dec_ref(v___x_3233_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v_v_3222_);
v___y_3226_ = v___x_3240_;
goto v___jp_3225_;
}
v___jp_3225_:
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3218_, v___x_3227_);
v___x_3229_ = lean_array_uset(v_bs_x27_3224_, v_i_3218_, v___y_3226_);
v_i_3218_ = v___x_3228_;
v_bs_3219_ = v___x_3229_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg___boxed(lean_object* v_val_3241_, lean_object* v___x_3242_, lean_object* v_sz_3243_, lean_object* v_i_3244_, lean_object* v_bs_3245_){
_start:
{
size_t v_sz_boxed_3246_; size_t v_i_boxed_3247_; lean_object* v_res_3248_; 
v_sz_boxed_3246_ = lean_unbox_usize(v_sz_3243_);
lean_dec(v_sz_3243_);
v_i_boxed_3247_ = lean_unbox_usize(v_i_3244_);
lean_dec(v_i_3244_);
v_res_3248_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg(v_val_3241_, v___x_3242_, v_sz_boxed_3246_, v_i_boxed_3247_, v_bs_3245_);
lean_dec_ref(v___x_3242_);
lean_dec_ref(v_val_3241_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3(lean_object* v_summaryName_3251_, lean_object* v_addImported_3252_, lean_object* v_initial_3253_, lean_object* v_as_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3268_; size_t v_sz_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v_fst_3272_; 
v___x_3257_ = l_Lean_persistentEnvExtensionsRef;
v___x_3258_ = lean_st_ref_get(v___x_3257_);
v___x_3268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0___closed__0));
v_sz_3269_ = lean_array_size(v___x_3258_);
v___x_3270_ = ((size_t)0ULL);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__0(v_summaryName_3251_, v___x_3258_, v_sz_3269_, v___x_3270_, v___x_3268_);
lean_dec(v___x_3258_);
v_fst_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_fst_3272_);
lean_dec_ref(v___x_3271_);
if (lean_obj_tag(v_fst_3272_) == 0)
{
lean_dec_ref(v_as_3254_);
lean_dec(v_initial_3253_);
lean_dec_ref(v_addImported_3252_);
goto v___jp_3259_;
}
else
{
lean_object* v_val_3273_; 
v_val_3273_ = lean_ctor_get(v_fst_3272_, 0);
lean_inc(v_val_3273_);
lean_dec_ref_known(v_fst_3272_, 1);
if (lean_obj_tag(v_val_3273_) == 1)
{
lean_object* v_val_3274_; lean_object* v_env_3275_; size_t v_sz_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec(v_summaryName_3251_);
v_val_3274_ = lean_ctor_get(v_val_3273_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v_val_3273_, 1);
v_env_3275_ = lean_ctor_get(v___y_3255_, 0);
v_sz_3276_ = lean_array_size(v_as_3254_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg(v_val_3274_, v_env_3275_, v_sz_3276_, v___x_3270_, v_as_3254_);
lean_dec(v_val_3274_);
lean_inc_ref(v___y_3255_);
v___x_3278_ = lean_apply_4(v_addImported_3252_, v_initial_3253_, v___x_3277_, v___y_3255_, lean_box(0));
return v___x_3278_;
}
else
{
lean_dec(v_val_3273_);
lean_dec_ref(v_as_3254_);
lean_dec(v_initial_3253_);
lean_dec_ref(v_addImported_3252_);
goto v___jp_3259_;
}
}
v___jp_3259_:
{
lean_object* v___x_3260_; uint8_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3260_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__0));
v___x_3261_ = 1;
v___x_3262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_summaryName_3251_, v___x_3261_);
v___x_3263_ = lean_string_append(v___x_3260_, v___x_3262_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___closed__1));
v___x_3265_ = lean_string_append(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___boxed(lean_object* v_summaryName_3279_, lean_object* v_addImported_3280_, lean_object* v_initial_3281_, lean_object* v_as_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3(v_summaryName_3279_, v_addImported_3280_, v_initial_3281_, v_as_3282_, v___y_3283_);
lean_dec_ref(v___y_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(lean_object* v_as_3286_, size_t v_i_3287_, size_t v_stop_3288_, lean_object* v_b_3289_){
_start:
{
lean_object* v___y_3291_; uint8_t v___x_3295_; 
v___x_3295_ = lean_usize_dec_eq(v_i_3287_, v_stop_3288_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_array_uget_borrowed(v_as_3286_, v_i_3287_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
v___x_3298_ = lean_array_push(v_b_3289_, v_a_3297_);
v___y_3291_ = v___x_3298_;
goto v___jp_3290_;
}
else
{
v___y_3291_ = v_b_3289_;
goto v___jp_3290_;
}
}
else
{
return v_b_3289_;
}
v___jp_3290_:
{
size_t v___x_3292_; size_t v___x_3293_; 
v___x_3292_ = ((size_t)1ULL);
v___x_3293_ = lean_usize_add(v_i_3287_, v___x_3292_);
v_i_3287_ = v___x_3293_;
v_b_3289_ = v___y_3291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg___boxed(lean_object* v_as_3299_, lean_object* v_i_3300_, lean_object* v_stop_3301_, lean_object* v_b_3302_){
_start:
{
size_t v_i_boxed_3303_; size_t v_stop_boxed_3304_; lean_object* v_res_3305_; 
v_i_boxed_3303_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_stop_boxed_3304_ = lean_unbox_usize(v_stop_3301_);
lean_dec(v_stop_3301_);
v_res_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(v_as_3299_, v_i_boxed_3303_, v_stop_boxed_3304_, v_b_3302_);
lean_dec_ref(v_as_3299_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg(lean_object* v_as_3306_, lean_object* v_start_3307_, lean_object* v_stop_3308_){
_start:
{
lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0));
v___x_3310_ = lean_nat_dec_lt(v_start_3307_, v_stop_3308_);
if (v___x_3310_ == 0)
{
return v___x_3309_;
}
else
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_array_get_size(v_as_3306_);
v___x_3312_ = lean_nat_dec_le(v_stop_3308_, v___x_3311_);
if (v___x_3312_ == 0)
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_nat_dec_lt(v_start_3307_, v___x_3311_);
if (v___x_3313_ == 0)
{
return v___x_3309_;
}
else
{
size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_usize_of_nat(v_start_3307_);
v___x_3315_ = lean_usize_of_nat(v___x_3311_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(v_as_3306_, v___x_3314_, v___x_3315_, v___x_3309_);
return v___x_3316_;
}
}
else
{
size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_usize_of_nat(v_start_3307_);
v___x_3318_ = lean_usize_of_nat(v_stop_3308_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(v_as_3306_, v___x_3317_, v___x_3318_, v___x_3309_);
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg___boxed(lean_object* v_as_3320_, lean_object* v_start_3321_, lean_object* v_stop_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg(v_as_3320_, v_start_3321_, v_stop_3322_);
lean_dec(v_stop_3322_);
lean_dec(v_start_3321_);
lean_dec_ref(v_as_3320_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(lean_object* v_build_3324_, lean_object* v_env_3325_, lean_object* v_es_3326_){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_array_get_size(v_es_3326_);
v___x_3329_ = l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg(v_es_3326_, v___x_3327_, v___x_3328_);
v___x_3330_ = lean_array_get_size(v___x_3329_);
v___x_3331_ = lean_nat_dec_eq(v___x_3330_, v___x_3327_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = lean_apply_2(v_build_3324_, v_env_3325_, v___x_3329_);
v___x_3333_ = lean_unsigned_to_nat(1u);
v___x_3334_ = lean_mk_empty_array_with_capacity(v___x_3333_);
v___x_3335_ = lean_array_push(v___x_3334_, v___x_3332_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; 
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_env_3325_);
lean_dec(v_build_3324_);
v___x_3336_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__2___closed__0));
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4___boxed(lean_object* v_build_3337_, lean_object* v_env_3338_, lean_object* v_es_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(v_build_3337_, v_env_3338_, v_es_3339_);
lean_dec_ref(v_es_3339_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__5(lean_object* v_a_3341_, lean_object* v___x_3342_, lean_object* v_build_3343_, lean_object* v_env_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v_ext_3346_; lean_object* v_toEnvExtension_3347_; lean_object* v_descr_3348_; lean_object* v_asyncMode_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v_exported_3354_; lean_object* v_server_3355_; lean_object* v_private_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3366_; 
v_ext_3346_ = lean_ctor_get(v_a_3341_, 1);
lean_inc_ref(v_ext_3346_);
v_toEnvExtension_3347_ = lean_ctor_get(v_ext_3346_, 0);
v_descr_3348_ = lean_ctor_get(v_a_3341_, 0);
lean_inc_ref(v_descr_3348_);
lean_dec_ref(v_a_3341_);
v_asyncMode_3349_ = lean_ctor_get(v_toEnvExtension_3347_, 2);
lean_inc(v_asyncMode_3349_);
v___x_3350_ = lean_box(0);
v___x_3351_ = 0;
lean_inc_ref_n(v_env_3344_, 2);
v___x_3352_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3342_, v_ext_3346_, v_env_3344_, v_asyncMode_3349_, v___x_3350_, v___x_3351_);
lean_dec(v_asyncMode_3349_);
lean_dec_ref(v_ext_3346_);
v___x_3353_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_3348_, v_env_3344_, v___x_3352_);
v_exported_3354_ = lean_ctor_get(v___x_3353_, 0);
v_server_3355_ = lean_ctor_get(v___x_3353_, 1);
v_private_3356_ = lean_ctor_get(v___x_3353_, 2);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3358_ = v___x_3353_;
v_isShared_3359_ = v_isSharedCheck_3366_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_private_3356_);
lean_inc(v_server_3355_);
lean_inc(v_exported_3354_);
lean_dec(v___x_3353_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3366_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_inc_ref_n(v_env_3344_, 2);
lean_inc_n(v_build_3343_, 2);
v___x_3360_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(v_build_3343_, v_env_3344_, v_exported_3354_);
lean_dec(v_exported_3354_);
v___x_3361_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(v_build_3343_, v_env_3344_, v_server_3355_);
lean_dec(v_server_3355_);
v___x_3362_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__4(v_build_3343_, v_env_3344_, v_private_3356_);
lean_dec(v_private_3356_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 2, v___x_3362_);
lean_ctor_set(v___x_3358_, 1, v___x_3361_);
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3364_ = v___x_3358_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3365_, 2, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6(lean_object* v___x_3367_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6___boxed(lean_object* v___x_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__6(v___x_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7(lean_object* v___x_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3373_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7___boxed(lean_object* v___x_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__7(v___x_3378_, v_x_3379_, v___y_3380_);
lean_dec_ref(v___y_3380_);
lean_dec_ref(v_x_3379_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg(lean_object* v_descr_3393_, lean_object* v_build_3394_, lean_object* v_addImported_3395_){
_start:
{
lean_object* v_name_3397_; lean_object* v_addEntry_3398_; lean_object* v_addImportedEntry_3399_; lean_object* v_initial_3400_; lean_object* v_finalizeImport_3401_; lean_object* v_exportEntry_x3f_3402_; uint8_t v_trackGen_3403_; uint8_t v_logWrites_3404_; lean_object* v_entryDecl_x3f_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3446_; 
v_name_3397_ = lean_ctor_get(v_descr_3393_, 0);
v_addEntry_3398_ = lean_ctor_get(v_descr_3393_, 1);
v_addImportedEntry_3399_ = lean_ctor_get(v_descr_3393_, 2);
v_initial_3400_ = lean_ctor_get(v_descr_3393_, 3);
v_finalizeImport_3401_ = lean_ctor_get(v_descr_3393_, 4);
v_exportEntry_x3f_3402_ = lean_ctor_get(v_descr_3393_, 5);
v_trackGen_3403_ = lean_ctor_get_uint8(v_descr_3393_, sizeof(void*)*8);
v_logWrites_3404_ = lean_ctor_get_uint8(v_descr_3393_, sizeof(void*)*8 + 1);
v_entryDecl_x3f_3405_ = lean_ctor_get(v_descr_3393_, 6);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_descr_3393_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v_descr_3393_, 7);
lean_dec(v_unused_3447_);
v___x_3407_ = v_descr_3393_;
v_isShared_3408_ = v_isSharedCheck_3446_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_entryDecl_x3f_3405_);
lean_inc(v_exportEntry_x3f_3402_);
lean_inc(v_finalizeImport_3401_);
lean_inc(v_initial_3400_);
lean_inc(v_addImportedEntry_3399_);
lean_inc(v_addEntry_3398_);
lean_inc(v_name_3397_);
lean_dec(v_descr_3393_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3446_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v_summaryName_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___f_3409_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__0));
v___f_3410_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__1));
v___f_3411_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__2));
v___x_3412_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__4));
lean_inc(v_name_3397_);
v_summaryName_3413_ = l_Lean_Name_append(v_name_3397_, v___x_3412_);
lean_inc(v_initial_3400_);
lean_inc(v_summaryName_3413_);
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3414_, 0, v_summaryName_3413_);
lean_closure_set(v___f_3414_, 1, v_addImported_3395_);
lean_closure_set(v___f_3414_, 2, v_initial_3400_);
v___x_3415_ = lean_obj_once(&l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0, &l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once, _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 7, v___f_3414_);
v___x_3417_ = v___x_3407_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_name_3397_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_addEntry_3398_);
lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_addImportedEntry_3399_);
lean_ctor_set(v_reuseFailAlloc_3445_, 3, v_initial_3400_);
lean_ctor_set(v_reuseFailAlloc_3445_, 4, v_finalizeImport_3401_);
lean_ctor_set(v_reuseFailAlloc_3445_, 5, v_exportEntry_x3f_3402_);
lean_ctor_set(v_reuseFailAlloc_3445_, 6, v_entryDecl_x3f_3405_);
lean_ctor_set(v_reuseFailAlloc_3445_, 7, v___f_3414_);
lean_ctor_set_uint8(v_reuseFailAlloc_3445_, sizeof(void*)*8, v_trackGen_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3445_, sizeof(void*)*8 + 1, v_logWrites_3404_);
v___x_3417_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3417_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_n(v_a_3419_, 2);
lean_dec_ref_known(v___x_3418_, 1);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___lam__5), 5, 3);
lean_closure_set(v___f_3420_, 0, v_a_3419_);
lean_closure_set(v___f_3420_, 1, v___x_3415_);
lean_closure_set(v___f_3420_, 2, v_build_3394_);
v___f_3421_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__5));
v___f_3422_ = ((lean_object*)(l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___closed__6));
v___x_3423_ = lean_box(2);
v___x_3424_ = lean_box(0);
v___x_3425_ = 0;
v___x_3426_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3426_, 0, v_summaryName_3413_);
lean_ctor_set(v___x_3426_, 1, v___f_3421_);
lean_ctor_set(v___x_3426_, 2, v___f_3422_);
lean_ctor_set(v___x_3426_, 3, v___f_3409_);
lean_ctor_set(v___x_3426_, 4, v___f_3420_);
lean_ctor_set(v___x_3426_, 5, v___f_3410_);
lean_ctor_set(v___x_3426_, 6, v___x_3423_);
lean_ctor_set(v___x_3426_, 7, v___x_3424_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*8, v___x_3425_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*8 + 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___f_3411_);
v___x_3428_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3436_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v_a_3419_);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3419_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_a_3419_);
v_a_3437_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3428_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3428_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_dec(v_summaryName_3413_);
lean_dec(v_build_3394_);
return v___x_3418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg___boxed(lean_object* v_descr_3448_, lean_object* v_build_3449_, lean_object* v_addImported_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg(v_descr_3448_, v_build_3449_, v_addImported_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries(lean_object* v_00_u03b1_3453_, lean_object* v_00_u03c3_3454_, lean_object* v_00_u03b9_3455_, lean_object* v_descr_3456_, lean_object* v_build_3457_, lean_object* v_addImported_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries___redArg(v_descr_3456_, v_build_3457_, v_addImported_3458_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerSimpleScopedEnvExtensionWithSummaries___boxed(lean_object* v_00_u03b1_3461_, lean_object* v_00_u03c3_3462_, lean_object* v_00_u03b9_3463_, lean_object* v_descr_3464_, lean_object* v_build_3465_, lean_object* v_addImported_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_registerSimpleScopedEnvExtensionWithSummaries(v_00_u03b1_3461_, v_00_u03c3_3462_, v_00_u03b9_3463_, v_descr_3464_, v_build_3465_, v_addImported_3466_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1(lean_object* v_00_u03b1_3469_, lean_object* v_00_u03b9_3470_, lean_object* v_val_3471_, lean_object* v___x_3472_, lean_object* v_as_3473_, size_t v_sz_3474_, size_t v_i_3475_, lean_object* v_bs_3476_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___redArg(v_val_3471_, v___x_3472_, v_sz_3474_, v_i_3475_, v_bs_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1___boxed(lean_object* v_00_u03b1_3478_, lean_object* v_00_u03b9_3479_, lean_object* v_val_3480_, lean_object* v___x_3481_, lean_object* v_as_3482_, lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_bs_3485_){
_start:
{
size_t v_sz_boxed_3486_; size_t v_i_boxed_3487_; lean_object* v_res_3488_; 
v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3487_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__1(v_00_u03b1_3478_, v_00_u03b9_3479_, v_val_3480_, v___x_3481_, v_as_3482_, v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
lean_dec_ref(v_as_3482_);
lean_dec_ref(v___x_3481_);
lean_dec_ref(v_val_3480_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2(lean_object* v_00_u03b1_3489_, lean_object* v_as_3490_, lean_object* v_start_3491_, lean_object* v_stop_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___redArg(v_as_3490_, v_start_3491_, v_stop_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_as_3495_, lean_object* v_start_3496_, lean_object* v_stop_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2(v_00_u03b1_3494_, v_as_3495_, v_start_3496_, v_stop_3497_);
lean_dec(v_stop_3497_);
lean_dec(v_start_3496_);
lean_dec_ref(v_as_3495_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2(lean_object* v_00_u03b1_3499_, lean_object* v_as_3500_, size_t v_i_3501_, size_t v_stop_3502_, lean_object* v_b_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___redArg(v_as_3500_, v_i_3501_, v_stop_3502_, v_b_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3505_, lean_object* v_as_3506_, lean_object* v_i_3507_, lean_object* v_stop_3508_, lean_object* v_b_3509_){
_start:
{
size_t v_i_boxed_3510_; size_t v_stop_boxed_3511_; lean_object* v_res_3512_; 
v_i_boxed_3510_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_stop_boxed_3511_ = lean_unbox_usize(v_stop_3508_);
lean_dec(v_stop_3508_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerSimpleScopedEnvExtensionWithSummaries_spec__2_spec__2(v_00_u03b1_3505_, v_as_3506_, v_i_boxed_3510_, v_stop_boxed_3511_, v_b_3509_);
lean_dec_ref(v_as_3506_);
return v_res_3512_;
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
