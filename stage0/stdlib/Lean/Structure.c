// Lean compiler output
// Module: Lean.Structure
// Imports: public import Lean.ProjFns public import Lean.Exception public import Init.While import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Array_erase___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedConstructorVal_default;
static const lean_ctor_object l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureFieldInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureFieldInfo_default = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureFieldInfo = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprStructureFieldInfo_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fieldName"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "projFn"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "subobject\?"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoParam\?"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprStructureFieldInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprStructureFieldInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprStructureFieldInfo___closed__0 = (const lean_object*)&l_Lean_instReprStructureFieldInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprStructureFieldInfo = (const lean_object*)&l_Lean_instReprStructureFieldInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_StructureFieldInfo_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureFieldInfo_lt___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedStructureParentInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureParentInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureParentInfo_default = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureParentInfo = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
static const lean_array_object l_Lean_instInhabitedStructureInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedStructureInfo_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureInfo_default = (const lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureInfo = (const lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_StructureInfo_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedStructureState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureState_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedStructureState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureState_default;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Structure"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 99, 41, 156, 128, 75, 220, 191)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(95, 65, 245, 208, 160, 42, 187, 12)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 218, 80, 170, 109, 89, 69, 212)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structureExt"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 77, 126, 118, 66, 118, 83, 124)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_structureExt;
static const lean_array_object l_Lean_instInhabitedStructureDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureDescr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr_default = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerStructure___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_registerStructure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerStructure___closed__0;
static const lean_array_object l_Lean_registerStructure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerStructure___closed__1 = (const lean_object*)&l_Lean_registerStructure___closed__1_value;
static const lean_string_object l_Lean_registerStructure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Structure"};
static const lean_object* l_Lean_registerStructure___closed__2 = (const lean_object*)&l_Lean_registerStructure___closed__2_value;
static const lean_string_object l_Lean_registerStructure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.registerStructure"};
static const lean_object* l_Lean_registerStructure___closed__3 = (const lean_object*)&l_Lean_registerStructure___closed__3_value;
static const lean_string_object l_Lean_registerStructure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "structure `"};
static const lean_object* l_Lean_registerStructure___closed__4 = (const lean_object*)&l_Lean_registerStructure___closed__4_value;
static const lean_string_object l_Lean_registerStructure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` is already registered"};
static const lean_object* l_Lean_registerStructure___closed__5 = (const lean_object*)&l_Lean_registerStructure___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_setStructureParents___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "cannot set structure parents for `"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_setStructureParents___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, structure not defined in current module"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__0_value;
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__1 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_getStructureInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.getStructureInfo"};
static const lean_object* l_Lean_getStructureInfo___closed__0 = (const lean_object*)&l_Lean_getStructureInfo___closed__0_value;
static const lean_string_object l_Lean_getStructureInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structure expected"};
static const lean_object* l_Lean_getStructureInfo___closed__1 = (const lean_object*)&l_Lean_getStructureInfo___closed__1_value;
static lean_once_cell_t l_Lean_getStructureInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object*);
static const lean_string_object l_Lean_getStructureCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.getStructureCtor"};
static const lean_object* l_Lean_getStructureCtor___closed__0 = (const lean_object*)&l_Lean_getStructureCtor___closed__0_value;
static lean_once_cell_t l_Lean_getStructureCtor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureCtor___closed__1;
static const lean_string_object l_Lean_getStructureCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed environment"};
static const lean_object* l_Lean_getStructureCtor___closed__2 = (const lean_object*)&l_Lean_getStructureCtor___closed__2_value;
static lean_once_cell_t l_Lean_getStructureCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureCtor___closed__3;
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkFlatCtorOfStructCtorName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_flat_ctor"};
static const lean_object* l_Lean_mkFlatCtorOfStructCtorName___closed__0 = (const lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__0_value;
static const lean_ctor_object l_Lean_mkFlatCtorOfStructCtorName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 244, 96, 108, 193, 103, 182, 1)}};
static const lean_object* l_Lean_mkFlatCtorOfStructCtorName___closed__1 = (const lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkDefaultFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_default"};
static const lean_object* l_Lean_mkDefaultFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkDefaultFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 118, 55, 225, 252, 34, 96, 112)}};
static const lean_object* l_Lean_mkDefaultFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object*);
static const lean_string_object l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "_inherited_default"};
static const lean_object* l_Lean_mkInheritedDefaultFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 137, 199, 23, 68, 254, 123, 5)}};
static const lean_object* l_Lean_mkInheritedDefaultFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getDefaultFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkDefaultFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getDefaultFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getDefaultFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkInheritedDefaultFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getEffectiveDefaultFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAutoParamFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_autoParam"};
static const lean_object* l_Lean_mkAutoParamFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkAutoParamFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 175, 123, 123, 31, 136, 163, 222)}};
static const lean_object* l_Lean_mkAutoParamFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object*);
static const lean_closure_object l_Lean_getAutoParamFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkAutoParamFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAutoParamFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getAutoParamFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_getNonRecStructureCtor_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.getNonRecStructureCtor\?"};
static const lean_object* l_Lean_getNonRecStructureCtor_x3f___closed__0 = (const lean_object*)&l_Lean_getNonRecStructureCtor_x3f___closed__0_value;
static lean_once_cell_t l_Lean_getNonRecStructureCtor_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getNonRecStructureCtor_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "structureResolutionExt"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 224, 121, 249, 250, 207, 252, 156)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_structureResolutionExt;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
static const lean_array_object l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value;
static const lean_array_object l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderResult = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value;
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_computeStructureResolutionOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_computeStructureResolutionOrder___redArg___closed__0 = (const lean_object*)&l_Lean_computeStructureResolutionOrder___redArg___closed__0_value;
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value;
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value)} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___closed__1 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_getStructureResolutionOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getStructureResolutionOrder___redArg___closed__0 = (const lean_object*)&l_Lean_getStructureResolutionOrder___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1));
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_val_16_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_val_16_);
lean_dec_ref_known(v_x_13_, 1);
v___x_17_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3));
v___x_18_ = lean_unsigned_to_nat(1024u);
v___x_19_ = l_Lean_Name_reprPrec(v_val_16_, v___x_18_);
v___x_20_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_17_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
v___x_21_ = l_Repr_addAppParen(v___x_20_, v_x_14_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(v_x_22_, v_x_23_);
lean_dec(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1));
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_val_28_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_x_25_, 1);
v___x_29_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3));
v___x_30_ = lean_unsigned_to_nat(1024u);
v___x_31_ = l_Lean_instReprExpr_repr(v_val_28_, v___x_30_);
v___x_32_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = l_Repr_addAppParen(v___x_32_, v_x_26_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1___boxed(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(v_x_34_, v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprStructureFieldInfo_repr_spec__2(lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_nat_to_int(v_a_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(13u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(10u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(14u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0));
v___x_75_ = lean_string_length(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg(lean_object* v_x_82_){
_start:
{
lean_object* v_fieldName_83_; lean_object* v_projFn_84_; lean_object* v_subobject_x3f_85_; uint8_t v_binderInfo_86_; lean_object* v_autoParam_x3f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_fieldName_83_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_fieldName_83_);
v_projFn_84_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_projFn_84_);
v_subobject_x3f_85_ = lean_ctor_get(v_x_82_, 2);
lean_inc(v_subobject_x3f_85_);
v_binderInfo_86_ = lean_ctor_get_uint8(v_x_82_, sizeof(void*)*4);
v_autoParam_x3f_87_ = lean_ctor_get(v_x_82_, 3);
lean_inc(v_autoParam_x3f_87_);
lean_dec_ref(v_x_82_);
v___x_88_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5));
v___x_89_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6));
v___x_90_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_Lean_Name_reprPrec(v_fieldName_83_, v___x_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_90_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_89_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9));
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_box(1);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11));
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_88_);
v___x_104_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12);
v___x_105_ = l_Lean_Name_reprPrec(v_projFn_84_, v___x_91_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_94_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_97_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_99_);
v___x_111_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14));
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_88_);
v___x_114_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15);
v___x_115_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(v_subobject_x3f_85_, v___x_91_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_94_);
v___x_118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_113_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_97_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_99_);
v___x_121_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17));
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_88_);
v___x_124_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_86_, v___x_91_);
v___x_125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_114_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_94_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_97_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_99_);
v___x_130_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_88_);
v___x_133_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(v_autoParam_x3f_87_, v___x_91_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_114_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_94_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_132_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22);
v___x_138_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23));
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_136_);
v___x_140_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24));
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_137_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_94_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_instReprStructureFieldInfo_repr___redArg(v_x_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___boxed(lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_instReprStructureFieldInfo_repr(v_x_147_, v_prec_148_);
lean_dec(v_prec_148_);
return v_res_149_;
}
}
uint8_t l_Lean_StructureFieldInfo_lt(lean_object* v_i_u2081_152_, lean_object* v_i_u2082_153_){
_start:
{
lean_object* v_fieldName_154_; lean_object* v_fieldName_155_; uint8_t v___x_156_; 
v_fieldName_154_ = lean_ctor_get(v_i_u2081_152_, 0);
v_fieldName_155_ = lean_ctor_get(v_i_u2082_153_, 0);
v___x_156_ = l_Lean_Name_quickLt(v_fieldName_154_, v_fieldName_155_);
return v___x_156_;
}
}
LEAN_EXPORT void l_Lean_StructureFieldInfo_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_u2081_152_ = stack[0].m_obj;
lean_object* v_i_u2082_153_ = stack[1].m_obj;
uint8_t v_res_157_;
v_res_157_ = l_Lean_StructureFieldInfo_lt(v_i_u2081_152_, v_i_u2082_153_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_StructureFieldInfo_lt___boxed(lean_object* v_i_u2081_158_, lean_object* v_i_u2082_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_StructureFieldInfo_lt(v_i_u2081_158_, v_i_u2082_159_);
lean_dec_ref(v_i_u2082_159_);
lean_dec_ref(v_i_u2081_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
uint8_t l_Lean_StructureInfo_lt(lean_object* v_i_u2081_174_, lean_object* v_i_u2082_175_){
_start:
{
lean_object* v_structName_176_; lean_object* v_structName_177_; uint8_t v___x_178_; 
v_structName_176_ = lean_ctor_get(v_i_u2081_174_, 0);
v_structName_177_ = lean_ctor_get(v_i_u2082_175_, 0);
v___x_178_ = l_Lean_Name_quickLt(v_structName_176_, v_structName_177_);
return v___x_178_;
}
}
LEAN_EXPORT void l_Lean_StructureInfo_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_u2081_174_ = stack[0].m_obj;
lean_object* v_i_u2082_175_ = stack[1].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_Lean_StructureInfo_lt(v_i_u2081_174_, v_i_u2082_175_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object* v_i_u2081_180_, lean_object* v_i_u2082_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_StructureInfo_lt(v_i_u2081_180_, v_i_u2082_181_);
lean_dec_ref(v_i_u2082_181_);
lean_dec_ref(v_i_u2081_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object* v_as_184_, lean_object* v_k_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_m_190_; lean_object* v_a_191_; uint8_t v___x_192_; 
v___x_188_ = lean_nat_add(v_x_186_, v_x_187_);
v___x_189_ = lean_unsigned_to_nat(1u);
v_m_190_ = lean_nat_shiftr(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
v_a_191_ = lean_array_fget_borrowed(v_as_184_, v_m_190_);
v___x_192_ = l_Lean_StructureFieldInfo_lt(v_a_191_, v_k_185_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
lean_dec(v_x_187_);
v___x_193_ = l_Lean_StructureFieldInfo_lt(v_k_185_, v_a_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec(v_m_190_);
lean_dec(v_x_186_);
lean_inc(v_a_191_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_a_191_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_eq(v_m_190_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_nat_sub(v_m_190_, v___x_189_);
lean_dec(v_m_190_);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v_x_186_);
if (v___x_198_ == 0)
{
v_x_187_ = v___x_197_;
goto _start;
}
else
{
lean_object* v___x_200_; 
lean_dec(v___x_197_);
lean_dec(v_x_186_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; 
lean_dec(v_m_190_);
lean_dec(v_x_186_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
}
else
{
lean_object* v___x_202_; uint8_t v___x_203_; 
lean_dec(v_x_186_);
v___x_202_ = lean_nat_add(v_m_190_, v___x_189_);
lean_dec(v_m_190_);
v___x_203_ = lean_nat_dec_le(v___x_202_, v_x_187_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v___x_202_);
lean_dec(v_x_187_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
v_x_186_ = v___x_202_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object* v_as_206_, lean_object* v_k_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_206_, v_k_207_, v_x_208_, v_x_209_);
lean_dec_ref(v_k_207_);
lean_dec_ref(v_as_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object* v_info_211_, lean_object* v_i_212_){
_start:
{
lean_object* v_fieldNames_213_; lean_object* v_fieldInfo_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_fieldNames_213_ = lean_ctor_get(v_info_211_, 1);
v_fieldInfo_214_ = lean_ctor_get(v_info_211_, 2);
v___x_215_ = lean_array_get_size(v_fieldNames_213_);
v___x_216_ = lean_nat_dec_lt(v_i_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_array_get_size(v_fieldInfo_214_);
v___x_220_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_sub(v___x_219_, v___x_223_);
v___x_225_ = lean_nat_dec_le(v___x_218_, v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v___x_224_);
return v___x_222_;
}
else
{
lean_object* v_fieldName_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_fieldName_226_ = lean_array_fget_borrowed(v_fieldNames_213_, v_i_212_);
v___x_227_ = lean_box(0);
v___x_228_ = 0;
lean_inc(v_fieldName_226_);
v___x_229_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_229_, 0, v_fieldName_226_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_222_);
lean_ctor_set(v___x_229_, 3, v___x_222_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4, v___x_228_);
v___x_230_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_214_, v___x_229_, v___x_218_, v___x_224_);
lean_dec_ref_known(v___x_229_, 4);
if (lean_obj_tag(v___x_230_) == 0)
{
return v___x_222_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_projFn_235_; lean_object* v___x_237_; 
v_projFn_235_ = lean_ctor_get(v_val_231_, 1);
lean_inc(v_projFn_235_);
lean_dec(v_val_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_projFn_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_projFn_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object* v_info_240_, lean_object* v_i_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_StructureInfo_getProjFn_x3f(v_info_240_, v_i_241_);
lean_dec(v_i_241_);
lean_dec_ref(v_info_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object* v_as_243_, lean_object* v_k_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_243_, v_k_244_, v_x_245_, v_x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object* v_as_249_, lean_object* v_k_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(v_as_249_, v_k_250_, v_x_251_, v_x_252_, v_x_253_);
lean_dec_ref(v_k_250_);
lean_dec_ref(v_as_249_);
return v_res_254_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__0(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_255_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_instInhabitedStructureState_default;
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v_x_262_);
lean_dec_ref(v_x_262_);
return v_res_263_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(size_t v_sz_264_, size_t v_i_265_, lean_object* v_bs_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_lt(v_i_265_, v_sz_264_);
if (v___x_267_ == 0)
{
return v_bs_266_;
}
else
{
lean_object* v_v_268_; lean_object* v_snd_269_; lean_object* v___x_270_; lean_object* v_bs_x27_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v_v_268_ = lean_array_uget_borrowed(v_bs_266_, v_i_265_);
v_snd_269_ = lean_ctor_get(v_v_268_, 1);
lean_inc(v_snd_269_);
v___x_270_ = lean_unsigned_to_nat(0u);
v_bs_x27_271_ = lean_array_uset(v_bs_266_, v_i_265_, v___x_270_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_265_, v___x_272_);
v___x_274_ = lean_array_uset(v_bs_x27_271_, v_i_265_, v_snd_269_);
v_i_265_ = v___x_273_;
v_bs_266_ = v___x_274_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_264_ = stack[0].m_num;
size_t v_i_265_ = stack[1].m_num;
lean_object* v_bs_266_ = stack[2].m_obj;
lean_object* v_res_276_;
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_264_, v_i_265_, v_bs_266_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_bs_279_){
_start:
{
size_t v_sz_boxed_280_; size_t v_i_boxed_281_; lean_object* v_res_282_; 
v_sz_boxed_280_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_281_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_boxed_280_, v_i_boxed_281_, v_bs_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object* v_f_283_, lean_object* v_x1_284_, lean_object* v_x2_285_, lean_object* v_x3_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_3(v_f_283_, v_x1_284_, v_x2_285_, v_x3_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_f_288_, lean_object* v_keys_289_, lean_object* v_vals_290_, lean_object* v_i_291_, lean_object* v_acc_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_get_size(v_keys_289_);
v___x_294_ = lean_nat_dec_lt(v_i_291_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v_i_291_);
lean_dec(v_f_288_);
return v_acc_292_;
}
else
{
lean_object* v_k_295_; lean_object* v_v_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_k_295_ = lean_array_fget_borrowed(v_keys_289_, v_i_291_);
v_v_296_ = lean_array_fget_borrowed(v_vals_290_, v_i_291_);
lean_inc(v_f_288_);
lean_inc(v_v_296_);
lean_inc(v_k_295_);
v___x_297_ = lean_apply_3(v_f_288_, v_acc_292_, v_k_295_, v_v_296_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_291_, v___x_298_);
lean_dec(v_i_291_);
v_i_291_ = v___x_299_;
v_acc_292_ = v___x_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_f_301_, lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_acc_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_301_, v_keys_302_, v_vals_303_, v_i_304_, v_acc_305_);
lean_dec_ref(v_vals_303_);
lean_dec_ref(v_keys_302_);
return v_res_306_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_307_, lean_object* v_as_308_, size_t v_i_309_, size_t v_stop_310_, lean_object* v_b_311_){
_start:
{
lean_object* v___y_313_; uint8_t v___x_317_; 
v___x_317_ = lean_usize_dec_eq(v_i_309_, v_stop_310_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_array_uget_borrowed(v_as_308_, v_i_309_);
switch(lean_obj_tag(v___x_318_))
{
case 0:
{
lean_object* v_key_319_; lean_object* v_val_320_; lean_object* v___x_321_; 
v_key_319_ = lean_ctor_get(v___x_318_, 0);
v_val_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_f_307_);
lean_inc(v_val_320_);
lean_inc(v_key_319_);
v___x_321_ = lean_apply_3(v_f_307_, v_b_311_, v_key_319_, v_val_320_);
v___y_313_ = v___x_321_;
goto v___jp_312_;
}
case 1:
{
lean_object* v_node_322_; lean_object* v___x_323_; 
v_node_322_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_f_307_);
v___x_323_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_307_, v_node_322_, v_b_311_);
v___y_313_ = v___x_323_;
goto v___jp_312_;
}
default: 
{
v___y_313_ = v_b_311_;
goto v___jp_312_;
}
}
}
else
{
lean_dec(v_f_307_);
return v_b_311_;
}
v___jp_312_:
{
size_t v___x_314_; size_t v___x_315_; 
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_309_, v___x_314_);
v_i_309_ = v___x_315_;
v_b_311_ = v___y_313_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_307_ = stack[0].m_obj;
lean_object* v_as_308_ = stack[1].m_obj;
size_t v_i_309_ = stack[2].m_num;
size_t v_stop_310_ = stack[3].m_num;
lean_object* v_b_311_ = stack[4].m_obj;
lean_object* v_res_324_;
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_307_, v_as_308_, v_i_309_, v_stop_310_, v_b_311_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_es_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_es_328_ = lean_ctor_get(v_x_326_, 0);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_array_get_size(v_es_328_);
v___x_331_ = lean_nat_dec_lt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v_f_325_);
return v_x_327_;
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_330_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_325_, v_es_328_, v___x_332_, v___x_333_, v_x_327_);
return v___x_334_;
}
}
else
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_ks_335_ = lean_ctor_get(v_x_326_, 0);
v_vs_336_ = lean_ctor_get(v_x_326_, 1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_325_, v_ks_335_, v_vs_336_, v___x_337_, v_x_327_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_339_, v_x_340_, v_x_341_);
lean_dec_ref(v_x_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_343_, lean_object* v_as_344_, lean_object* v_i_345_, lean_object* v_stop_346_, lean_object* v_b_347_){
_start:
{
size_t v_i_boxed_348_; size_t v_stop_boxed_349_; lean_object* v_res_350_; 
v_i_boxed_348_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_stop_boxed_349_ = lean_unbox_usize(v_stop_346_);
lean_dec(v_stop_346_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_343_, v_as_344_, v_i_boxed_348_, v_stop_boxed_349_, v_b_347_);
lean_dec_ref(v_as_344_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_351_, lean_object* v_f_352_, lean_object* v_init_353_){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; 
v___f_354_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_354_, 0, v_f_352_);
v___x_355_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_354_, v_map_351_, v_init_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_356_, lean_object* v_f_357_, lean_object* v_init_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_356_, v_f_357_, v_init_358_);
lean_dec_ref(v_map_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_ps_360_, lean_object* v_k_361_, lean_object* v_v_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_k_361_);
lean_ctor_set(v___x_363_, 1, v_v_362_);
v___x_364_ = lean_array_push(v_ps_360_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_368_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___f_369_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_370_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__1));
v___x_371_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_368_, v___f_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_m_372_);
lean_dec_ref(v_m_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_374_, lean_object* v_pivot_375_, lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_k_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_nat_dec_lt(v_k_378_, v_hi_374_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_k_378_);
v___x_380_ = lean_array_fswap(v_as_376_, v_i_377_, v_hi_374_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_i_377_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_fget_borrowed(v_as_376_, v_k_378_);
v___x_383_ = l_Lean_StructureInfo_lt(v___x_382_, v_pivot_375_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_k_378_, v___x_384_);
lean_dec(v_k_378_);
v_k_378_ = v___x_385_;
goto _start;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_array_fswap(v_as_376_, v_i_377_, v_k_378_);
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_add(v_i_377_, v___x_388_);
lean_dec(v_i_377_);
v___x_390_ = lean_nat_add(v_k_378_, v___x_388_);
lean_dec(v_k_378_);
v_as_376_ = v___x_387_;
v_i_377_ = v___x_389_;
v_k_378_ = v___x_390_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_392_, lean_object* v_pivot_393_, lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_392_, v_pivot_393_, v_as_394_, v_i_395_, v_k_396_);
lean_dec_ref(v_pivot_393_);
lean_dec(v_hi_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_398_, lean_object* v_as_399_, lean_object* v_lo_400_, lean_object* v_hi_401_){
_start:
{
lean_object* v___y_403_; uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_lt(v_lo_400_, v_hi_401_);
if (v___x_413_ == 0)
{
lean_dec(v_lo_400_);
return v_as_399_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_mid_416_; lean_object* v___y_418_; lean_object* v___y_424_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_414_ = lean_nat_add(v_lo_400_, v_hi_401_);
v___x_415_ = lean_unsigned_to_nat(1u);
v_mid_416_ = lean_nat_shiftr(v___x_414_, v___x_415_);
lean_dec(v___x_414_);
v___x_429_ = lean_array_fget_borrowed(v_as_399_, v_mid_416_);
v___x_430_ = lean_array_fget_borrowed(v_as_399_, v_lo_400_);
v___x_431_ = l_Lean_StructureInfo_lt(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
v___y_424_ = v_as_399_;
goto v___jp_423_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = lean_array_fswap(v_as_399_, v_lo_400_, v_mid_416_);
v___y_424_ = v___x_432_;
goto v___jp_423_;
}
v___jp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_array_fget_borrowed(v___y_418_, v_mid_416_);
v___x_420_ = lean_array_fget_borrowed(v___y_418_, v_hi_401_);
v___x_421_ = l_Lean_StructureInfo_lt(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec(v_mid_416_);
v___y_403_ = v___y_418_;
goto v___jp_402_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_array_fswap(v___y_418_, v_mid_416_, v_hi_401_);
lean_dec(v_mid_416_);
v___y_403_ = v___x_422_;
goto v___jp_402_;
}
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_array_fget_borrowed(v___y_424_, v_hi_401_);
v___x_426_ = lean_array_fget_borrowed(v___y_424_, v_lo_400_);
v___x_427_ = l_Lean_StructureInfo_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
v___y_418_ = v___y_424_;
goto v___jp_417_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_array_fswap(v___y_424_, v_lo_400_, v_hi_401_);
v___y_418_ = v___x_428_;
goto v___jp_417_;
}
}
}
v___jp_402_:
{
lean_object* v_pivot_404_; lean_object* v___x_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; uint8_t v___x_408_; 
v_pivot_404_ = lean_array_fget(v___y_403_, v_hi_401_);
lean_inc_n(v_lo_400_, 2);
v___x_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_401_, v_pivot_404_, v___y_403_, v_lo_400_, v_lo_400_);
lean_dec(v_pivot_404_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
v_snd_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v___x_405_);
v___x_408_ = lean_nat_dec_le(v_hi_401_, v_fst_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_398_, v_snd_407_, v_lo_400_, v_fst_406_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_fst_406_, v___x_410_);
lean_dec(v_fst_406_);
v_as_399_ = v___x_409_;
v_lo_400_ = v___x_411_;
goto _start;
}
else
{
lean_dec(v_fst_406_);
lean_dec(v_lo_400_);
return v_snd_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_433_, lean_object* v_as_434_, lean_object* v_lo_435_, lean_object* v_hi_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_433_, v_as_434_, v_lo_435_, v_hi_436_);
lean_dec(v_hi_436_);
lean_dec(v_n_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_438_, lean_object* v_x_439_, lean_object* v_s_440_){
_start:
{
lean_object* v_snd_441_; lean_object* v___x_442_; size_t v_sz_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___x_452_; 
v_snd_441_ = lean_ctor_get(v_s_440_, 1);
v___x_442_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_snd_441_);
v_sz_443_ = lean_array_size(v___x_442_);
v___x_444_ = ((size_t)0ULL);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_443_, v___x_444_, v___x_442_);
v___x_446_ = lean_array_get_size(v___x_445_);
v___x_452_ = lean_nat_dec_eq(v___x_446_, v___x_438_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___y_456_; uint8_t v___x_458_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_sub(v___x_446_, v___x_453_);
v___x_458_ = lean_nat_dec_le(v___x_438_, v___x_454_);
if (v___x_458_ == 0)
{
lean_dec(v___x_438_);
lean_inc(v___x_454_);
v___y_456_ = v___x_454_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___x_438_;
goto v___jp_455_;
}
v___jp_455_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_le(v___y_456_, v___x_454_);
if (v___x_457_ == 0)
{
lean_dec(v___x_454_);
lean_inc(v___y_456_);
v___y_448_ = v___y_456_;
v___y_449_ = v___y_456_;
goto v___jp_447_;
}
else
{
v___y_448_ = v___y_456_;
v___y_449_ = v___x_454_;
goto v___jp_447_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___x_438_);
lean_inc_ref_n(v___x_445_, 2);
v___x_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_445_);
lean_ctor_set(v___x_459_, 1, v___x_445_);
lean_ctor_set(v___x_459_, 2, v___x_445_);
return v___x_459_;
}
v___jp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_446_, v___x_445_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_inc_ref_n(v___x_450_, 2);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_460_, lean_object* v_x_461_, lean_object* v_s_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_460_, v_x_461_, v_s_462_);
lean_dec_ref(v_s_462_);
lean_dec_ref(v_x_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_snd_466_; lean_object* v___x_467_; size_t v_sz_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_snd_466_ = lean_ctor_get(v_x_465_, 1);
v___x_467_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_snd_466_);
v_sz_468_ = lean_array_size(v___x_467_);
v___x_469_ = ((size_t)0ULL);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_468_, v___x_469_, v___x_467_);
v___x_471_ = lean_array_get_size(v___x_470_);
v___x_472_ = lean_nat_dec_eq(v___x_471_, v___x_464_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___y_476_; uint8_t v___x_480_; 
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_sub(v___x_471_, v___x_473_);
v___x_480_ = lean_nat_dec_le(v___x_464_, v___x_474_);
if (v___x_480_ == 0)
{
lean_dec(v___x_464_);
lean_inc(v___x_474_);
v___y_476_ = v___x_474_;
goto v___jp_475_;
}
else
{
v___y_476_ = v___x_464_;
goto v___jp_475_;
}
v___jp_475_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_le(v___y_476_, v___x_474_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v___x_474_);
lean_inc(v___y_476_);
v___x_478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_471_, v___x_470_, v___y_476_, v___y_476_);
lean_dec(v___y_476_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_471_, v___x_470_, v___y_476_, v___x_474_);
lean_dec(v___x_474_);
return v___x_479_;
}
}
}
else
{
lean_dec(v___x_464_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_481_, v_x_482_);
lean_dec_ref(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_ks_488_; lean_object* v_vs_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_ks_488_ = lean_ctor_get(v_x_484_, 0);
v_vs_489_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_x_484_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_vs_489_);
lean_inc(v_ks_488_);
lean_dec(v_x_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_array_get_size(v_ks_488_);
v___x_494_ = lean_nat_dec_lt(v_x_485_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec(v_x_485_);
v___x_495_ = lean_array_push(v_ks_488_, v_x_486_);
v___x_496_ = lean_array_push(v_vs_489_, v_x_487_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_496_);
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_k_x27_500_; uint8_t v___x_501_; 
v_k_x27_500_ = lean_array_fget_borrowed(v_ks_488_, v_x_485_);
v___x_501_ = lean_name_eq(v_x_486_, v_k_x27_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
if (v_isShared_492_ == 0)
{
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_ks_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_vs_489_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_x_485_, v___x_504_);
lean_dec(v_x_485_);
v_x_484_ = v___x_503_;
v_x_485_ = v___x_505_;
goto _start;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_array_fset(v_ks_488_, v_x_485_, v_x_486_);
v___x_509_ = lean_array_fset(v_vs_489_, v_x_485_, v_x_487_);
lean_dec(v_x_485_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_509_);
lean_ctor_set(v___x_491_, 0, v___x_508_);
v___x_511_ = v___x_491_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_n_514_, lean_object* v_k_515_, lean_object* v_v_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_n_514_, v___x_517_, v_k_515_, v_v_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_519_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_520_, size_t v_x_521_, size_t v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_es_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v_j_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_es_525_ = lean_ctor_get(v_x_520_, 0);
v___x_526_ = ((size_t)31ULL);
v___x_527_ = lean_usize_land(v_x_521_, v___x_526_);
v_j_528_ = lean_usize_to_nat(v___x_527_);
v___x_529_ = lean_array_get_size(v_es_525_);
v___x_530_ = lean_nat_dec_lt(v_j_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_j_528_);
lean_dec(v_x_524_);
lean_dec(v_x_523_);
return v_x_520_;
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_569_; 
lean_inc_ref(v_es_525_);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_x_520_, 0);
lean_dec(v_unused_570_);
v___x_532_ = v_x_520_;
v_isShared_533_ = v_isSharedCheck_569_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_x_520_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_569_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_v_534_; lean_object* v___x_535_; lean_object* v_xs_x27_536_; lean_object* v___y_538_; 
v_v_534_ = lean_array_fget(v_es_525_, v_j_528_);
v___x_535_ = lean_box(0);
v_xs_x27_536_ = lean_array_fset(v_es_525_, v_j_528_, v___x_535_);
switch(lean_obj_tag(v_v_534_))
{
case 0:
{
lean_object* v_key_543_; lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_key_543_ = lean_ctor_get(v_v_534_, 0);
v_val_544_ = lean_ctor_get(v_v_534_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_v_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_546_ = v_v_534_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_inc(v_key_543_);
lean_dec(v_v_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v___x_548_; 
v___x_548_ = lean_name_eq(v_x_523_, v_key_543_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_del_object(v___x_546_);
v___x_549_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_543_, v_val_544_, v_x_523_, v_x_524_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
v___y_538_ = v___x_550_;
goto v___jp_537_;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_val_544_);
lean_dec(v_key_543_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_x_524_);
lean_ctor_set(v___x_546_, 0, v_x_523_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_x_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_x_524_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v___y_538_ = v___x_552_;
goto v___jp_537_;
}
}
}
}
case 1:
{
lean_object* v_node_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_node_555_ = lean_ctor_get(v_v_534_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_534_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v_v_534_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_node_555_);
lean_dec(v_v_534_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_usize_shift_right(v_x_521_, v___x_559_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_x_522_, v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_555_, v___x_560_, v___x_562_, v_x_523_, v_x_524_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_563_);
v___x_565_ = v___x_557_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v___y_538_ = v___x_565_;
goto v___jp_537_;
}
}
}
default: 
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_x_523_);
lean_ctor_set(v___x_568_, 1, v_x_524_);
v___y_538_ = v___x_568_;
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_array_fset(v_xs_x27_536_, v_j_528_, v___y_538_);
lean_dec(v_j_528_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_539_);
v___x_541_ = v___x_532_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v_ks_571_; lean_object* v_vs_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_590_; 
v_ks_571_ = lean_ctor_get(v_x_520_, 0);
v_vs_572_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_590_ == 0)
{
v___x_574_ = v_x_520_;
v_isShared_575_ = v_isSharedCheck_590_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_vs_572_);
lean_inc(v_ks_571_);
lean_dec(v_x_520_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_590_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_ks_571_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_vs_572_);
v___x_577_ = v_reuseFailAlloc_589_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v_newNode_578_; size_t v___x_579_; uint8_t v___x_580_; 
v_newNode_578_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_577_, v_x_523_, v_x_524_);
v___x_579_ = ((size_t)7ULL);
v___x_580_ = lean_usize_dec_le(v___x_579_, v_x_522_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_578_);
v___x_582_ = lean_unsigned_to_nat(4u);
v___x_583_ = lean_nat_dec_lt(v___x_581_, v___x_582_);
lean_dec(v___x_581_);
if (v___x_583_ == 0)
{
lean_object* v_ks_584_; lean_object* v_vs_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_ks_584_ = lean_ctor_get(v_newNode_578_, 0);
lean_inc_ref(v_ks_584_);
v_vs_585_ = lean_ctor_get(v_newNode_578_, 1);
lean_inc_ref(v_vs_585_);
lean_dec_ref(v_newNode_578_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_522_, v_ks_584_, v_vs_585_, v___x_586_, v___x_587_);
lean_dec_ref(v_vs_585_);
lean_dec_ref(v_ks_584_);
return v___x_588_;
}
else
{
return v_newNode_578_;
}
}
else
{
return v_newNode_578_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_520_ = stack[0].m_obj;
size_t v_x_521_ = stack[1].m_num;
size_t v_x_522_ = stack[2].m_num;
lean_object* v_x_523_ = stack[3].m_obj;
lean_object* v_x_524_ = stack[4].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_520_, v_x_521_, v_x_522_, v_x_523_, v_x_524_);
stack->m_obj
 = v_res_591_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_592_, lean_object* v_keys_593_, lean_object* v_vals_594_, lean_object* v_i_595_, lean_object* v_entries_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_size(v_keys_593_);
v___x_598_ = lean_nat_dec_lt(v_i_595_, v___x_597_);
if (v___x_598_ == 0)
{
lean_dec(v_i_595_);
return v_entries_596_;
}
else
{
lean_object* v_k_599_; lean_object* v_v_600_; uint64_t v___y_602_; 
v_k_599_ = lean_array_fget_borrowed(v_keys_593_, v_i_595_);
v_v_600_ = lean_array_fget_borrowed(v_vals_594_, v_i_595_);
if (lean_obj_tag(v_k_599_) == 0)
{
uint64_t v___x_613_; 
v___x_613_ = 1723ULL;
v___y_602_ = v___x_613_;
goto v___jp_601_;
}
else
{
uint64_t v_hash_614_; 
v_hash_614_ = lean_ctor_get_uint64(v_k_599_, sizeof(void*)*2);
v___y_602_ = v_hash_614_;
goto v___jp_601_;
}
v___jp_601_:
{
size_t v_h_603_; size_t v___x_604_; lean_object* v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v_h_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_h_603_ = lean_uint64_to_usize(v___y_602_);
v___x_604_ = ((size_t)5ULL);
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_sub(v_depth_592_, v___x_606_);
v___x_608_ = lean_usize_mul(v___x_604_, v___x_607_);
v_h_609_ = lean_usize_shift_right(v_h_603_, v___x_608_);
v___x_610_ = lean_nat_add(v_i_595_, v___x_605_);
lean_dec(v_i_595_);
lean_inc(v_v_600_);
lean_inc(v_k_599_);
v___x_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_596_, v_h_609_, v_depth_592_, v_k_599_, v_v_600_);
v_i_595_ = v___x_610_;
v_entries_596_ = v___x_611_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_592_ = stack[0].m_num;
lean_object* v_keys_593_ = stack[1].m_obj;
lean_object* v_vals_594_ = stack[2].m_obj;
lean_object* v_i_595_ = stack[3].m_obj;
lean_object* v_entries_596_ = stack[4].m_obj;
lean_object* v_res_615_;
v_res_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_592_, v_keys_593_, v_vals_594_, v_i_595_, v_entries_596_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_616_, lean_object* v_keys_617_, lean_object* v_vals_618_, lean_object* v_i_619_, lean_object* v_entries_620_){
_start:
{
size_t v_depth_boxed_621_; lean_object* v_res_622_; 
v_depth_boxed_621_ = lean_unbox_usize(v_depth_616_);
lean_dec(v_depth_616_);
v_res_622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_621_, v_keys_617_, v_vals_618_, v_i_619_, v_entries_620_);
lean_dec_ref(v_vals_618_);
lean_dec_ref(v_keys_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
size_t v_x_1970__boxed_628_; size_t v_x_1971__boxed_629_; lean_object* v_res_630_; 
v_x_1970__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_x_1971__boxed_629_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_623_, v_x_1970__boxed_628_, v_x_1971__boxed_629_, v_x_626_, v_x_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
uint64_t v___y_635_; 
if (lean_obj_tag(v_x_632_) == 0)
{
uint64_t v___x_639_; 
v___x_639_ = 1723ULL;
v___y_635_ = v___x_639_;
goto v___jp_634_;
}
else
{
uint64_t v_hash_640_; 
v_hash_640_ = lean_ctor_get_uint64(v_x_632_, sizeof(void*)*2);
v___y_635_ = v_hash_640_;
goto v___jp_634_;
}
v___jp_634_:
{
size_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_uint64_to_usize(v___y_635_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_631_, v___x_636_, v___x_637_, v_x_632_, v_x_633_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_641_, lean_object* v_x_642_, lean_object* v_e_643_){
_start:
{
lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_653_; 
v_snd_644_ = lean_ctor_get(v_x_642_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_x_642_, 0);
lean_dec(v_unused_654_);
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_structName_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v_structName_648_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_structName_648_);
v___x_649_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(v_snd_644_, v_structName_648_, v_e_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_649_);
lean_ctor_set(v___x_646_, 0, v___x_641_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
return v___x_657_;
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_655_ = stack[0].m_obj;
lean_object* v_res_658_;
v_res_658_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_655_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_659_);
return v_res_661_;
}
}
lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_662_, lean_object* v_x_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_662_);
return v___x_666_;
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_662_ = stack[0].m_obj;
lean_object* v_x_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v_res_667_;
v_res_667_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_662_, v_x_663_, v___y_664_);
stack->m_obj
 = v_res_667_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_668_, v_x_669_, v___y_670_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v_x_669_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_703_ = lean_box(0);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_705_; lean_object* v___f_706_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_706_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_706_, 0, v___x_705_);
return v___f_706_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_707_; lean_object* v___f_708_; 
v___x_707_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_708_, 0, v___x_707_);
return v___f_708_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_709_ = 1;
v___x_710_ = 0;
v___x_711_ = lean_box(0);
v___x_712_ = lean_box(2);
v___f_713_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_714_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_715_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_716_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_717_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_718_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___x_719_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___f_717_);
lean_ctor_set(v___x_719_, 2, v___f_716_);
lean_ctor_set(v___x_719_, 3, v___f_715_);
lean_ctor_set(v___x_719_, 4, v___f_714_);
lean_ctor_set(v___x_719_, 5, v___f_713_);
lean_ctor_set(v___x_719_, 6, v___x_712_);
lean_ctor_set(v___x_719_, 7, v___x_711_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*8, v___x_710_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*8 + 1, v___x_709_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___f_720_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___x_721_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___f_720_);
return v___x_722_;
}
}
lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_725_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_726_;
v_res_726_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_();
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_729_, lean_object* v_m_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_m_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_732_, lean_object* v_m_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0(v_00_u03b2_732_, v_m_733_);
lean_dec_ref(v_m_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2(lean_object* v_n_735_, lean_object* v_as_736_, lean_object* v_lo_737_, lean_object* v_hi_738_, lean_object* v_w_739_, lean_object* v_hlo_740_, lean_object* v_hhi_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_735_, v_as_736_, v_lo_737_, v_hi_738_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_743_, lean_object* v_as_744_, lean_object* v_lo_745_, lean_object* v_hi_746_, lean_object* v_w_747_, lean_object* v_hlo_748_, lean_object* v_hhi_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2(v_n_743_, v_as_744_, v_lo_745_, v_hi_746_, v_w_747_, v_hlo_748_, v_hhi_749_);
lean_dec(v_hi_746_);
lean_dec(v_n_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(v_x_752_, v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_756_, lean_object* v_00_u03b2_757_, lean_object* v_map_758_, lean_object* v_f_759_, lean_object* v_init_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_758_, v_f_759_, v_init_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_762_, lean_object* v_00_u03b2_763_, lean_object* v_map_764_, lean_object* v_f_765_, lean_object* v_init_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_762_, v_00_u03b2_763_, v_map_764_, v_f_765_, v_init_766_);
lean_dec_ref(v_map_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_768_, lean_object* v_lo_769_, lean_object* v_hi_770_, lean_object* v_hhi_771_, lean_object* v_pivot_772_, lean_object* v_as_773_, lean_object* v_i_774_, lean_object* v_k_775_, lean_object* v_ilo_776_, lean_object* v_ik_777_, lean_object* v_w_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_770_, v_pivot_772_, v_as_773_, v_i_774_, v_k_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_780_, lean_object* v_lo_781_, lean_object* v_hi_782_, lean_object* v_hhi_783_, lean_object* v_pivot_784_, lean_object* v_as_785_, lean_object* v_i_786_, lean_object* v_k_787_, lean_object* v_ilo_788_, lean_object* v_ik_789_, lean_object* v_w_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3(v_n_780_, v_lo_781_, v_hi_782_, v_hhi_783_, v_pivot_784_, v_as_785_, v_i_786_, v_k_787_, v_ilo_788_, v_ik_789_, v_w_790_);
lean_dec_ref(v_pivot_784_);
lean_dec(v_hi_782_);
lean_dec(v_lo_781_);
lean_dec(v_n_780_);
return v_res_791_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, size_t v_x_794_, size_t v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_793_, v_x_794_, v_x_795_, v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_793_ = stack[1].m_obj;
size_t v_x_794_ = stack[2].m_num;
size_t v_x_795_ = stack[3].m_num;
lean_object* v_x_796_ = stack[4].m_obj;
lean_object* v_x_797_ = stack[5].m_obj;
lean_object* v_res_799_;
v_res_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(lean_box(0), v_x_793_, v_x_794_, v_x_795_, v_x_796_, v_x_797_);
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
size_t v_x_2547__boxed_806_; size_t v_x_2548__boxed_807_; lean_object* v_res_808_; 
v_x_2547__boxed_806_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_x_2548__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_800_, v_x_801_, v_x_2547__boxed_806_, v_x_2548__boxed_807_, v_x_804_, v_x_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_809_, lean_object* v_f_810_, lean_object* v_init_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_810_, v_map_809_, v_init_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_813_, lean_object* v_f_814_, lean_object* v_init_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_813_, v_f_814_, v_init_815_);
lean_dec_ref(v_map_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_817_, lean_object* v_00_u03b2_818_, lean_object* v_map_819_, lean_object* v_f_820_, lean_object* v_init_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_820_, v_map_819_, v_init_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_823_, lean_object* v_00_u03b2_824_, lean_object* v_map_825_, lean_object* v_f_826_, lean_object* v_init_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_823_, v_00_u03b2_824_, v_map_825_, v_f_826_, v_init_827_);
lean_dec_ref(v_map_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_829_, lean_object* v_n_830_, lean_object* v_k_831_, lean_object* v_v_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_830_, v_k_831_, v_v_832_);
return v___x_833_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_834_, size_t v_depth_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_entries_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_835_, v_keys_836_, v_vals_837_, v_i_839_, v_entries_840_);
return v___x_841_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_835_ = stack[1].m_num;
lean_object* v_keys_836_ = stack[2].m_obj;
lean_object* v_vals_837_ = stack[3].m_obj;
lean_object* v_i_839_ = stack[5].m_obj;
lean_object* v_entries_840_ = stack[6].m_obj;
lean_object* v_res_842_;
v_res_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_box(0), v_depth_835_, v_keys_836_, v_vals_837_, lean_box(0), v_i_839_, v_entries_840_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_843_, lean_object* v_depth_844_, lean_object* v_keys_845_, lean_object* v_vals_846_, lean_object* v_heq_847_, lean_object* v_i_848_, lean_object* v_entries_849_){
_start:
{
size_t v_depth_boxed_850_; lean_object* v_res_851_; 
v_depth_boxed_850_ = lean_unbox_usize(v_depth_844_);
lean_dec(v_depth_844_);
v_res_851_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_843_, v_depth_boxed_850_, v_keys_845_, v_vals_846_, v_heq_847_, v_i_848_, v_entries_849_);
lean_dec_ref(v_vals_846_);
lean_dec_ref(v_keys_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_852_, lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_f_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_859_, lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_f_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_859_, v_00_u03b1_860_, v_00_u03b2_861_, v_f_862_, v_x_863_, v_x_864_);
lean_dec_ref(v_x_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_00_u03c3_874_, lean_object* v_f_875_, lean_object* v_as_876_, size_t v_i_877_, size_t v_stop_878_, lean_object* v_b_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_875_, v_as_876_, v_i_877_, v_stop_878_, v_b_879_);
return v___x_880_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_875_ = stack[3].m_obj;
lean_object* v_as_876_ = stack[4].m_obj;
size_t v_i_877_ = stack[5].m_num;
size_t v_stop_878_ = stack[6].m_num;
lean_object* v_b_879_ = stack[7].m_obj;
lean_object* v_res_881_;
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_box(0), lean_box(0), lean_box(0), v_f_875_, v_as_876_, v_i_877_, v_stop_878_, v_b_879_);
stack->m_obj
 = v_res_881_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_00_u03c3_884_, lean_object* v_f_885_, lean_object* v_as_886_, lean_object* v_i_887_, lean_object* v_stop_888_, lean_object* v_b_889_){
_start:
{
size_t v_i_boxed_890_; size_t v_stop_boxed_891_; lean_object* v_res_892_; 
v_i_boxed_890_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_stop_boxed_891_ = lean_unbox_usize(v_stop_888_);
lean_dec(v_stop_888_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_882_, v_00_u03b2_883_, v_00_u03c3_884_, v_f_885_, v_as_886_, v_i_boxed_890_, v_stop_boxed_891_, v_b_889_);
lean_dec_ref(v_as_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_893_, lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_f_896_, lean_object* v_keys_897_, lean_object* v_vals_898_, lean_object* v_heq_899_, lean_object* v_i_900_, lean_object* v_acc_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_896_, v_keys_897_, v_vals_898_, v_i_900_, v_acc_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_903_, lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_f_906_, lean_object* v_keys_907_, lean_object* v_vals_908_, lean_object* v_heq_909_, lean_object* v_i_910_, lean_object* v_acc_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_903_, v_00_u03b1_904_, v_00_u03b2_905_, v_f_906_, v_keys_907_, v_vals_908_, v_heq_909_, v_i_910_, v_acc_911_);
lean_dec_ref(v_vals_908_);
lean_dec_ref(v_keys_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3(lean_object* v_env_920_, lean_object* v_msg_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_panic_fn_borrowed(v_env_920_, v_msg_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3___boxed(lean_object* v_env_923_, lean_object* v_msg_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_panic___at___00Lean_registerStructure_spec__3(v_env_923_, v_msg_924_);
lean_dec_ref(v_env_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure___lam__0(lean_object* v_addEntryFn_926_, lean_object* v___x_927_, lean_object* v_s_928_){
_start:
{
lean_object* v_importedEntries_929_; lean_object* v_state_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_importedEntries_929_ = lean_ctor_get(v_s_928_, 0);
v_state_930_ = lean_ctor_get(v_s_928_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_s_928_);
if (v_isSharedCheck_938_ == 0)
{
v___x_932_ = v_s_928_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_state_930_);
lean_inc(v_importedEntries_929_);
lean_dec(v_s_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_state_934_; lean_object* v___x_936_; 
v_state_934_ = lean_apply_2(v_addEntryFn_926_, v_state_930_, v___x_927_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_state_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_importedEntries_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_state_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(size_t v_sz_939_, size_t v_i_940_, lean_object* v_bs_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_940_, v_sz_939_);
if (v___x_942_ == 0)
{
return v_bs_941_;
}
else
{
lean_object* v_v_943_; lean_object* v_fieldName_944_; lean_object* v___x_945_; lean_object* v_bs_x27_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
v_v_943_ = lean_array_uget_borrowed(v_bs_941_, v_i_940_);
v_fieldName_944_ = lean_ctor_get(v_v_943_, 0);
lean_inc(v_fieldName_944_);
v___x_945_ = lean_unsigned_to_nat(0u);
v_bs_x27_946_ = lean_array_uset(v_bs_941_, v_i_940_, v___x_945_);
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_940_, v___x_947_);
v___x_949_ = lean_array_uset(v_bs_x27_946_, v_i_940_, v_fieldName_944_);
v_i_940_ = v___x_948_;
v_bs_941_ = v___x_949_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_939_ = stack[0].m_num;
size_t v_i_940_ = stack[1].m_num;
lean_object* v_bs_941_ = stack[2].m_obj;
lean_object* v_res_951_;
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(v_sz_939_, v_i_940_, v_bs_941_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_bs_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_956_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(v_sz_boxed_955_, v_i_boxed_956_, v_bs_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(lean_object* v_hi_958_, lean_object* v_pivot_959_, lean_object* v_as_960_, lean_object* v_i_961_, lean_object* v_k_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_lt(v_k_962_, v_hi_958_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_k_962_);
v___x_964_ = lean_array_fswap(v_as_960_, v_i_961_, v_hi_958_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_i_961_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_fget_borrowed(v_as_960_, v_k_962_);
v___x_967_ = l_Lean_StructureFieldInfo_lt(v___x_966_, v_pivot_959_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_k_962_, v___x_968_);
lean_dec(v_k_962_);
v_k_962_ = v___x_969_;
goto _start;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_971_ = lean_array_fswap(v_as_960_, v_i_961_, v_k_962_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_i_961_, v___x_972_);
lean_dec(v_i_961_);
v___x_974_ = lean_nat_add(v_k_962_, v___x_972_);
lean_dec(v_k_962_);
v_as_960_ = v___x_971_;
v_i_961_ = v___x_973_;
v_k_962_ = v___x_974_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg___boxed(lean_object* v_hi_976_, lean_object* v_pivot_977_, lean_object* v_as_978_, lean_object* v_i_979_, lean_object* v_k_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_976_, v_pivot_977_, v_as_978_, v_i_979_, v_k_980_);
lean_dec_ref(v_pivot_977_);
lean_dec(v_hi_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(lean_object* v_n_982_, lean_object* v_as_983_, lean_object* v_lo_984_, lean_object* v_hi_985_){
_start:
{
lean_object* v___y_987_; uint8_t v___x_997_; 
v___x_997_ = lean_nat_dec_lt(v_lo_984_, v_hi_985_);
if (v___x_997_ == 0)
{
lean_dec(v_lo_984_);
return v_as_983_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_mid_1000_; lean_object* v___y_1002_; lean_object* v___y_1008_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_998_ = lean_nat_add(v_lo_984_, v_hi_985_);
v___x_999_ = lean_unsigned_to_nat(1u);
v_mid_1000_ = lean_nat_shiftr(v___x_998_, v___x_999_);
lean_dec(v___x_998_);
v___x_1013_ = lean_array_fget_borrowed(v_as_983_, v_mid_1000_);
v___x_1014_ = lean_array_fget_borrowed(v_as_983_, v_lo_984_);
v___x_1015_ = l_Lean_StructureFieldInfo_lt(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
v___y_1008_ = v_as_983_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_array_fswap(v_as_983_, v_lo_984_, v_mid_1000_);
v___y_1008_ = v___x_1016_;
goto v___jp_1007_;
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_array_fget_borrowed(v___y_1002_, v_mid_1000_);
v___x_1004_ = lean_array_fget_borrowed(v___y_1002_, v_hi_985_);
v___x_1005_ = l_Lean_StructureFieldInfo_lt(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v_mid_1000_);
v___y_987_ = v___y_1002_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_array_fswap(v___y_1002_, v_mid_1000_, v_hi_985_);
lean_dec(v_mid_1000_);
v___y_987_ = v___x_1006_;
goto v___jp_986_;
}
}
v___jp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = lean_array_fget_borrowed(v___y_1008_, v_hi_985_);
v___x_1010_ = lean_array_fget_borrowed(v___y_1008_, v_lo_984_);
v___x_1011_ = l_Lean_StructureFieldInfo_lt(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
v___y_1002_ = v___y_1008_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_array_fswap(v___y_1008_, v_lo_984_, v_hi_985_);
v___y_1002_ = v___x_1012_;
goto v___jp_1001_;
}
}
}
v___jp_986_:
{
lean_object* v_pivot_988_; lean_object* v___x_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; uint8_t v___x_992_; 
v_pivot_988_ = lean_array_fget(v___y_987_, v_hi_985_);
lean_inc_n(v_lo_984_, 2);
v___x_989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_985_, v_pivot_988_, v___y_987_, v_lo_984_, v_lo_984_);
lean_dec(v_pivot_988_);
v_fst_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_snd_991_);
lean_dec_ref(v___x_989_);
v___x_992_ = lean_nat_dec_le(v_hi_985_, v_fst_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_982_, v_snd_991_, v_lo_984_, v_fst_990_);
v___x_994_ = lean_unsigned_to_nat(1u);
v___x_995_ = lean_nat_add(v_fst_990_, v___x_994_);
lean_dec(v_fst_990_);
v_as_983_ = v___x_993_;
v_lo_984_ = v___x_995_;
goto _start;
}
else
{
lean_dec(v_fst_990_);
lean_dec(v_lo_984_);
return v_snd_991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg___boxed(lean_object* v_n_1017_, lean_object* v_as_1018_, lean_object* v_lo_1019_, lean_object* v_hi_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_1017_, v_as_1018_, v_lo_1019_, v_hi_1020_);
lean_dec(v_hi_1020_);
lean_dec(v_n_1017_);
return v_res_1021_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1022_, lean_object* v_i_1023_, lean_object* v_k_1024_){
_start:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_array_get_size(v_keys_1022_);
v___x_1026_ = lean_nat_dec_lt(v_i_1023_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec(v_i_1023_);
return v___x_1026_;
}
else
{
lean_object* v_k_x27_1027_; uint8_t v___x_1028_; 
v_k_x27_1027_ = lean_array_fget_borrowed(v_keys_1022_, v_i_1023_);
v___x_1028_ = lean_name_eq(v_k_1024_, v_k_x27_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_i_1023_, v___x_1029_);
lean_dec(v_i_1023_);
v_i_1023_ = v___x_1030_;
goto _start;
}
else
{
lean_dec(v_i_1023_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1022_ = stack[0].m_obj;
lean_object* v_i_1023_ = stack[1].m_obj;
lean_object* v_k_1024_ = stack[2].m_obj;
uint8_t v_res_1032_;
v_res_1032_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_keys_1022_, v_i_1023_, v_k_1024_);
stack->m_num = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1033_, lean_object* v_i_1034_, lean_object* v_k_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_keys_1033_, v_i_1034_, v_k_1035_);
lean_dec(v_k_1035_);
lean_dec_ref(v_keys_1033_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(lean_object* v_x_1038_, size_t v_x_1039_, lean_object* v_x_1040_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v_es_1041_; lean_object* v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; lean_object* v_j_1045_; lean_object* v___x_1046_; 
v_es_1041_ = lean_ctor_get(v_x_1038_, 0);
v___x_1042_ = lean_box(2);
v___x_1043_ = ((size_t)31ULL);
v___x_1044_ = lean_usize_land(v_x_1039_, v___x_1043_);
v_j_1045_ = lean_usize_to_nat(v___x_1044_);
v___x_1046_ = lean_array_get_borrowed(v___x_1042_, v_es_1041_, v_j_1045_);
lean_dec(v_j_1045_);
switch(lean_obj_tag(v___x_1046_))
{
case 0:
{
lean_object* v_key_1047_; uint8_t v___x_1048_; 
v_key_1047_ = lean_ctor_get(v___x_1046_, 0);
v___x_1048_ = lean_name_eq(v_x_1040_, v_key_1047_);
return v___x_1048_;
}
case 1:
{
lean_object* v_node_1049_; size_t v___x_1050_; size_t v___x_1051_; 
v_node_1049_ = lean_ctor_get(v___x_1046_, 0);
v___x_1050_ = ((size_t)5ULL);
v___x_1051_ = lean_usize_shift_right(v_x_1039_, v___x_1050_);
v_x_1038_ = v_node_1049_;
v_x_1039_ = v___x_1051_;
goto _start;
}
default: 
{
uint8_t v___x_1053_; 
v___x_1053_ = 0;
return v___x_1053_;
}
}
}
else
{
lean_object* v_ks_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_ks_1054_ = lean_ctor_get(v_x_1038_, 0);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_ks_1054_, v___x_1055_, v_x_1040_);
return v___x_1056_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1038_ = stack[0].m_obj;
size_t v_x_1039_ = stack[1].m_num;
lean_object* v_x_1040_ = stack[2].m_obj;
uint8_t v_res_1057_;
v_res_1057_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1038_, v_x_1039_, v_x_1040_);
stack->m_num = v_res_1057_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
size_t v_x_714__boxed_1061_; uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_x_714__boxed_1061_ = lean_unbox_usize(v_x_1059_);
lean_dec(v_x_1059_);
v_res_1062_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1058_, v_x_714__boxed_1061_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec_ref(v_x_1058_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
uint64_t v___y_1067_; 
if (lean_obj_tag(v_x_1065_) == 0)
{
uint64_t v___x_1070_; 
v___x_1070_ = 1723ULL;
v___y_1067_ = v___x_1070_;
goto v___jp_1066_;
}
else
{
uint64_t v_hash_1071_; 
v_hash_1071_ = lean_ctor_get_uint64(v_x_1065_, sizeof(void*)*2);
v___y_1067_ = v_hash_1071_;
goto v___jp_1066_;
}
v___jp_1066_:
{
size_t v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_uint64_to_usize(v___y_1067_);
v___x_1069_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1064_, v___x_1068_, v_x_1065_);
return v___x_1069_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1064_ = stack[0].m_obj;
lean_object* v_x_1065_ = stack[1].m_obj;
uint8_t v_res_1072_;
v_res_1072_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_x_1064_, v_x_1065_);
stack->m_num = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg___boxed(lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_x_1073_, v_x_1074_);
lean_dec(v_x_1074_);
lean_dec_ref(v_x_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
static lean_object* _init_l_Lean_registerStructure___closed__0(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = l_Lean_instInhabitedStructureState_default;
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_1086_, lean_object* v_e_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v_toEnvExtension_1089_; lean_object* v_addEntryFn_1090_; lean_object* v_asyncMode_1091_; uint8_t v_logWrites_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v_snd_1097_; lean_object* v_structName_1098_; lean_object* v_fields_1099_; uint8_t v___x_1100_; 
v___x_1088_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1089_ = lean_ctor_get(v___x_1088_, 0);
v_addEntryFn_1090_ = lean_ctor_get(v___x_1088_, 3);
v_asyncMode_1091_ = lean_ctor_get(v_toEnvExtension_1089_, 2);
v_logWrites_1092_ = lean_ctor_get_uint8(v_toEnvExtension_1089_, sizeof(void*)*6);
v___x_1093_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___x_1094_ = lean_box(0);
v___x_1095_ = 0;
lean_inc_ref(v_env_1086_);
v___x_1096_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1093_, v___x_1088_, v_env_1086_, v_asyncMode_1091_, v___x_1094_, v___x_1095_);
v_snd_1097_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_snd_1097_);
lean_dec(v___x_1096_);
v_structName_1098_ = lean_ctor_get(v_e_1087_, 0);
lean_inc(v_structName_1098_);
v_fields_1099_ = lean_ctor_get(v_e_1087_, 1);
lean_inc_ref(v_fields_1099_);
lean_dec_ref(v_e_1087_);
v___x_1100_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_snd_1097_, v_structName_1098_);
lean_dec(v_snd_1097_);
if (v___x_1100_ == 0)
{
size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___x_1113_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_sz_1101_ = lean_array_size(v_fields_1099_);
v___x_1102_ = ((size_t)0ULL);
lean_inc_ref(v_fields_1099_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(v_sz_1101_, v___x_1102_, v_fields_1099_);
v___x_1113_ = lean_array_get_size(v_fields_1099_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_nat_dec_eq(v___x_1113_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; uint8_t v___x_1125_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_sub(v___x_1113_, v___x_1120_);
v___x_1125_ = lean_nat_dec_le(v___x_1118_, v___x_1121_);
if (v___x_1125_ == 0)
{
lean_inc(v___x_1121_);
v___y_1123_ = v___x_1121_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___x_1118_;
goto v___jp_1122_;
}
v___jp_1122_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_nat_dec_le(v___y_1123_, v___x_1121_);
if (v___x_1124_ == 0)
{
lean_dec(v___x_1121_);
lean_inc(v___y_1123_);
v___y_1115_ = v___y_1123_;
v___y_1116_ = v___y_1123_;
goto v___jp_1114_;
}
else
{
v___y_1115_ = v___y_1123_;
v___y_1116_ = v___x_1121_;
goto v___jp_1114_;
}
}
}
else
{
v___y_1105_ = v_fields_1099_;
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; uint8_t v___x_1109_; 
v___x_1106_ = ((lean_object*)(l_Lean_registerStructure___closed__1));
lean_inc(v_structName_1098_);
v___x_1107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1107_, 0, v_structName_1098_);
lean_ctor_set(v___x_1107_, 1, v___x_1103_);
lean_ctor_set(v___x_1107_, 2, v___y_1105_);
lean_ctor_set(v___x_1107_, 3, v___x_1106_);
lean_inc(v_addEntryFn_1090_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_registerStructure___lam__0), 3, 2);
lean_closure_set(v___f_1108_, 0, v_addEntryFn_1090_);
lean_closure_set(v___f_1108_, 1, v___x_1107_);
v___x_1109_ = 1;
if (v_logWrites_1092_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_structName_1098_);
lean_inc_ref(v_toEnvExtension_1089_);
v___x_1110_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1089_, v_env_1086_, v___f_1108_, v_asyncMode_1091_, v___x_1094_, v___x_1109_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = l_Lean_Environment_logDeclChange(v_env_1086_, v_structName_1098_);
lean_inc_ref(v_toEnvExtension_1089_);
v___x_1112_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1089_, v___x_1111_, v___f_1108_, v_asyncMode_1091_, v___x_1094_, v___x_1109_);
return v___x_1112_;
}
}
v___jp_1114_:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v___x_1113_, v_fields_1099_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
v___y_1105_ = v___x_1117_;
goto v___jp_1104_;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v_fields_1099_);
v___x_1126_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1127_ = ((lean_object*)(l_Lean_registerStructure___closed__3));
v___x_1128_ = lean_unsigned_to_nat(115u);
v___x_1129_ = lean_unsigned_to_nat(4u);
v___x_1130_ = ((lean_object*)(l_Lean_registerStructure___closed__4));
v___x_1131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_structName_1098_, v___x_1100_);
v___x_1132_ = lean_string_append(v___x_1130_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_registerStructure___closed__5));
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
v___x_1135_ = l_mkPanicMessageWithDecl(v___x_1126_, v___x_1127_, v___x_1128_, v___x_1129_, v___x_1134_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = lean_panic_fn_borrowed(v_env_1086_, v___x_1135_);
lean_dec_ref(v_env_1086_);
return v___x_1136_;
}
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_x_1138_, v_x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1138_ = stack[1].m_obj;
lean_object* v_x_1139_ = stack[2].m_obj;
uint8_t v_res_1141_;
v_res_1141_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(lean_box(0), v_x_1138_, v_x_1139_);
stack->m_num = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(v_00_u03b2_1142_, v_x_1143_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec_ref(v_x_1143_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2(lean_object* v_n_1147_, lean_object* v_as_1148_, lean_object* v_lo_1149_, lean_object* v_hi_1150_, lean_object* v_w_1151_, lean_object* v_hlo_1152_, lean_object* v_hhi_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_1147_, v_as_1148_, v_lo_1149_, v_hi_1150_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___boxed(lean_object* v_n_1155_, lean_object* v_as_1156_, lean_object* v_lo_1157_, lean_object* v_hi_1158_, lean_object* v_w_1159_, lean_object* v_hlo_1160_, lean_object* v_hhi_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2(v_n_1155_, v_as_1156_, v_lo_1157_, v_hi_1158_, v_w_1159_, v_hlo_1160_, v_hhi_1161_);
lean_dec(v_hi_1158_);
lean_dec(v_n_1155_);
return v_res_1162_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, size_t v_x_1165_, lean_object* v_x_1166_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1164_, v_x_1165_, v_x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1164_ = stack[1].m_obj;
size_t v_x_1165_ = stack[2].m_num;
lean_object* v_x_1166_ = stack[3].m_obj;
uint8_t v_res_1168_;
v_res_1168_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(lean_box(0), v_x_1164_, v_x_1165_, v_x_1166_);
stack->m_num = v_res_1168_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
size_t v_x_977__boxed_1173_; uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_x_977__boxed_1173_ = lean_unbox_usize(v_x_1171_);
lean_dec(v_x_1171_);
v_res_1174_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(v_00_u03b2_1169_, v_x_1170_, v_x_977__boxed_1173_, v_x_1172_);
lean_dec(v_x_1172_);
lean_dec_ref(v_x_1170_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3(lean_object* v_n_1176_, lean_object* v_lo_1177_, lean_object* v_hi_1178_, lean_object* v_hhi_1179_, lean_object* v_pivot_1180_, lean_object* v_as_1181_, lean_object* v_i_1182_, lean_object* v_k_1183_, lean_object* v_ilo_1184_, lean_object* v_ik_1185_, lean_object* v_w_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_1178_, v_pivot_1180_, v_as_1181_, v_i_1182_, v_k_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___boxed(lean_object* v_n_1188_, lean_object* v_lo_1189_, lean_object* v_hi_1190_, lean_object* v_hhi_1191_, lean_object* v_pivot_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_k_1195_, lean_object* v_ilo_1196_, lean_object* v_ik_1197_, lean_object* v_w_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3(v_n_1188_, v_lo_1189_, v_hi_1190_, v_hhi_1191_, v_pivot_1192_, v_as_1193_, v_i_1194_, v_k_1195_, v_ilo_1196_, v_ik_1197_, v_w_1198_);
lean_dec_ref(v_pivot_1192_);
lean_dec(v_hi_1190_);
lean_dec(v_lo_1189_);
lean_dec(v_n_1188_);
return v_res_1199_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1200_, lean_object* v_keys_1201_, lean_object* v_vals_1202_, lean_object* v_heq_1203_, lean_object* v_i_1204_, lean_object* v_k_1205_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_keys_1201_, v_i_1204_, v_k_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1201_ = stack[1].m_obj;
lean_object* v_vals_1202_ = stack[2].m_obj;
lean_object* v_i_1204_ = stack[4].m_obj;
lean_object* v_k_1205_ = stack[5].m_obj;
uint8_t v_res_1207_;
v_res_1207_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(lean_box(0), v_keys_1201_, v_vals_1202_, lean_box(0), v_i_1204_, v_k_1205_);
stack->m_num = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1208_, lean_object* v_keys_1209_, lean_object* v_vals_1210_, lean_object* v_heq_1211_, lean_object* v_i_1212_, lean_object* v_k_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(v_00_u03b2_1208_, v_keys_1209_, v_vals_1210_, v_heq_1211_, v_i_1212_, v_k_1213_);
lean_dec(v_k_1213_);
lean_dec_ref(v_vals_1210_);
lean_dec_ref(v_keys_1209_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v_val_1216_, lean_object* v_parentInfo_1217_, lean_object* v_addEntryFn_1218_, uint8_t v_logWrites_1219_, lean_object* v_toEnvExtension_1220_, lean_object* v_asyncMode_1221_, lean_object* v___x_1222_, lean_object* v_structName_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v_structName_1225_; lean_object* v_fieldNames_1226_; lean_object* v_fieldInfo_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1239_; 
v_structName_1225_ = lean_ctor_get(v_val_1216_, 0);
v_fieldNames_1226_ = lean_ctor_get(v_val_1216_, 1);
v_fieldInfo_1227_ = lean_ctor_get(v_val_1216_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_val_1216_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_val_1216_, 3);
lean_dec(v_unused_1240_);
v___x_1229_ = v_val_1216_;
v_isShared_1230_ = v_isSharedCheck_1239_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_fieldInfo_1227_);
lean_inc(v_fieldNames_1226_);
lean_inc(v_structName_1225_);
lean_dec(v_val_1216_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1239_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 3, v_parentInfo_1217_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_structName_1225_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_fieldNames_1226_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_fieldInfo_1227_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_parentInfo_1217_);
v___x_1232_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___f_1233_; uint8_t v___x_1234_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Lean_registerStructure___lam__0), 3, 2);
lean_closure_set(v___f_1233_, 0, v_addEntryFn_1218_);
lean_closure_set(v___f_1233_, 1, v___x_1232_);
v___x_1234_ = 1;
if (v_logWrites_1219_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_structName_1223_);
v___x_1235_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1220_, v_x_1224_, v___f_1233_, v_asyncMode_1221_, v___x_1222_, v___x_1234_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_Environment_logDeclChange(v_x_1224_, v_structName_1223_);
v___x_1237_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1220_, v___x_1236_, v___f_1233_, v_asyncMode_1221_, v___x_1222_, v___x_1234_);
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_setStructureParents___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1216_ = stack[0].m_obj;
lean_object* v_parentInfo_1217_ = stack[1].m_obj;
lean_object* v_addEntryFn_1218_ = stack[2].m_obj;
uint8_t v_logWrites_1219_ = stack[3].m_num;
lean_object* v_toEnvExtension_1220_ = stack[4].m_obj;
lean_object* v_asyncMode_1221_ = stack[5].m_obj;
lean_object* v___x_1222_ = stack[6].m_obj;
lean_object* v_structName_1223_ = stack[7].m_obj;
lean_object* v_x_1224_ = stack[8].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l_Lean_setStructureParents___redArg___lam__1(v_val_1216_, v_parentInfo_1217_, v_addEntryFn_1218_, v_logWrites_1219_, v_toEnvExtension_1220_, v_asyncMode_1221_, v___x_1222_, v_structName_1223_, v_x_1224_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1___boxed(lean_object* v_val_1242_, lean_object* v_parentInfo_1243_, lean_object* v_addEntryFn_1244_, lean_object* v_logWrites_1245_, lean_object* v_toEnvExtension_1246_, lean_object* v_asyncMode_1247_, lean_object* v___x_1248_, lean_object* v_structName_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v_logWrites_boxed_1251_; lean_object* v_res_1252_; 
v_logWrites_boxed_1251_ = lean_unbox(v_logWrites_1245_);
v_res_1252_ = l_Lean_setStructureParents___redArg___lam__1(v_val_1242_, v_parentInfo_1243_, v_addEntryFn_1244_, v_logWrites_boxed_1251_, v_toEnvExtension_1246_, v_asyncMode_1247_, v___x_1248_, v_structName_1249_, v_x_1250_);
lean_dec(v_asyncMode_1247_);
return v_res_1252_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__0___closed__0));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__0___closed__2));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v_structName_1262_, lean_object* v_parentInfo_1263_, lean_object* v_modifyEnv_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_____do__lift_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v_toEnvExtension_1269_; lean_object* v_addEntryFn_1270_; lean_object* v_asyncMode_1271_; uint8_t v_logWrites_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1293_; 
v___x_1268_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1269_ = lean_ctor_get(v___x_1268_, 0);
v_addEntryFn_1270_ = lean_ctor_get(v___x_1268_, 3);
v_asyncMode_1271_ = lean_ctor_get(v_toEnvExtension_1269_, 2);
v_logWrites_1272_ = lean_ctor_get_uint8(v_toEnvExtension_1269_, sizeof(void*)*6);
v___x_1273_ = lean_box(0);
v___x_1274_ = 0;
v___x_1275_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1259_, v___x_1268_, v_____do__lift_1267_, v_asyncMode_1271_, v___x_1273_, v___x_1274_);
v_snd_1276_ = lean_ctor_get(v___x_1275_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1294_);
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1293_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1293_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; 
lean_inc(v_structName_1262_);
v___x_1280_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1260_, v___x_1261_, v_snd_1276_, v_structName_1262_);
lean_dec(v_snd_1276_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
lean_del_object(v___x_1278_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_box(v_logWrites_1272_);
lean_inc(v_asyncMode_1271_);
lean_inc_ref(v_toEnvExtension_1269_);
lean_inc(v_addEntryFn_1270_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_1283_, 0, v_val_1281_);
lean_closure_set(v___f_1283_, 1, v_parentInfo_1263_);
lean_closure_set(v___f_1283_, 2, v_addEntryFn_1270_);
lean_closure_set(v___f_1283_, 3, v___x_1282_);
lean_closure_set(v___f_1283_, 4, v_toEnvExtension_1269_);
lean_closure_set(v___f_1283_, 5, v_asyncMode_1271_);
lean_closure_set(v___f_1283_, 6, v___x_1273_);
lean_closure_set(v___f_1283_, 7, v_structName_1262_);
v___x_1284_ = lean_apply_1(v_modifyEnv_1264_, v___f_1283_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v___x_1280_);
lean_dec(v_modifyEnv_1264_);
lean_dec_ref(v_parentInfo_1263_);
v___x_1285_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__0___closed__1, &l_Lean_setStructureParents___redArg___lam__0___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__0___closed__1);
v___x_1286_ = l_Lean_MessageData_ofName(v_structName_1262_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 7);
lean_ctor_set(v___x_1278_, 1, v___x_1286_);
lean_ctor_set(v___x_1278_, 0, v___x_1285_);
v___x_1288_ = v___x_1278_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__0___closed__3, &l_Lean_setStructureParents___redArg___lam__0___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__0___closed__3);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_throwError___redArg(v_inst_1265_, v_inst_1266_, v___x_1290_);
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_structName_1300_, lean_object* v_parentInfo_1301_){
_start:
{
lean_object* v_toBind_1302_; lean_object* v_getEnv_1303_; lean_object* v_modifyEnv_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; 
v_toBind_1302_ = lean_ctor_get(v_inst_1297_, 1);
lean_inc(v_toBind_1302_);
v_getEnv_1303_ = lean_ctor_get(v_inst_1298_, 0);
lean_inc(v_getEnv_1303_);
v_modifyEnv_1304_ = lean_ctor_get(v_inst_1298_, 1);
lean_inc(v_modifyEnv_1304_);
lean_dec_ref(v_inst_1298_);
v___x_1305_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1306_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1307_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0), 9, 8);
lean_closure_set(v___f_1308_, 0, v___x_1307_);
lean_closure_set(v___f_1308_, 1, v___x_1305_);
lean_closure_set(v___f_1308_, 2, v___x_1306_);
lean_closure_set(v___f_1308_, 3, v_structName_1300_);
lean_closure_set(v___f_1308_, 4, v_parentInfo_1301_);
lean_closure_set(v___f_1308_, 5, v_modifyEnv_1304_);
lean_closure_set(v___f_1308_, 6, v_inst_1297_);
lean_closure_set(v___f_1308_, 7, v_inst_1299_);
v___x_1309_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v_getEnv_1303_, v___f_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_structName_1314_, lean_object* v_parentInfo_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_setStructureParents___redArg(v_inst_1311_, v_inst_1312_, v_inst_1313_, v_structName_1314_, v_parentInfo_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1317_, lean_object* v_k_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_m_1323_; lean_object* v_a_1324_; uint8_t v___x_1325_; 
v___x_1321_ = lean_nat_add(v_x_1319_, v_x_1320_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v_m_1323_ = lean_nat_shiftr(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
v_a_1324_ = lean_array_fget_borrowed(v_as_1317_, v_m_1323_);
v___x_1325_ = l_Lean_StructureInfo_lt(v_a_1324_, v_k_1318_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
lean_dec(v_x_1320_);
v___x_1326_ = l_Lean_StructureInfo_lt(v_k_1318_, v_a_1324_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v_m_1323_);
lean_dec(v_x_1319_);
lean_inc(v_a_1324_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_a_1324_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_nat_dec_eq(v_m_1323_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_nat_sub(v_m_1323_, v___x_1322_);
lean_dec(v_m_1323_);
v___x_1331_ = lean_nat_dec_lt(v___x_1330_, v_x_1319_);
if (v___x_1331_ == 0)
{
v_x_1320_ = v___x_1330_;
goto _start;
}
else
{
lean_object* v___x_1333_; 
lean_dec(v___x_1330_);
lean_dec(v_x_1319_);
v___x_1333_ = lean_box(0);
return v___x_1333_;
}
}
else
{
lean_object* v___x_1334_; 
lean_dec(v_m_1323_);
lean_dec(v_x_1319_);
v___x_1334_ = lean_box(0);
return v___x_1334_;
}
}
}
else
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
lean_dec(v_x_1319_);
v___x_1335_ = lean_nat_add(v_m_1323_, v___x_1322_);
lean_dec(v_m_1323_);
v___x_1336_ = lean_nat_dec_le(v___x_1335_, v_x_1320_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v___x_1335_);
lean_dec(v_x_1320_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
v_x_1319_ = v___x_1335_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1339_, lean_object* v_k_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1339_, v_k_1340_, v_x_1341_, v_x_1342_);
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_as_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1344_, lean_object* v_vals_1345_, lean_object* v_i_1346_, lean_object* v_k_1347_){
_start:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_array_get_size(v_keys_1344_);
v___x_1349_ = lean_nat_dec_lt(v_i_1346_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_i_1346_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
lean_object* v_k_x27_1351_; uint8_t v___x_1352_; 
v_k_x27_1351_ = lean_array_fget_borrowed(v_keys_1344_, v_i_1346_);
v___x_1352_ = lean_name_eq(v_k_1347_, v_k_x27_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_add(v_i_1346_, v___x_1353_);
lean_dec(v_i_1346_);
v_i_1346_ = v___x_1354_;
goto _start;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_array_fget_borrowed(v_vals_1345_, v_i_1346_);
lean_dec(v_i_1346_);
lean_inc(v___x_1356_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_i_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1358_, v_vals_1359_, v_i_1360_, v_k_1361_);
lean_dec(v_k_1361_);
lean_dec_ref(v_vals_1359_);
lean_dec_ref(v_keys_1358_);
return v_res_1362_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1363_, size_t v_x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
lean_object* v_es_1366_; lean_object* v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v_j_1370_; lean_object* v___x_1371_; 
v_es_1366_ = lean_ctor_get(v_x_1363_, 0);
v___x_1367_ = lean_box(2);
v___x_1368_ = ((size_t)31ULL);
v___x_1369_ = lean_usize_land(v_x_1364_, v___x_1368_);
v_j_1370_ = lean_usize_to_nat(v___x_1369_);
v___x_1371_ = lean_array_get_borrowed(v___x_1367_, v_es_1366_, v_j_1370_);
lean_dec(v_j_1370_);
switch(lean_obj_tag(v___x_1371_))
{
case 0:
{
lean_object* v_key_1372_; lean_object* v_val_1373_; uint8_t v___x_1374_; 
v_key_1372_ = lean_ctor_get(v___x_1371_, 0);
v_val_1373_ = lean_ctor_get(v___x_1371_, 1);
v___x_1374_ = lean_name_eq(v_x_1365_, v_key_1372_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
lean_inc(v_val_1373_);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_val_1373_);
return v___x_1376_;
}
}
case 1:
{
lean_object* v_node_1377_; size_t v___x_1378_; size_t v___x_1379_; 
v_node_1377_ = lean_ctor_get(v___x_1371_, 0);
v___x_1378_ = ((size_t)5ULL);
v___x_1379_ = lean_usize_shift_right(v_x_1364_, v___x_1378_);
v_x_1363_ = v_node_1377_;
v_x_1364_ = v___x_1379_;
goto _start;
}
default: 
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
}
}
else
{
lean_object* v_ks_1382_; lean_object* v_vs_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_ks_1382_ = lean_ctor_get(v_x_1363_, 0);
v_vs_1383_ = lean_ctor_get(v_x_1363_, 1);
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1382_, v_vs_1383_, v___x_1384_, v_x_1365_);
return v___x_1385_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1363_ = stack[0].m_obj;
size_t v_x_1364_ = stack[1].m_num;
lean_object* v_x_1365_ = stack[2].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1363_, v_x_1364_, v_x_1365_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
size_t v_x_425__boxed_1390_; lean_object* v_res_1391_; 
v_x_425__boxed_1390_ = lean_unbox_usize(v_x_1388_);
lean_dec(v_x_1388_);
v_res_1391_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1387_, v_x_425__boxed_1390_, v_x_1389_);
lean_dec(v_x_1389_);
lean_dec_ref(v_x_1387_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
uint64_t v___y_1395_; 
if (lean_obj_tag(v_x_1393_) == 0)
{
uint64_t v___x_1398_; 
v___x_1398_ = 1723ULL;
v___y_1395_ = v___x_1398_;
goto v___jp_1394_;
}
else
{
uint64_t v_hash_1399_; 
v_hash_1399_ = lean_ctor_get_uint64(v_x_1393_, sizeof(void*)*2);
v___y_1395_ = v_hash_1399_;
goto v___jp_1394_;
}
v___jp_1394_:
{
size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_uint64_to_usize(v___y_1395_);
v___x_1397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1392_, v___x_1396_, v_x_1393_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1400_, v_x_1401_);
lean_dec(v_x_1401_);
lean_dec_ref(v_x_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1403_, lean_object* v_structName_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___x_1406_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1403_, v_structName_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; lean_object* v_toEnvExtension_1408_; lean_object* v_asyncMode_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v_snd_1413_; lean_object* v___x_1414_; 
v___x_1407_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1408_ = lean_ctor_get(v___x_1407_, 0);
v_asyncMode_1409_ = lean_ctor_get(v_toEnvExtension_1408_, 2);
v___x_1410_ = lean_box(0);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1405_, v___x_1407_, v_env_1403_, v_asyncMode_1409_, v___x_1410_, v___x_1411_);
v_snd_1413_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_snd_1413_);
lean_dec(v___x_1412_);
v___x_1414_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1413_, v_structName_1404_);
lean_dec(v_structName_1404_);
lean_dec(v_snd_1413_);
return v___x_1414_;
}
else
{
lean_object* v_val_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_val_1415_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1416_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1417_ = 0;
v___x_1418_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1405_, v___x_1416_, v_env_1403_, v_val_1415_, v___x_1417_);
lean_dec(v_val_1415_);
lean_dec_ref(v_env_1403_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_array_get_size(v___x_1418_);
v___x_1421_ = lean_nat_dec_lt(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v___x_1418_);
lean_dec(v_structName_1404_);
v___x_1422_ = lean_box(0);
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_sub(v___x_1420_, v___x_1423_);
v___x_1425_ = lean_nat_dec_le(v___x_1419_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec(v___x_1424_);
lean_dec_ref(v___x_1418_);
lean_dec(v_structName_1404_);
v___x_1426_ = lean_box(0);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1428_, 0, v_structName_1404_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
lean_ctor_set(v___x_1428_, 3, v___x_1427_);
v___x_1429_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1418_, v___x_1428_, v___x_1419_, v___x_1424_);
lean_dec_ref_known(v___x_1428_, 4);
lean_dec_ref(v___x_1418_);
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1434_, v_x_1435_, v_x_1436_);
lean_dec(v_x_1436_);
lean_dec_ref(v_x_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1438_, lean_object* v_k_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1438_, v_k_1439_, v_x_1440_, v_x_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1444_, lean_object* v_k_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1444_, v_k_1445_, v_x_1446_, v_x_1447_, v_x_1448_);
lean_dec_ref(v_k_1445_);
lean_dec_ref(v_as_1444_);
return v_res_1449_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1450_, lean_object* v_x_1451_, size_t v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1451_, v_x_1452_, v_x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1451_ = stack[1].m_obj;
size_t v_x_1452_ = stack[2].m_num;
lean_object* v_x_1453_ = stack[3].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_box(0), v_x_1451_, v_x_1452_, v_x_1453_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
size_t v_x_626__boxed_1460_; lean_object* v_res_1461_; 
v_x_626__boxed_1460_ = lean_unbox_usize(v_x_1458_);
lean_dec(v_x_1458_);
v_res_1461_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1456_, v_x_1457_, v_x_626__boxed_1460_, v_x_1459_);
lean_dec(v_x_1459_);
lean_dec_ref(v_x_1457_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_heq_1465_, lean_object* v_i_1466_, lean_object* v_k_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1463_, v_vals_1464_, v_i_1466_, v_k_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1469_, lean_object* v_keys_1470_, lean_object* v_vals_1471_, lean_object* v_heq_1472_, lean_object* v_i_1473_, lean_object* v_k_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1469_, v_keys_1470_, v_vals_1471_, v_heq_1472_, v_i_1473_, v_k_1474_);
lean_dec(v_k_1474_);
lean_dec_ref(v_vals_1471_);
lean_dec_ref(v_keys_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1478_ = lean_panic_fn_borrowed(v___x_1477_, v_msg_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__2(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1482_ = lean_unsigned_to_nat(4u);
v___x_1483_ = lean_unsigned_to_nat(146u);
v___x_1484_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1485_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1487_, lean_object* v_structName_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_getStructureInfo_x3f(v_env_1487_, v_structName_1488_);
if (lean_obj_tag(v___x_1489_) == 1)
{
lean_object* v_val_1490_; 
v_val_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_val_1490_);
lean_dec_ref_known(v___x_1489_, 1);
return v_val_1490_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v___x_1489_);
v___x_1491_ = lean_obj_once(&l_Lean_getStructureInfo___closed__2, &l_Lean_getStructureInfo___closed__2_once, _init_l_Lean_getStructureInfo___closed__2);
v___x_1492_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1491_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1493_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1495_ = lean_panic_fn_borrowed(v___x_1494_, v_msg_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1497_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1498_ = lean_unsigned_to_nat(9u);
v___x_1499_ = lean_unsigned_to_nat(161u);
v___x_1500_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1501_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1502_ = l_mkPanicMessageWithDecl(v___x_1501_, v___x_1500_, v___x_1499_, v___x_1498_, v___x_1497_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1505_ = lean_unsigned_to_nat(11u);
v___x_1506_ = lean_unsigned_to_nat(160u);
v___x_1507_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1508_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1509_ = l_mkPanicMessageWithDecl(v___x_1508_, v___x_1507_, v___x_1506_, v___x_1505_, v___x_1504_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1510_, lean_object* v_constName_1511_){
_start:
{
uint8_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = 0;
lean_inc_ref(v_env_1510_);
v___x_1519_ = l_Lean_Environment_find_x3f(v_env_1510_, v_constName_1511_, v___x_1518_);
if (lean_obj_tag(v___x_1519_) == 1)
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
if (lean_obj_tag(v_val_1520_) == 5)
{
lean_object* v_val_1521_; lean_object* v_ctors_1522_; 
v_val_1521_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_val_1521_);
lean_dec_ref_known(v_val_1520_, 1);
v_ctors_1522_ = lean_ctor_get(v_val_1521_, 4);
lean_inc(v_ctors_1522_);
lean_dec_ref(v_val_1521_);
if (lean_obj_tag(v_ctors_1522_) == 1)
{
lean_object* v_tail_1523_; 
v_tail_1523_ = lean_ctor_get(v_ctors_1522_, 1);
if (lean_obj_tag(v_tail_1523_) == 0)
{
lean_object* v_head_1524_; lean_object* v___x_1525_; 
v_head_1524_ = lean_ctor_get(v_ctors_1522_, 0);
lean_inc(v_head_1524_);
lean_dec_ref_known(v_ctors_1522_, 2);
v___x_1525_ = l_Lean_Environment_find_x3f(v_env_1510_, v_head_1524_, v___x_1518_);
if (lean_obj_tag(v___x_1525_) == 1)
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1525_, 1);
if (lean_obj_tag(v_val_1526_) == 6)
{
lean_object* v_val_1527_; 
v_val_1527_ = lean_ctor_get(v_val_1526_, 0);
lean_inc_ref(v_val_1527_);
lean_dec_ref_known(v_val_1526_, 1);
return v_val_1527_;
}
else
{
lean_dec(v_val_1526_);
goto v___jp_1515_;
}
}
else
{
lean_dec(v___x_1525_);
goto v___jp_1515_;
}
}
else
{
lean_dec_ref_known(v_ctors_1522_, 2);
lean_dec_ref(v_env_1510_);
goto v___jp_1512_;
}
}
else
{
lean_dec(v_ctors_1522_);
lean_dec_ref(v_env_1510_);
goto v___jp_1512_;
}
}
else
{
lean_dec(v_val_1520_);
lean_dec_ref(v_env_1510_);
goto v___jp_1512_;
}
}
else
{
lean_dec(v___x_1519_);
lean_dec_ref(v_env_1510_);
goto v___jp_1512_;
}
v___jp_1512_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1514_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1513_);
return v___x_1514_;
}
v___jp_1515_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1517_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1516_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1528_, lean_object* v_structName_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v_fieldNames_1531_; 
v___x_1530_ = l_Lean_getStructureInfo(v_env_1528_, v_structName_1529_);
v_fieldNames_1531_ = lean_ctor_get(v___x_1530_, 1);
lean_inc_ref(v_fieldNames_1531_);
lean_dec_ref(v___x_1530_);
return v_fieldNames_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1532_, lean_object* v_structName_1533_, lean_object* v_fieldName_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_getStructureInfo_x3f(v_env_1532_, v_structName_1533_);
if (lean_obj_tag(v___x_1535_) == 1)
{
lean_object* v_val_1536_; lean_object* v_fieldInfo_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_val_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v_fieldInfo_1537_ = lean_ctor_get(v_val_1536_, 2);
lean_inc_ref(v_fieldInfo_1537_);
lean_dec(v_val_1536_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_array_get_size(v_fieldInfo_1537_);
v___x_1540_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref(v_fieldInfo_1537_);
lean_dec(v_fieldName_1534_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_sub(v___x_1539_, v___x_1542_);
v___x_1544_ = lean_nat_dec_le(v___x_1538_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec(v___x_1543_);
lean_dec_ref(v_fieldInfo_1537_);
lean_dec(v_fieldName_1534_);
v___x_1545_ = lean_box(0);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_box(0);
v___x_1548_ = 0;
v___x_1549_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1549_, 0, v_fieldName_1534_);
lean_ctor_set(v___x_1549_, 1, v___x_1546_);
lean_ctor_set(v___x_1549_, 2, v___x_1547_);
lean_ctor_set(v___x_1549_, 3, v___x_1547_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*4, v___x_1548_);
v___x_1550_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1537_, v___x_1549_, v___x_1538_, v___x_1543_);
lean_dec_ref_known(v___x_1549_, 4);
lean_dec_ref(v_fieldInfo_1537_);
return v___x_1550_;
}
}
}
else
{
lean_object* v___x_1551_; 
lean_dec(v___x_1535_);
lean_dec(v_fieldName_1534_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1552_, lean_object* v_structName_1553_, lean_object* v_fieldName_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_getFieldInfo_x3f(v_env_1552_, v_structName_1553_, v_fieldName_1554_);
if (lean_obj_tag(v___x_1555_) == 1)
{
lean_object* v_val_1556_; lean_object* v_subobject_x3f_1557_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_subobject_x3f_1557_ = lean_ctor_get(v_val_1556_, 2);
lean_inc(v_subobject_x3f_1557_);
lean_dec(v_val_1556_);
return v_subobject_x3f_1557_;
}
else
{
lean_object* v___x_1558_; 
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1559_, lean_object* v_structName_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v_parentInfo_1562_; 
v___x_1561_ = l_Lean_getStructureInfo(v_env_1559_, v_structName_1560_);
v_parentInfo_1562_ = lean_ctor_get(v___x_1561_, 3);
lean_inc_ref(v_parentInfo_1562_);
lean_dec_ref(v___x_1561_);
return v_parentInfo_1562_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1563_, lean_object* v_structName_1564_, lean_object* v_as_1565_, size_t v_i_1566_, size_t v_stop_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___y_1570_; uint8_t v___x_1574_; 
v___x_1574_ = lean_usize_dec_eq(v_i_1566_, v_stop_1567_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_array_uget_borrowed(v_as_1565_, v_i_1566_);
lean_inc(v___x_1575_);
lean_inc(v_structName_1564_);
lean_inc_ref(v_env_1563_);
v___x_1576_ = l_Lean_isSubobjectField_x3f(v_env_1563_, v_structName_1564_, v___x_1575_);
if (lean_obj_tag(v___x_1576_) == 0)
{
v___y_1570_ = v_b_1568_;
goto v___jp_1569_;
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1578_; 
v_val_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_array_push(v_b_1568_, v_val_1577_);
v___y_1570_ = v___x_1578_;
goto v___jp_1569_;
}
}
else
{
lean_dec(v_structName_1564_);
lean_dec_ref(v_env_1563_);
return v_b_1568_;
}
v___jp_1569_:
{
size_t v___x_1571_; size_t v___x_1572_; 
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1566_, v___x_1571_);
v_i_1566_ = v___x_1572_;
v_b_1568_ = v___y_1570_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1563_ = stack[0].m_obj;
lean_object* v_structName_1564_ = stack[1].m_obj;
lean_object* v_as_1565_ = stack[2].m_obj;
size_t v_i_1566_ = stack[3].m_num;
size_t v_stop_1567_ = stack[4].m_num;
lean_object* v_b_1568_ = stack[5].m_obj;
lean_object* v_res_1579_;
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1563_, v_structName_1564_, v_as_1565_, v_i_1566_, v_stop_1567_, v_b_1568_);
stack->m_obj
 = v_res_1579_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1580_, lean_object* v_structName_1581_, lean_object* v_as_1582_, lean_object* v_i_1583_, lean_object* v_stop_1584_, lean_object* v_b_1585_){
_start:
{
size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; lean_object* v_res_1588_; 
v_i_boxed_1586_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1584_);
lean_dec(v_stop_1584_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1580_, v_structName_1581_, v_as_1582_, v_i_boxed_1586_, v_stop_boxed_1587_, v_b_1585_);
lean_dec_ref(v_as_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1589_, lean_object* v_structName_1590_, lean_object* v_as_1591_, lean_object* v_start_1592_, lean_object* v_stop_1593_){
_start:
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1595_ = lean_nat_dec_lt(v_start_1592_, v_stop_1593_);
if (v___x_1595_ == 0)
{
lean_dec(v_structName_1590_);
lean_dec_ref(v_env_1589_);
return v___x_1594_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_array_get_size(v_as_1591_);
v___x_1597_ = lean_nat_dec_le(v_stop_1593_, v___x_1596_);
if (v___x_1597_ == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_nat_dec_lt(v_start_1592_, v___x_1596_);
if (v___x_1598_ == 0)
{
lean_dec(v_structName_1590_);
lean_dec_ref(v_env_1589_);
return v___x_1594_;
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_usize_of_nat(v_start_1592_);
v___x_1600_ = lean_usize_of_nat(v___x_1596_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1589_, v_structName_1590_, v_as_1591_, v___x_1599_, v___x_1600_, v___x_1594_);
return v___x_1601_;
}
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_usize_of_nat(v_start_1592_);
v___x_1603_ = lean_usize_of_nat(v_stop_1593_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1589_, v_structName_1590_, v_as_1591_, v___x_1602_, v___x_1603_, v___x_1594_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1605_, lean_object* v_structName_1606_, lean_object* v_as_1607_, lean_object* v_start_1608_, lean_object* v_stop_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1605_, v_structName_1606_, v_as_1607_, v_start_1608_, v_stop_1609_);
lean_dec(v_stop_1609_);
lean_dec(v_start_1608_);
lean_dec_ref(v_as_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1611_, lean_object* v_structName_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v_structName_1612_);
lean_inc_ref(v_env_1611_);
v___x_1613_ = l_Lean_getStructureFields(v_env_1611_, v_structName_1612_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_array_get_size(v___x_1613_);
v___x_1616_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1611_, v_structName_1612_, v___x_1613_, v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1613_);
return v___x_1616_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1617_, lean_object* v_as_1618_, size_t v_i_1619_, size_t v_stop_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_usize_dec_eq(v_i_1619_, v_stop_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_array_uget_borrowed(v_as_1618_, v_i_1619_);
v___x_1623_ = lean_name_eq(v_a_1617_, v___x_1622_);
if (v___x_1623_ == 0)
{
size_t v___x_1624_; size_t v___x_1625_; 
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = lean_usize_add(v_i_1619_, v___x_1624_);
v_i_1619_ = v___x_1625_;
goto _start;
}
else
{
return v___x_1623_;
}
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
return v___x_1627_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1617_ = stack[0].m_obj;
lean_object* v_as_1618_ = stack[1].m_obj;
size_t v_i_1619_ = stack[2].m_num;
size_t v_stop_1620_ = stack[3].m_num;
uint8_t v_res_1628_;
v_res_1628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1617_, v_as_1618_, v_i_1619_, v_stop_1620_);
stack->m_num = v_res_1628_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1629_, lean_object* v_as_1630_, lean_object* v_i_1631_, lean_object* v_stop_1632_){
_start:
{
size_t v_i_boxed_1633_; size_t v_stop_boxed_1634_; uint8_t v_res_1635_; lean_object* v_r_1636_; 
v_i_boxed_1633_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_stop_boxed_1634_ = lean_unbox_usize(v_stop_1632_);
lean_dec(v_stop_1632_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1629_, v_as_1630_, v_i_boxed_1633_, v_stop_boxed_1634_);
lean_dec_ref(v_as_1630_);
lean_dec(v_a_1629_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_array_get_size(v_as_1637_);
v___x_1641_ = lean_nat_dec_lt(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
return v___x_1641_;
}
else
{
if (v___x_1641_ == 0)
{
return v___x_1641_;
}
else
{
size_t v___x_1642_; size_t v___x_1643_; uint8_t v___x_1644_; 
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = lean_usize_of_nat(v___x_1640_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1638_, v_as_1637_, v___x_1642_, v___x_1643_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_findField_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1637_ = stack[0].m_obj;
lean_object* v_a_1638_ = stack[1].m_obj;
uint8_t v_res_1645_;
v_res_1645_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1637_, v_a_1638_);
stack->m_num = v_res_1645_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1646_, lean_object* v_a_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_as_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1653_, lean_object* v_structName_1654_, lean_object* v_fieldName_1655_){
_start:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
lean_inc(v_structName_1654_);
lean_inc_ref(v_env_1653_);
v___x_1656_ = l_Lean_getStructureFields(v_env_1653_, v_structName_1654_);
v___x_1657_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1656_, v_fieldName_1655_);
lean_dec_ref(v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; size_t v_sz_1661_; size_t v___x_1662_; lean_object* v___x_1663_; lean_object* v_fst_1664_; 
lean_inc_ref(v_env_1653_);
v___x_1658_ = l_Lean_getStructureSubobjects(v_env_1653_, v_structName_1654_);
v___x_1659_ = lean_box(0);
v___x_1660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1661_ = lean_array_size(v___x_1658_);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1653_, v_fieldName_1655_, v___x_1658_, v_sz_1661_, v___x_1662_, v___x_1660_);
lean_dec_ref(v___x_1658_);
v_fst_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_fst_1664_);
lean_dec_ref(v___x_1663_);
if (lean_obj_tag(v_fst_1664_) == 0)
{
return v___x_1659_;
}
else
{
lean_object* v_val_1665_; 
v_val_1665_ = lean_ctor_get(v_fst_1664_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_fst_1664_, 1);
return v_val_1665_;
}
}
else
{
lean_object* v___x_1666_; 
lean_dec_ref(v_env_1653_);
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_structName_1654_);
return v___x_1666_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1667_, lean_object* v_fieldName_1668_, lean_object* v_as_1669_, size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_b_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v_env_1667_);
lean_inc_ref(v_b_1672_);
return v_b_1672_;
}
else
{
lean_object* v___x_1674_; lean_object* v_a_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_box(0);
v_a_1675_ = lean_array_uget_borrowed(v_as_1669_, v_i_1671_);
lean_inc(v_a_1675_);
lean_inc_ref(v_env_1667_);
v___x_1676_ = l_Lean_findField_x3f(v_env_1667_, v_a_1675_, v_fieldName_1668_);
if (lean_obj_tag(v___x_1676_) == 1)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v_env_1667_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___x_1674_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; size_t v___x_1680_; size_t v___x_1681_; 
lean_dec(v___x_1676_);
v___x_1679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1671_, v___x_1680_);
v_i_1671_ = v___x_1681_;
v_b_1672_ = v___x_1679_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1667_ = stack[0].m_obj;
lean_object* v_fieldName_1668_ = stack[1].m_obj;
lean_object* v_as_1669_ = stack[2].m_obj;
size_t v_sz_1670_ = stack[3].m_num;
size_t v_i_1671_ = stack[4].m_num;
lean_object* v_b_1672_ = stack[5].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1667_, v_fieldName_1668_, v_as_1669_, v_sz_1670_, v_i_1671_, v_b_1672_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1684_, lean_object* v_fieldName_1685_, lean_object* v_as_1686_, lean_object* v_sz_1687_, lean_object* v_i_1688_, lean_object* v_b_1689_){
_start:
{
size_t v_sz_boxed_1690_; size_t v_i_boxed_1691_; lean_object* v_res_1692_; 
v_sz_boxed_1690_ = lean_unbox_usize(v_sz_1687_);
lean_dec(v_sz_1687_);
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_res_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1684_, v_fieldName_1685_, v_as_1686_, v_sz_boxed_1690_, v_i_boxed_1691_, v_b_1689_);
lean_dec_ref(v_b_1689_);
lean_dec_ref(v_as_1686_);
lean_dec(v_fieldName_1685_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1693_, lean_object* v_structName_1694_, lean_object* v_fieldName_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_findField_x3f(v_env_1693_, v_structName_1694_, v_fieldName_1695_);
lean_dec(v_fieldName_1695_);
return v_res_1696_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1700_, lean_object* v_as_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_b_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1705_ == 0)
{
lean_inc_ref(v_b_1704_);
return v_b_1704_;
}
else
{
lean_object* v_a_1706_; lean_object* v_projFn_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_a_1706_ = lean_array_uget_borrowed(v_as_1701_, v_i_1703_);
v_projFn_1707_ = lean_ctor_get(v_a_1706_, 1);
v___x_1708_ = lean_box(0);
v___x_1709_ = l_Lean_Name_isSuffixOf(v_projName_1700_, v_projFn_1707_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1703_, v___x_1711_);
v_i_1703_ = v___x_1712_;
v_b_1704_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_inc(v_a_1706_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_a_1706_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1708_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_projName_1700_ = stack[0].m_obj;
lean_object* v_as_1701_ = stack[1].m_obj;
size_t v_sz_1702_ = stack[2].m_num;
size_t v_i_1703_ = stack[3].m_num;
lean_object* v_b_1704_ = stack[4].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1700_, v_as_1701_, v_sz_1702_, v_i_1703_, v_b_1704_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1718_, lean_object* v_as_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_b_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1718_, v_as_1719_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1722_);
lean_dec_ref(v_b_1722_);
lean_dec_ref(v_as_1719_);
lean_dec(v_projName_1718_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1726_, lean_object* v_projName_1727_, lean_object* v_structName_1728_, lean_object* v_a_1729_){
_start:
{
uint8_t v___x_1730_; 
v___x_1730_ = l_Lean_NameSet_contains(v_a_1729_, v_structName_1728_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1755_; size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; lean_object* v_fst_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1776_; 
lean_inc(v_structName_1728_);
lean_inc_ref(v_env_1726_);
v___x_1731_ = l_Lean_getStructureParentInfo(v_env_1726_, v_structName_1728_);
v___x_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1756_ = lean_array_size(v___x_1731_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1727_, v___x_1731_, v_sz_1756_, v___x_1757_, v___x_1755_);
v_fst_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1758_, 1);
lean_dec(v_unused_1777_);
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1776_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_fst_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1776_;
goto v_resetjp_1760_;
}
v___jp_1732_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; size_t v_sz_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v_fst_1739_; lean_object* v_fst_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1753_; 
v___x_1733_ = l_Lean_NameSet_insert(v_a_1729_, v_structName_1728_);
v___x_1734_ = lean_box(0);
v___x_1735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1736_ = lean_array_size(v___x_1731_);
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1726_, v_projName_1727_, v___x_1731_, v_sz_1736_, v___x_1737_, v___x_1735_, v___x_1733_);
lean_dec_ref(v___x_1731_);
v_fst_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_fst_1739_);
v_fst_1740_ = lean_ctor_get(v_fst_1739_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_fst_1739_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v_fst_1739_, 1);
lean_dec(v_unused_1754_);
v___x_1742_ = v_fst_1739_;
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_fst_1740_);
lean_dec(v_fst_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
if (lean_obj_tag(v_fst_1740_) == 0)
{
lean_object* v_snd_1744_; lean_object* v___x_1746_; 
v_snd_1744_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1744_);
lean_dec_ref(v___x_1738_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_snd_1744_);
lean_ctor_set(v___x_1742_, 0, v___x_1734_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_snd_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
else
{
lean_object* v_snd_1748_; lean_object* v_val_1749_; lean_object* v___x_1751_; 
v_snd_1748_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1748_);
lean_dec_ref(v___x_1738_);
v_val_1749_ = lean_ctor_get(v_fst_1740_, 0);
lean_inc(v_val_1749_);
lean_dec_ref_known(v_fst_1740_, 1);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_snd_1748_);
lean_ctor_set(v___x_1742_, 0, v_val_1749_);
v___x_1751_ = v___x_1742_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_val_1749_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_snd_1748_);
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
v_resetjp_1760_:
{
if (lean_obj_tag(v_fst_1759_) == 0)
{
lean_del_object(v___x_1761_);
goto v___jp_1732_;
}
else
{
lean_object* v_val_1763_; 
v_val_1763_ = lean_ctor_get(v_fst_1759_, 0);
lean_inc(v_val_1763_);
lean_dec_ref_known(v_fst_1759_, 1);
if (lean_obj_tag(v_val_1763_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v___x_1731_);
lean_dec(v_structName_1728_);
lean_dec_ref(v_env_1726_);
v_val_1764_ = lean_ctor_get(v_val_1763_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_val_1763_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1766_ = v_val_1763_;
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_dec(v_val_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_structName_1768_; lean_object* v___x_1770_; 
v_structName_1768_ = lean_ctor_get(v_val_1764_, 0);
lean_inc(v_structName_1768_);
lean_dec(v_val_1764_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v_structName_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_structName_1768_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_a_1729_);
lean_ctor_set(v___x_1761_, 0, v___x_1770_);
v___x_1772_ = v___x_1761_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_a_1729_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_dec(v_val_1763_);
lean_del_object(v___x_1761_);
goto v___jp_1732_;
}
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_structName_1728_);
lean_dec_ref(v_env_1726_);
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_a_1729_);
return v___x_1779_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1780_, lean_object* v_projName_1781_, lean_object* v_as_1782_, size_t v_sz_1783_, size_t v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_usize_dec_lt(v_i_1784_, v_sz_1783_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref(v_env_1780_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_b_1785_);
lean_ctor_set(v___x_1788_, 1, v___y_1786_);
return v___x_1788_;
}
else
{
lean_object* v_a_1789_; lean_object* v_structName_1790_; lean_object* v___x_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_b_1785_);
v_a_1789_ = lean_array_uget_borrowed(v_as_1782_, v_i_1784_);
v_structName_1790_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_structName_1790_);
lean_inc_ref(v_env_1780_);
v___x_1791_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1780_, v_projName_1781_, v_structName_1790_, v___y_1786_);
v_fst_1792_ = lean_ctor_get(v___x_1791_, 0);
v_snd_1793_ = lean_ctor_get(v___x_1791_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1795_ = v___x_1791_;
v_isShared_1796_ = v_isSharedCheck_1807_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1792_);
lean_dec(v___x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1807_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_box(0);
if (lean_obj_tag(v_fst_1792_) == 1)
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec_ref(v_env_1780_);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_fst_1792_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1797_);
lean_ctor_set(v___x_1795_, 0, v___x_1798_);
v___x_1800_ = v___x_1795_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1797_);
v___x_1800_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_snd_1793_);
return v___x_1801_;
}
}
else
{
lean_object* v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; 
lean_del_object(v___x_1795_);
lean_dec(v_fst_1792_);
v___x_1803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1784_, v___x_1804_);
v_i_1784_ = v___x_1805_;
v_b_1785_ = v___x_1803_;
v___y_1786_ = v_snd_1793_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1780_ = stack[0].m_obj;
lean_object* v_projName_1781_ = stack[1].m_obj;
lean_object* v_as_1782_ = stack[2].m_obj;
size_t v_sz_1783_ = stack[3].m_num;
size_t v_i_1784_ = stack[4].m_num;
lean_object* v_b_1785_ = stack[5].m_obj;
lean_object* v___y_1786_ = stack[6].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1780_, v_projName_1781_, v_as_1782_, v_sz_1783_, v_i_1784_, v_b_1785_, v___y_1786_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1809_, lean_object* v_projName_1810_, lean_object* v_as_1811_, lean_object* v_sz_1812_, lean_object* v_i_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_){
_start:
{
size_t v_sz_boxed_1816_; size_t v_i_boxed_1817_; lean_object* v_res_1818_; 
v_sz_boxed_1816_ = lean_unbox_usize(v_sz_1812_);
lean_dec(v_sz_1812_);
v_i_boxed_1817_ = lean_unbox_usize(v_i_1813_);
lean_dec(v_i_1813_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1809_, v_projName_1810_, v_as_1811_, v_sz_boxed_1816_, v_i_boxed_1817_, v_b_1814_, v___y_1815_);
lean_dec_ref(v_as_1811_);
lean_dec(v_projName_1810_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1819_, lean_object* v_projName_1820_, lean_object* v_structName_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1819_, v_projName_1820_, v_structName_1821_, v_a_1822_);
lean_dec(v_projName_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1824_, lean_object* v_structName_1825_, lean_object* v_projName_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_fst_1829_; 
v___x_1827_ = l_Lean_NameSet_empty;
v___x_1828_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1824_, v_projName_1826_, v_structName_1825_, v___x_1827_);
v_fst_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fst_1829_);
lean_dec_ref(v___x_1828_);
return v_fst_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1830_, lean_object* v_structName_1831_, lean_object* v_projName_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_findParentProjStruct_x3f(v_env_1830_, v_structName_1831_, v_projName_1832_);
lean_dec(v_projName_1832_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1839_ = l_Lean_Name_append(v_structCtorName_1837_, v___x_1838_);
return v___x_1839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1840_, lean_object* v_structName_1841_, uint8_t v_includeSubobjectFields_1842_, lean_object* v_as_1843_, size_t v_i_1844_, size_t v_stop_1845_, lean_object* v_b_1846_){
_start:
{
lean_object* v___y_1848_; uint8_t v___x_1852_; 
v___x_1852_ = lean_usize_dec_eq(v_i_1844_, v_stop_1845_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_array_uget_borrowed(v_as_1843_, v_i_1844_);
lean_inc(v___x_1853_);
lean_inc(v_structName_1841_);
lean_inc_ref(v_env_1840_);
v___x_1854_ = l_Lean_isSubobjectField_x3f(v_env_1840_, v_structName_1841_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1855_; 
lean_inc(v___x_1853_);
v___x_1855_ = lean_array_push(v_b_1846_, v___x_1853_);
v___y_1848_ = v___x_1855_;
goto v___jp_1847_;
}
else
{
if (v_includeSubobjectFields_1842_ == 0)
{
lean_object* v_val_1856_; lean_object* v___x_1857_; 
v_val_1856_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v___x_1854_, 1);
lean_inc_ref(v_env_1840_);
v___x_1857_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1840_, v_val_1856_, v_b_1846_, v_includeSubobjectFields_1842_);
v___y_1848_ = v___x_1857_;
goto v___jp_1847_;
}
else
{
lean_object* v_val_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_val_1858_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_val_1858_);
lean_dec_ref_known(v___x_1854_, 1);
lean_inc(v___x_1853_);
v___x_1859_ = lean_array_push(v_b_1846_, v___x_1853_);
lean_inc_ref(v_env_1840_);
v___x_1860_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1840_, v_val_1858_, v___x_1859_, v_includeSubobjectFields_1842_);
v___y_1848_ = v___x_1860_;
goto v___jp_1847_;
}
}
}
else
{
lean_dec(v_structName_1841_);
lean_dec_ref(v_env_1840_);
return v_b_1846_;
}
v___jp_1847_:
{
size_t v___x_1849_; size_t v___x_1850_; 
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1844_, v___x_1849_);
v_i_1844_ = v___x_1850_;
v_b_1846_ = v___y_1848_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1840_ = stack[0].m_obj;
lean_object* v_structName_1841_ = stack[1].m_obj;
uint8_t v_includeSubobjectFields_1842_ = stack[2].m_num;
lean_object* v_as_1843_ = stack[3].m_obj;
size_t v_i_1844_ = stack[4].m_num;
size_t v_stop_1845_ = stack[5].m_num;
lean_object* v_b_1846_ = stack[6].m_obj;
lean_object* v_res_1861_;
v_res_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1840_, v_structName_1841_, v_includeSubobjectFields_1842_, v_as_1843_, v_i_1844_, v_stop_1845_, v_b_1846_);
stack->m_obj
 = v_res_1861_;
}
lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1862_, lean_object* v_structName_1863_, lean_object* v_fullNames_1864_, uint8_t v_includeSubobjectFields_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
lean_inc(v_structName_1863_);
lean_inc_ref(v_env_1862_);
v___x_1866_ = l_Lean_getStructureFields(v_env_1862_, v_structName_1863_);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_array_get_size(v___x_1866_);
v___x_1869_ = lean_nat_dec_lt(v___x_1867_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec_ref(v___x_1866_);
lean_dec(v_structName_1863_);
lean_dec_ref(v_env_1862_);
return v_fullNames_1864_;
}
else
{
uint8_t v___x_1870_; 
v___x_1870_ = lean_nat_dec_le(v___x_1868_, v___x_1868_);
if (v___x_1870_ == 0)
{
if (v___x_1869_ == 0)
{
lean_dec_ref(v___x_1866_);
lean_dec(v_structName_1863_);
lean_dec_ref(v_env_1862_);
return v_fullNames_1864_;
}
else
{
size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = lean_usize_of_nat(v___x_1868_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1862_, v_structName_1863_, v_includeSubobjectFields_1865_, v___x_1866_, v___x_1871_, v___x_1872_, v_fullNames_1864_);
lean_dec_ref(v___x_1866_);
return v___x_1873_;
}
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1868_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1862_, v_structName_1863_, v_includeSubobjectFields_1865_, v___x_1866_, v___x_1874_, v___x_1875_, v_fullNames_1864_);
lean_dec_ref(v___x_1866_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1862_ = stack[0].m_obj;
lean_object* v_structName_1863_ = stack[1].m_obj;
lean_object* v_fullNames_1864_ = stack[2].m_obj;
uint8_t v_includeSubobjectFields_1865_ = stack[3].m_num;
lean_object* v_res_1877_;
v_res_1877_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1862_, v_structName_1863_, v_fullNames_1864_, v_includeSubobjectFields_1865_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1878_, lean_object* v_structName_1879_, lean_object* v_fullNames_1880_, lean_object* v_includeSubobjectFields_1881_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1882_; lean_object* v_res_1883_; 
v_includeSubobjectFields_boxed_1882_ = lean_unbox(v_includeSubobjectFields_1881_);
v_res_1883_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1878_, v_structName_1879_, v_fullNames_1880_, v_includeSubobjectFields_boxed_1882_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1884_, lean_object* v_structName_1885_, lean_object* v_includeSubobjectFields_1886_, lean_object* v_as_1887_, lean_object* v_i_1888_, lean_object* v_stop_1889_, lean_object* v_b_1890_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1891_; size_t v_i_boxed_1892_; size_t v_stop_boxed_1893_; lean_object* v_res_1894_; 
v_includeSubobjectFields_boxed_1891_ = lean_unbox(v_includeSubobjectFields_1886_);
v_i_boxed_1892_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_stop_boxed_1893_ = lean_unbox_usize(v_stop_1889_);
lean_dec(v_stop_1889_);
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1884_, v_structName_1885_, v_includeSubobjectFields_boxed_1891_, v_as_1887_, v_i_boxed_1892_, v_stop_boxed_1893_, v_b_1890_);
lean_dec_ref(v_as_1887_);
return v_res_1894_;
}
}
lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1895_, lean_object* v_structName_1896_, uint8_t v_includeSubobjectFields_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1899_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1895_, v_structName_1896_, v___x_1898_, v_includeSubobjectFields_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT void l_Lean_getStructureFieldsFlattened_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1895_ = stack[0].m_obj;
lean_object* v_structName_1896_ = stack[1].m_obj;
uint8_t v_includeSubobjectFields_1897_ = stack[2].m_num;
lean_object* v_res_1900_;
v_res_1900_ = l_Lean_getStructureFieldsFlattened(v_env_1895_, v_structName_1896_, v_includeSubobjectFields_1897_);
stack->m_obj
 = v_res_1900_;
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1901_, lean_object* v_structName_1902_, lean_object* v_includeSubobjectFields_1903_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1904_; lean_object* v_res_1905_; 
v_includeSubobjectFields_boxed_1904_ = lean_unbox(v_includeSubobjectFields_1903_);
v_res_1905_ = l_Lean_getStructureFieldsFlattened(v_env_1901_, v_structName_1902_, v_includeSubobjectFields_boxed_1904_);
return v_res_1905_;
}
}
uint8_t l_Lean_isStructure(lean_object* v_env_1906_, lean_object* v_constName_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_getStructureInfo_x3f(v_env_1906_, v_constName_1907_);
if (lean_obj_tag(v___x_1908_) == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = 0;
return v___x_1909_;
}
else
{
uint8_t v___x_1910_; 
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = 1;
return v___x_1910_;
}
}
}
LEAN_EXPORT void l_Lean_isStructure_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1906_ = stack[0].m_obj;
lean_object* v_constName_1907_ = stack[1].m_obj;
uint8_t v_res_1911_;
v_res_1911_ = l_Lean_isStructure(v_env_1906_, v_constName_1907_);
stack->m_num = v_res_1911_;
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1912_, lean_object* v_constName_1913_){
_start:
{
uint8_t v_res_1914_; lean_object* v_r_1915_; 
v_res_1914_ = l_Lean_isStructure(v_env_1912_, v_constName_1913_);
v_r_1915_ = lean_box(v_res_1914_);
return v_r_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1916_, lean_object* v_structName_1917_, lean_object* v_fieldName_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_getFieldInfo_x3f(v_env_1916_, v_structName_1917_, v_fieldName_1918_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_projFn_1924_; lean_object* v___x_1926_; 
v_projFn_1924_ = lean_ctor_get(v_val_1920_, 1);
lean_inc(v_projFn_1924_);
lean_dec(v_val_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_projFn_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_projFn_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v___x_1919_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1930_, lean_object* v_structName_1931_, lean_object* v_fieldName_1932_){
_start:
{
lean_object* v___x_1933_; 
lean_inc_ref(v_env_1930_);
v___x_1933_ = l_Lean_getProjFnForField_x3f(v_env_1930_, v_structName_1931_, v_fieldName_1932_);
if (lean_obj_tag(v___x_1933_) == 1)
{
lean_object* v_val_1934_; lean_object* v___x_1935_; 
v_val_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc_n(v_val_1934_, 2);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1930_, v_val_1934_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; 
lean_dec(v_val_1934_);
v___x_1936_ = lean_box(0);
return v___x_1936_;
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
v_val_1937_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1939_ = v___x_1935_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_val_1937_);
lean_dec(v___x_1935_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_val_1934_);
lean_ctor_set(v___x_1941_, 1, v_val_1937_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v___x_1946_; 
lean_dec(v___x_1933_);
lean_dec_ref(v_env_1930_);
v___x_1946_ = lean_box(0);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1952_ = l_Lean_Name_append(v_projFn_1950_, v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1958_ = l_Lean_Name_append(v_projFn_1956_, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1959_, lean_object* v_env_1960_, lean_object* v_structName_1961_, lean_object* v_fieldName_1962_){
_start:
{
lean_object* v___x_1963_; 
lean_inc(v_fieldName_1962_);
lean_inc(v_structName_1961_);
lean_inc_ref(v_env_1960_);
v___x_1963_ = l_Lean_getProjFnForField_x3f(v_env_1960_, v_structName_1961_, v_fieldName_1962_);
if (lean_obj_tag(v___x_1963_) == 1)
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_fieldName_1962_);
lean_dec(v_structName_1961_);
v_val_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1975_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1975_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_defFn_1968_; uint8_t v___x_1969_; uint8_t v___x_1970_; 
v_defFn_1968_ = lean_apply_1(v_mkName_1959_, v_val_1964_);
v___x_1969_ = 1;
lean_inc(v_defFn_1968_);
v___x_1970_ = l_Lean_Environment_contains(v_env_1960_, v_defFn_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_defFn_1968_);
lean_del_object(v___x_1966_);
v___x_1971_ = lean_box(0);
return v___x_1971_;
}
else
{
lean_object* v___x_1973_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_defFn_1968_);
v___x_1973_ = v___x_1966_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_defFn_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1976_; lean_object* v_defFn_1977_; uint8_t v___x_1978_; uint8_t v___x_1979_; 
lean_dec(v___x_1963_);
v___x_1976_ = l_Lean_Name_append(v_structName_1961_, v_fieldName_1962_);
v_defFn_1977_ = lean_apply_1(v_mkName_1959_, v___x_1976_);
v___x_1978_ = 1;
lean_inc(v_defFn_1977_);
v___x_1979_ = l_Lean_Environment_contains(v_env_1960_, v_defFn_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v_defFn_1977_);
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_defFn_1977_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1983_, lean_object* v_structName_1984_, lean_object* v_fieldName_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1987_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1986_, v_env_1983_, v_structName_1984_, v_fieldName_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1989_, lean_object* v_structName_1990_, lean_object* v_fieldName_1991_){
_start:
{
lean_object* v___x_1992_; 
lean_inc(v_fieldName_1991_);
lean_inc(v_structName_1990_);
lean_inc_ref(v_env_1989_);
v___x_1992_ = l_Lean_getDefaultFnForField_x3f(v_env_1989_, v_structName_1990_, v_fieldName_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1994_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1993_, v_env_1989_, v_structName_1990_, v_fieldName_1991_);
return v___x_1994_;
}
else
{
lean_dec(v_fieldName_1991_);
lean_dec(v_structName_1990_);
lean_dec_ref(v_env_1989_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_2000_ = l_Lean_Name_append(v_projFn_1998_, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_2002_, lean_object* v_structName_2003_, lean_object* v_fieldName_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_2006_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_2005_, v_env_2002_, v_structName_2003_, v_fieldName_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_2007_, lean_object* v_env_2008_, lean_object* v_baseStructName_2009_, lean_object* v_as_2010_, lean_object* v_i_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_snd_2014_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = lean_array_get_size(v_as_2010_);
v___x_2019_ = lean_nat_dec_lt(v_i_2011_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v_i_2011_);
lean_dec_ref(v_env_2008_);
lean_dec(v_path_2007_);
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___y_2012_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; lean_object* v_subobject_x3f_2023_; 
v___x_2022_ = lean_array_fget_borrowed(v_as_2010_, v_i_2011_);
v_subobject_x3f_2023_ = lean_ctor_get(v___x_2022_, 2);
if (lean_obj_tag(v_subobject_x3f_2023_) == 1)
{
lean_object* v_projFn_2024_; lean_object* v_val_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_fst_2028_; 
v_projFn_2024_ = lean_ctor_get(v___x_2022_, 1);
v_val_2025_ = lean_ctor_get(v_subobject_x3f_2023_, 0);
lean_inc(v_path_2007_);
lean_inc(v_projFn_2024_);
v___x_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_projFn_2024_);
lean_ctor_set(v___x_2026_, 1, v_path_2007_);
lean_inc(v_val_2025_);
lean_inc_ref(v_env_2008_);
v___x_2027_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2008_, v_baseStructName_2009_, v_val_2025_, v___x_2026_, v___y_2012_);
v_fst_2028_ = lean_ctor_get(v___x_2027_, 0);
if (lean_obj_tag(v_fst_2028_) == 0)
{
lean_object* v_snd_2029_; 
v_snd_2029_ = lean_ctor_get(v___x_2027_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2027_);
v_snd_2014_ = v_snd_2029_;
goto v___jp_2013_;
}
else
{
lean_dec(v_i_2011_);
lean_dec_ref(v_env_2008_);
lean_dec(v_path_2007_);
return v___x_2027_;
}
}
else
{
v_snd_2014_ = v___y_2012_;
goto v___jp_2013_;
}
}
v___jp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_i_2011_, v___x_2015_);
lean_dec(v_i_2011_);
v_i_2011_ = v___x_2016_;
v___y_2012_ = v_snd_2014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_2030_, lean_object* v_baseStructName_2031_, lean_object* v_structName_2032_, lean_object* v_path_2033_, lean_object* v_a_2034_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_name_eq(v_baseStructName_2031_, v_structName_2032_);
if (v___x_2048_ == 0)
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lean_NameSet_contains(v_a_2034_, v_structName_2032_);
if (v___x_2049_ == 0)
{
goto v___jp_2035_;
}
else
{
if (v___x_2048_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_path_2033_);
lean_dec(v_structName_2032_);
lean_dec_ref(v_env_2030_);
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_a_2034_);
return v___x_2051_;
}
else
{
goto v___jp_2035_;
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v_structName_2032_);
lean_dec_ref(v_env_2030_);
v___x_2052_ = l_List_reverse___redArg(v_path_2033_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v_a_2034_);
return v___x_2054_;
}
v___jp_2035_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_inc(v_structName_2032_);
v___x_2036_ = l_Lean_NameSet_insert(v_a_2034_, v_structName_2032_);
lean_inc_ref(v_env_2030_);
v___x_2037_ = l_Lean_getStructureInfo_x3f(v_env_2030_, v_structName_2032_);
if (lean_obj_tag(v___x_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v_fieldInfo_2039_; lean_object* v_parentInfo_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_fst_2043_; 
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v_fieldInfo_2039_ = lean_ctor_get(v_val_2038_, 2);
lean_inc_ref(v_fieldInfo_2039_);
v_parentInfo_2040_ = lean_ctor_get(v_val_2038_, 3);
lean_inc_ref(v_parentInfo_2040_);
lean_dec(v_val_2038_);
v___x_2041_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_2030_);
lean_inc(v_path_2033_);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_2033_, v_env_2030_, v_baseStructName_2031_, v_fieldInfo_2039_, v___x_2041_, v___x_2036_);
lean_dec_ref(v_fieldInfo_2039_);
v_fst_2043_ = lean_ctor_get(v___x_2042_, 0);
if (lean_obj_tag(v_fst_2043_) == 0)
{
lean_object* v_snd_2044_; lean_object* v___x_2045_; 
v_snd_2044_ = lean_ctor_get(v___x_2042_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2042_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_2033_, v_env_2030_, v_baseStructName_2031_, v_parentInfo_2040_, v___x_2041_, v_snd_2044_);
lean_dec_ref(v_parentInfo_2040_);
return v___x_2045_;
}
else
{
lean_dec_ref(v_parentInfo_2040_);
lean_dec(v_path_2033_);
lean_dec_ref(v_env_2030_);
return v___x_2042_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v___x_2037_);
lean_dec(v_path_2033_);
lean_dec_ref(v_env_2030_);
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v___x_2036_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_2055_, lean_object* v_env_2056_, lean_object* v_baseStructName_2057_, lean_object* v_as_2058_, lean_object* v_i_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = lean_array_get_size(v_as_2058_);
v___x_2062_ = lean_nat_dec_lt(v_i_2059_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v_i_2059_);
lean_dec_ref(v_env_2056_);
lean_dec(v_path_2055_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___y_2060_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v_structName_2066_; lean_object* v_projFn_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_fst_2070_; 
v___x_2065_ = lean_array_fget_borrowed(v_as_2058_, v_i_2059_);
v_structName_2066_ = lean_ctor_get(v___x_2065_, 0);
v_projFn_2067_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_path_2055_);
lean_inc(v_projFn_2067_);
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_projFn_2067_);
lean_ctor_set(v___x_2068_, 1, v_path_2055_);
lean_inc(v_structName_2066_);
lean_inc_ref(v_env_2056_);
v___x_2069_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2056_, v_baseStructName_2057_, v_structName_2066_, v___x_2068_, v___y_2060_);
v_fst_2070_ = lean_ctor_get(v___x_2069_, 0);
if (lean_obj_tag(v_fst_2070_) == 0)
{
lean_object* v_snd_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_snd_2071_ = lean_ctor_get(v___x_2069_, 1);
lean_inc(v_snd_2071_);
lean_dec_ref(v___x_2069_);
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_add(v_i_2059_, v___x_2072_);
lean_dec(v_i_2059_);
v_i_2059_ = v___x_2073_;
v___y_2060_ = v_snd_2071_;
goto _start;
}
else
{
lean_dec(v_i_2059_);
lean_dec_ref(v_env_2056_);
lean_dec(v_path_2055_);
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_2075_, lean_object* v_env_2076_, lean_object* v_baseStructName_2077_, lean_object* v_as_2078_, lean_object* v_i_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_2075_, v_env_2076_, v_baseStructName_2077_, v_as_2078_, v_i_2079_, v___y_2080_);
lean_dec_ref(v_as_2078_);
lean_dec(v_baseStructName_2077_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_2082_, lean_object* v_env_2083_, lean_object* v_baseStructName_2084_, lean_object* v_as_2085_, lean_object* v_i_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_2082_, v_env_2083_, v_baseStructName_2084_, v_as_2085_, v_i_2086_, v___y_2087_);
lean_dec_ref(v_as_2085_);
lean_dec(v_baseStructName_2084_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_2089_, lean_object* v_baseStructName_2090_, lean_object* v_structName_2091_, lean_object* v_path_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2089_, v_baseStructName_2090_, v_structName_2091_, v_path_2092_, v_a_2093_);
lean_dec(v_baseStructName_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_2095_, lean_object* v_baseStructName_2096_, lean_object* v_structName_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_fst_2101_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Lean_NameSet_empty;
v___x_2100_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2095_, v_baseStructName_2096_, v_structName_2097_, v___x_2098_, v___x_2099_);
v_fst_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fst_2101_);
lean_dec_ref(v___x_2100_);
return v_fst_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_2102_, lean_object* v_baseStructName_2103_, lean_object* v_structName_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_getPathToBaseStructure_x3f(v_env_2102_, v_baseStructName_2103_, v_structName_2104_);
lean_dec(v_baseStructName_2103_);
return v_res_2105_;
}
}
uint8_t l_Lean_isNonRecStructure(lean_object* v_env_2106_, lean_object* v_constName_2107_){
_start:
{
uint8_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = 0;
v___x_2109_ = l_Lean_Environment_find_x3f(v_env_2106_, v_constName_2107_, v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 1)
{
lean_object* v_val_2110_; 
v_val_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v___x_2109_, 1);
if (lean_obj_tag(v_val_2110_) == 5)
{
lean_object* v_val_2111_; lean_object* v_numIndices_2112_; lean_object* v_ctors_2113_; uint8_t v_isRec_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_val_2111_ = lean_ctor_get(v_val_2110_, 0);
lean_inc_ref(v_val_2111_);
lean_dec_ref_known(v_val_2110_, 1);
v_numIndices_2112_ = lean_ctor_get(v_val_2111_, 2);
lean_inc(v_numIndices_2112_);
v_ctors_2113_ = lean_ctor_get(v_val_2111_, 4);
lean_inc(v_ctors_2113_);
v_isRec_2114_ = lean_ctor_get_uint8(v_val_2111_, sizeof(void*)*6);
lean_dec_ref(v_val_2111_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_nat_dec_eq(v_numIndices_2112_, v___x_2115_);
lean_dec(v_numIndices_2112_);
if (v___x_2116_ == 0)
{
lean_dec(v_ctors_2113_);
return v___x_2116_;
}
else
{
if (lean_obj_tag(v_ctors_2113_) == 1)
{
lean_object* v_tail_2117_; 
v_tail_2117_ = lean_ctor_get(v_ctors_2113_, 1);
lean_inc(v_tail_2117_);
lean_dec_ref_known(v_ctors_2113_, 2);
if (lean_obj_tag(v_tail_2117_) == 0)
{
if (v_isRec_2114_ == 0)
{
return v___x_2116_;
}
else
{
return v___x_2108_;
}
}
else
{
lean_dec(v_tail_2117_);
return v___x_2108_;
}
}
else
{
lean_dec(v_ctors_2113_);
return v___x_2108_;
}
}
}
else
{
lean_dec(v_val_2110_);
return v___x_2108_;
}
}
else
{
lean_dec(v___x_2109_);
return v___x_2108_;
}
}
}
LEAN_EXPORT void l_Lean_isNonRecStructure_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2106_ = stack[0].m_obj;
lean_object* v_constName_2107_ = stack[1].m_obj;
uint8_t v_res_2118_;
v_res_2118_ = l_Lean_isNonRecStructure(v_env_2106_, v_constName_2107_);
stack->m_num = v_res_2118_;
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_2119_, lean_object* v_constName_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_Lean_isNonRecStructure(v_env_2119_, v_constName_2120_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_2123_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_panic_fn_borrowed(v___x_2124_, v_msg_2123_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_2128_ = lean_unsigned_to_nat(11u);
v___x_2129_ = lean_unsigned_to_nat(381u);
v___x_2130_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_2131_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_2132_ = l_mkPanicMessageWithDecl(v___x_2131_, v___x_2130_, v___x_2129_, v___x_2128_, v___x_2127_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_2133_, lean_object* v_constName_2134_){
_start:
{
uint8_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = 0;
lean_inc_ref(v_env_2133_);
v___x_2139_ = l_Lean_Environment_find_x3f(v_env_2133_, v_constName_2134_, v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 1)
{
lean_object* v_val_2140_; 
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_val_2140_);
lean_dec_ref_known(v___x_2139_, 1);
if (lean_obj_tag(v_val_2140_) == 5)
{
lean_object* v_val_2141_; lean_object* v_numIndices_2142_; lean_object* v_ctors_2143_; uint8_t v_isRec_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_val_2141_ = lean_ctor_get(v_val_2140_, 0);
lean_inc_ref(v_val_2141_);
lean_dec_ref_known(v_val_2140_, 1);
v_numIndices_2142_ = lean_ctor_get(v_val_2141_, 2);
lean_inc(v_numIndices_2142_);
v_ctors_2143_ = lean_ctor_get(v_val_2141_, 4);
lean_inc(v_ctors_2143_);
v_isRec_2144_ = lean_ctor_get_uint8(v_val_2141_, sizeof(void*)*6);
lean_dec_ref(v_val_2141_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_nat_dec_eq(v_numIndices_2142_, v___x_2145_);
lean_dec(v_numIndices_2142_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v_ctors_2143_);
lean_dec_ref(v_env_2133_);
v___x_2147_ = lean_box(0);
return v___x_2147_;
}
else
{
if (lean_obj_tag(v_ctors_2143_) == 1)
{
lean_object* v_tail_2148_; 
v_tail_2148_ = lean_ctor_get(v_ctors_2143_, 1);
if (lean_obj_tag(v_tail_2148_) == 0)
{
if (v_isRec_2144_ == 0)
{
lean_object* v_head_2149_; lean_object* v___x_2150_; 
v_head_2149_ = lean_ctor_get(v_ctors_2143_, 0);
lean_inc(v_head_2149_);
lean_dec_ref_known(v_ctors_2143_, 2);
v___x_2150_ = l_Lean_Environment_find_x3f(v_env_2133_, v_head_2149_, v_isRec_2144_);
if (lean_obj_tag(v___x_2150_) == 1)
{
lean_object* v_val_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2159_; 
v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_val_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
if (lean_obj_tag(v_val_2151_) == 6)
{
lean_object* v_val_2155_; lean_object* v___x_2157_; 
v_val_2155_ = lean_ctor_get(v_val_2151_, 0);
lean_inc_ref(v_val_2155_);
lean_dec_ref_known(v_val_2151_, 1);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v_val_2155_);
v___x_2157_ = v___x_2153_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_val_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
else
{
lean_del_object(v___x_2153_);
lean_dec(v_val_2151_);
goto v___jp_2135_;
}
}
}
else
{
lean_dec(v___x_2150_);
goto v___jp_2135_;
}
}
else
{
lean_object* v___x_2160_; 
lean_dec_ref_known(v_ctors_2143_, 2);
lean_dec_ref(v_env_2133_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
}
else
{
lean_object* v___x_2161_; 
lean_dec_ref_known(v_ctors_2143_, 2);
lean_dec_ref(v_env_2133_);
v___x_2161_ = lean_box(0);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2162_; 
lean_dec(v_ctors_2143_);
lean_dec_ref(v_env_2133_);
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_val_2140_);
lean_dec_ref(v_env_2133_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
else
{
lean_object* v___x_2164_; 
lean_dec(v___x_2139_);
lean_dec_ref(v_env_2133_);
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
v___jp_2135_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_2137_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_2136_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_2165_, lean_object* v_constName_2166_){
_start:
{
uint8_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = 0;
lean_inc_ref(v_env_2165_);
v___x_2168_ = l_Lean_Environment_find_x3f(v_env_2165_, v_constName_2166_, v___x_2167_);
if (lean_obj_tag(v___x_2168_) == 1)
{
lean_object* v_val_2169_; 
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref_known(v___x_2168_, 1);
if (lean_obj_tag(v_val_2169_) == 5)
{
lean_object* v_val_2170_; lean_object* v_numIndices_2171_; lean_object* v_ctors_2172_; uint8_t v_isRec_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_val_2170_ = lean_ctor_get(v_val_2169_, 0);
lean_inc_ref(v_val_2170_);
lean_dec_ref_known(v_val_2169_, 1);
v_numIndices_2171_ = lean_ctor_get(v_val_2170_, 2);
lean_inc(v_numIndices_2171_);
v_ctors_2172_ = lean_ctor_get(v_val_2170_, 4);
lean_inc(v_ctors_2172_);
v_isRec_2173_ = lean_ctor_get_uint8(v_val_2170_, sizeof(void*)*6);
lean_dec_ref(v_val_2170_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_nat_dec_eq(v_numIndices_2171_, v___x_2174_);
lean_dec(v_numIndices_2171_);
if (v___x_2175_ == 0)
{
lean_dec(v_ctors_2172_);
lean_dec_ref(v_env_2165_);
return v___x_2174_;
}
else
{
if (lean_obj_tag(v_ctors_2172_) == 1)
{
lean_object* v_tail_2176_; 
v_tail_2176_ = lean_ctor_get(v_ctors_2172_, 1);
if (lean_obj_tag(v_tail_2176_) == 0)
{
if (v_isRec_2173_ == 0)
{
lean_object* v_head_2177_; lean_object* v___x_2178_; 
v_head_2177_ = lean_ctor_get(v_ctors_2172_, 0);
lean_inc(v_head_2177_);
lean_dec_ref_known(v_ctors_2172_, 2);
v___x_2178_ = l_Lean_Environment_find_x3f(v_env_2165_, v_head_2177_, v_isRec_2173_);
if (lean_obj_tag(v___x_2178_) == 1)
{
lean_object* v_val_2179_; 
v_val_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v___x_2178_, 1);
if (lean_obj_tag(v_val_2179_) == 6)
{
lean_object* v_val_2180_; lean_object* v_numFields_2181_; 
v_val_2180_ = lean_ctor_get(v_val_2179_, 0);
lean_inc_ref(v_val_2180_);
lean_dec_ref_known(v_val_2179_, 1);
v_numFields_2181_ = lean_ctor_get(v_val_2180_, 4);
lean_inc(v_numFields_2181_);
lean_dec_ref(v_val_2180_);
return v_numFields_2181_;
}
else
{
lean_dec(v_val_2179_);
return v___x_2174_;
}
}
else
{
lean_dec(v___x_2178_);
return v___x_2174_;
}
}
else
{
lean_dec_ref_known(v_ctors_2172_, 2);
lean_dec_ref(v_env_2165_);
return v___x_2174_;
}
}
else
{
lean_dec_ref_known(v_ctors_2172_, 2);
lean_dec_ref(v_env_2165_);
return v___x_2174_;
}
}
else
{
lean_dec(v_ctors_2172_);
lean_dec_ref(v_env_2165_);
return v___x_2174_;
}
}
}
else
{
lean_object* v___x_2182_; 
lean_dec(v_val_2169_);
lean_dec_ref(v_env_2165_);
v___x_2182_ = lean_unsigned_to_nat(0u);
return v___x_2182_;
}
}
else
{
lean_object* v___x_2183_; 
lean_dec(v___x_2168_);
lean_dec_ref(v_env_2165_);
v___x_2183_ = lean_unsigned_to_nat(0u);
return v___x_2183_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2187_;
}
}
lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(lean_object* v___x_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2188_ = stack[0].m_obj;
lean_object* v_res_2191_;
v_res_2191_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(v___x_2188_);
stack->m_obj
 = v_res_2191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object* v___x_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(v___x_2192_);
return v_res_2194_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___f_2196_; 
v___x_2195_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2196_, 0, v___x_2195_);
return v___f_2196_;
}
}
lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v___f_2202_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_box(1);
v___x_2205_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_));
v___x_2206_ = 0;
v___x_2207_ = 1;
v___x_2208_ = l_Lean_registerEnvExtension___redArg(v___f_2202_, v___x_2203_, v___x_2204_, v___x_2205_, v___x_2206_, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2209_;
v_res_2209_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_();
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2212_, lean_object* v_structName_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v_asyncMode_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2214_ = l_Lean_structureResolutionExt;
v_asyncMode_2215_ = lean_ctor_get(v___x_2214_, 2);
v___x_2216_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2217_ = lean_box(0);
v___x_2218_ = 0;
v___x_2219_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2216_, v___x_2214_, v_env_2212_, v_asyncMode_2215_, v___x_2217_, v___x_2218_);
v___x_2220_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2219_, v_structName_2213_);
lean_dec(v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2221_, lean_object* v_structName_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2221_, v_structName_2222_);
lean_dec(v_structName_2222_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2224_, lean_object* v___x_2225_, lean_object* v_structName_2226_, lean_object* v_resolutionOrder_2227_, lean_object* v_s_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2224_, v___x_2225_, v_s_2228_, v_structName_2226_, v_resolutionOrder_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2230_, lean_object* v_env_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v_asyncMode_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = l_Lean_structureResolutionExt;
v_asyncMode_2233_ = lean_ctor_get(v___x_2232_, 2);
v___x_2234_ = lean_box(0);
v___x_2235_ = 1;
v___x_2236_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_2232_, v_env_2231_, v___f_2230_, v_asyncMode_2233_, v___x_2234_, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2237_, lean_object* v_structName_2238_, lean_object* v_resolutionOrder_2239_){
_start:
{
lean_object* v_modifyEnv_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; 
v_modifyEnv_2240_ = lean_ctor_get(v_inst_2237_, 1);
lean_inc(v_modifyEnv_2240_);
lean_dec_ref(v_inst_2237_);
v___x_2241_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2242_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2243_, 0, v___x_2241_);
lean_closure_set(v___f_2243_, 1, v___x_2242_);
lean_closure_set(v___f_2243_, 2, v_structName_2238_);
lean_closure_set(v___f_2243_, 3, v_resolutionOrder_2239_);
v___f_2244_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2244_, 0, v___f_2243_);
v___x_2245_ = lean_apply_1(v_modifyEnv_2240_, v___f_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2246_, lean_object* v_inst_2247_, lean_object* v_structName_2248_, lean_object* v_resolutionOrder_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2247_, v_structName_2248_, v_resolutionOrder_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2268_, lean_object* v_resOrders_2269_, lean_object* v___x_2270_, lean_object* v_toPure_2271_, lean_object* v_____s_2272_){
_start:
{
lean_object* v_fst_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2288_; 
v_fst_2273_ = lean_ctor_get(v_____s_2272_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_____s_2272_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v_____s_2272_, 1);
lean_dec(v_unused_2289_);
v___x_2275_ = v_____s_2272_;
v_isShared_2276_ = v_isSharedCheck_2288_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_fst_2273_);
lean_dec(v_____s_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2288_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
if (lean_obj_tag(v_fst_2273_) == 0)
{
uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2277_ = 0;
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_get_borrowed(v___x_2268_, v_resOrders_2269_, v___x_2278_);
v___x_2280_ = lean_array_get_borrowed(v___x_2270_, v___x_2279_, v___x_2278_);
v___x_2281_ = lean_box(v___x_2277_);
lean_inc(v___x_2280_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 1, v___x_2280_);
lean_ctor_set(v___x_2275_, 0, v___x_2281_);
v___x_2283_ = v___x_2275_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2280_);
v___x_2283_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_apply_2(v_toPure_2271_, lean_box(0), v___x_2283_);
return v___x_2284_;
}
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2275_);
v_val_2286_ = lean_ctor_get(v_fst_2273_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_fst_2273_, 1);
v___x_2287_ = lean_apply_2(v_toPure_2271_, lean_box(0), v_val_2286_);
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2290_, lean_object* v_resOrders_2291_, lean_object* v___x_2292_, lean_object* v_toPure_2293_, lean_object* v_____s_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2290_, v_resOrders_2291_, v___x_2292_, v_toPure_2293_, v_____s_2294_);
lean_dec(v___x_2292_);
lean_dec_ref(v_resOrders_2291_);
lean_dec_ref(v___x_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2296_, lean_object* v_____do__lift_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_apply_2(v_toPure_2296_, lean_box(0), v_____do__lift_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2299_, lean_object* v_toPure_2300_, lean_object* v___x_2301_, lean_object* v_____s_2302_){
_start:
{
lean_object* v_fst_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2321_; 
v_fst_2303_ = lean_ctor_get(v_____s_2302_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_____s_2302_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_____s_2302_, 1);
lean_dec(v_unused_2322_);
v___x_2305_ = v_____s_2302_;
v_isShared_2306_ = v_isSharedCheck_2321_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_fst_2303_);
lean_dec(v_____s_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2321_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
if (lean_obj_tag(v_fst_2303_) == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_del_object(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2299_);
v___x_2308_ = lean_apply_2(v_toPure_2300_, lean_box(0), v___x_2307_);
return v___x_2308_;
}
else
{
lean_object* v___x_2310_; 
lean_dec_ref(v___x_2299_);
lean_inc_ref(v_fst_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2301_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_fst_2303_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2301_);
v___x_2310_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2318_; 
v_isSharedCheck_2318_ = !lean_is_exclusive(v_fst_2303_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_fst_2303_, 0);
lean_dec(v_unused_2319_);
v___x_2312_ = v_fst_2303_;
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v_fst_2303_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2310_);
v___x_2315_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_apply_2(v_toPure_2300_, lean_box(0), v___x_2315_);
return v___x_2316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2323_, lean_object* v_next_2324_, lean_object* v_G_2325_, lean_object* v_____do__lift_2326_){
_start:
{
if (lean_obj_tag(v_____do__lift_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
lean_dec(v_G_2325_);
v_a_2327_ = lean_ctor_get(v_____do__lift_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v_____do__lift_2326_, 1);
v___x_2328_ = lean_apply_2(v_toPure_2323_, lean_box(0), v_a_2327_);
return v___x_2328_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v_toPure_2323_);
v_a_2329_ = lean_ctor_get(v_____do__lift_2326_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v_____do__lift_2326_, 1);
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_next_2324_, v___x_2330_);
v___x_2332_ = lean_apply_4(v_G_2325_, v___x_2331_, v_a_2329_, lean_box(0), lean_box(0));
return v___x_2332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2333_, lean_object* v_next_2334_, lean_object* v_G_2335_, lean_object* v_____do__lift_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2333_, v_next_2334_, v_G_2335_, v_____do__lift_2336_);
lean_dec(v_next_2334_);
return v_res_2337_;
}
}
uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2338_, uint8_t v___x_2339_, lean_object* v_v_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_name_eq(v_v_2340_, v___x_2338_);
if (v___x_2341_ == 0)
{
return v___x_2341_;
}
else
{
return v___x_2339_;
}
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2338_ = stack[0].m_obj;
uint8_t v___x_2339_ = stack[1].m_num;
lean_object* v_v_2340_ = stack[2].m_obj;
uint8_t v_res_2342_;
v_res_2342_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2338_, v___x_2339_, v_v_2340_);
stack->m_num = v_res_2342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2343_, lean_object* v___x_2344_, lean_object* v_v_2345_){
_start:
{
uint8_t v___x_1611__boxed_2346_; uint8_t v_res_2347_; lean_object* v_r_2348_; 
v___x_1611__boxed_2346_ = lean_unbox(v___x_2344_);
v_res_2347_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2343_, v___x_1611__boxed_2346_, v_v_2345_);
lean_dec(v_v_2345_);
lean_dec(v___x_2343_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2368_, lean_object* v___f_2369_, lean_object* v_resOrder_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_array_2375_; lean_object* v_start_2376_; lean_object* v_stop_2377_; uint8_t v___x_2378_; lean_object* v___y_2380_; 
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_array_get_size(v_resOrder_2370_);
v___x_2373_ = l_Array_toSubarray___redArg(v_resOrder_2370_, v___x_2371_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2375_ = lean_ctor_get(v___x_2373_, 0);
lean_inc_ref(v_array_2375_);
v_start_2376_ = lean_ctor_get(v___x_2373_, 1);
lean_inc(v_start_2376_);
v_stop_2377_ = lean_ctor_get(v___x_2373_, 2);
lean_inc(v_stop_2377_);
lean_dec_ref(v___x_2373_);
v___x_2378_ = lean_nat_dec_lt(v_start_2376_, v_stop_2377_);
if (v___x_2378_ == 0)
{
lean_dec(v_stop_2377_);
lean_dec(v_start_2376_);
lean_dec_ref(v_array_2375_);
lean_dec_ref(v___f_2369_);
return v___x_2368_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_array_get_size(v_array_2375_);
v___x_2388_ = lean_nat_dec_le(v_stop_2377_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_dec(v_stop_2377_);
v___y_2380_ = v___x_2387_;
goto v___jp_2379_;
}
else
{
v___y_2380_ = v_stop_2377_;
goto v___jp_2379_;
}
}
v___jp_2379_:
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_nat_dec_lt(v_start_2376_, v___y_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v___y_2380_);
lean_dec(v_start_2376_);
lean_dec_ref(v_array_2375_);
lean_dec_ref(v___f_2369_);
return v___x_2378_;
}
else
{
size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2382_ = lean_usize_of_nat(v_start_2376_);
lean_dec(v_start_2376_);
v___x_2383_ = lean_usize_of_nat(v___y_2380_);
lean_dec(v___y_2380_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2374_, v___f_2369_, v_array_2375_, v___x_2382_, v___x_2383_);
v___x_2385_ = lean_unbox(v___x_2384_);
lean_dec(v___x_2384_);
if (v___x_2385_ == 0)
{
return v___x_2381_;
}
else
{
uint8_t v___x_2386_; 
v___x_2386_ = 0;
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2368_ = stack[0].m_num;
lean_object* v___f_2369_ = stack[1].m_obj;
lean_object* v_resOrder_2370_ = stack[2].m_obj;
uint8_t v_res_2389_;
v_res_2389_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_2368_, v___f_2369_, v_resOrder_2370_);
stack->m_num = v_res_2389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2390_, lean_object* v___f_2391_, lean_object* v_resOrder_2392_){
_start:
{
uint8_t v___x_1661__boxed_2393_; uint8_t v_res_2394_; lean_object* v_r_2395_; 
v___x_1661__boxed_2393_ = lean_unbox(v___x_2390_);
v_res_2394_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1661__boxed_2393_, v___f_2391_, v_resOrder_2392_);
v_r_2395_ = lean_box(v_res_2394_);
return v_r_2395_;
}
}
uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2396_, uint8_t v___y_2397_, lean_object* v_v_2398_){
_start:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_apply_1(v___f_2396_, v_v_2398_);
v___x_2400_ = lean_unbox(v___x_2399_);
if (v___x_2400_ == 0)
{
return v___y_2397_;
}
else
{
uint8_t v___x_2401_; 
v___x_2401_ = 0;
return v___x_2401_;
}
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2396_ = stack[0].m_obj;
uint8_t v___y_2397_ = stack[1].m_num;
lean_object* v_v_2398_ = stack[2].m_obj;
uint8_t v_res_2402_;
v_res_2402_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2396_, v___y_2397_, v_v_2398_);
stack->m_num = v_res_2402_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2403_, lean_object* v___y_2404_, lean_object* v_v_2405_){
_start:
{
uint8_t v___y_1755__boxed_2406_; uint8_t v_res_2407_; lean_object* v_r_2408_; 
v___y_1755__boxed_2406_ = lean_unbox(v___y_2404_);
v_res_2407_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2403_, v___y_1755__boxed_2406_, v_v_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2409_, uint8_t v___x_2410_, lean_object* v_v_2411_){
_start:
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = lean_apply_1(v___f_2409_, v_v_2411_);
v___x_2413_ = lean_unbox(v___x_2412_);
if (v___x_2413_ == 0)
{
return v___x_2410_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = 0;
return v___x_2414_;
}
}
}
LEAN_EXPORT void l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2409_ = stack[0].m_obj;
uint8_t v___x_2410_ = stack[1].m_num;
lean_object* v_v_2411_ = stack[2].m_obj;
uint8_t v_res_2415_;
v_res_2415_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2409_, v___x_2410_, v_v_2411_);
stack->m_num = v_res_2415_;
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2416_, lean_object* v___x_2417_, lean_object* v_v_2418_){
_start:
{
uint8_t v___x_1774__boxed_2419_; uint8_t v_res_2420_; lean_object* v_r_2421_; 
v___x_1774__boxed_2419_ = lean_unbox(v___x_2417_);
v_res_2420_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2416_, v___x_1774__boxed_2419_, v_v_2418_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2422_, lean_object* v_toPure_2423_, lean_object* v___x_2424_, lean_object* v_resOrders_2425_, lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v_toBind_2428_, lean_object* v___f_2429_, lean_object* v___x_2430_, lean_object* v_next_2431_, lean_object* v___x_2432_, lean_object* v_next_2433_, lean_object* v_acc_2434_, lean_object* v_h_2435_, lean_object* v_G_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_nat_dec_lt(v_next_2433_, v___x_2422_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_dec(v_G_2436_);
lean_dec(v_next_2433_);
lean_dec_ref(v___x_2430_);
lean_dec(v___f_2429_);
lean_dec(v_toBind_2428_);
lean_dec(v___x_2427_);
lean_dec_ref(v_resOrders_2425_);
lean_dec(v___x_2422_);
v___x_2438_ = lean_apply_2(v_toPure_2423_, lean_box(0), v_acc_2434_);
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_array_2443_; lean_object* v_start_2444_; lean_object* v_stop_2445_; lean_object* v___f_2446_; lean_object* v___y_2448_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; uint8_t v___y_2478_; uint8_t v___x_2490_; 
lean_dec_ref(v_acc_2434_);
v___x_2439_ = lean_array_get_borrowed(v___x_2424_, v_resOrders_2425_, v_next_2433_);
v___x_2440_ = lean_array_get(v___x_2426_, v___x_2439_, v___x_2427_);
lean_inc_n(v_next_2433_, 2);
lean_inc(v___x_2427_);
lean_inc_ref(v_resOrders_2425_);
v___x_2441_ = l_Array_toSubarray___redArg(v_resOrders_2425_, v___x_2427_, v_next_2433_);
v___x_2442_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2443_ = lean_ctor_get(v___x_2441_, 0);
lean_inc_ref(v_array_2443_);
v_start_2444_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_start_2444_);
v_stop_2445_ = lean_ctor_get(v___x_2441_, 2);
lean_inc(v_stop_2445_);
lean_dec_ref(v___x_2441_);
lean_inc(v_toPure_2423_);
v___f_2446_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2446_, 0, v_toPure_2423_);
lean_closure_set(v___f_2446_, 1, v_next_2433_);
lean_closure_set(v___f_2446_, 2, v_G_2436_);
v___x_2473_ = lean_box(v___x_2437_);
lean_inc(v___x_2440_);
v___f_2474_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_2474_, 0, v___x_2440_);
lean_closure_set(v___f_2474_, 1, v___x_2473_);
v___x_2475_ = lean_box(v___x_2437_);
v___f_2476_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2476_, 0, v___x_2475_);
lean_closure_set(v___f_2476_, 1, v___f_2474_);
v___x_2490_ = lean_nat_dec_lt(v_start_2444_, v_stop_2445_);
if (v___x_2490_ == 0)
{
lean_dec(v_stop_2445_);
lean_dec(v_start_2444_);
lean_dec_ref(v_array_2443_);
v___y_2478_ = v___x_2437_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___y_2494_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2491_ = lean_box(v___x_2437_);
lean_inc_ref(v___f_2476_);
v___f_2492_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2492_, 0, v___f_2476_);
lean_closure_set(v___f_2492_, 1, v___x_2491_);
v___x_2500_ = lean_array_get_size(v_array_2443_);
v___x_2501_ = lean_nat_dec_le(v_stop_2445_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec(v_stop_2445_);
v___y_2494_ = v___x_2500_;
goto v___jp_2493_;
}
else
{
v___y_2494_ = v_stop_2445_;
goto v___jp_2493_;
}
v___jp_2493_:
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_nat_dec_lt(v_start_2444_, v___y_2494_);
if (v___x_2495_ == 0)
{
lean_dec(v___y_2494_);
lean_dec_ref(v___f_2492_);
lean_dec(v_start_2444_);
lean_dec_ref(v_array_2443_);
v___y_2478_ = v___x_2490_;
goto v___jp_2477_;
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2496_ = lean_usize_of_nat(v_start_2444_);
lean_dec(v_start_2444_);
v___x_2497_ = lean_usize_of_nat(v___y_2494_);
lean_dec(v___y_2494_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2442_, v___f_2492_, v_array_2443_, v___x_2496_, v___x_2497_);
v___x_2499_ = lean_unbox(v___x_2498_);
lean_dec(v___x_2498_);
if (v___x_2499_ == 0)
{
v___y_2478_ = v___x_2495_;
goto v___jp_2477_;
}
else
{
lean_dec_ref(v___f_2476_);
lean_dec(v___x_2440_);
lean_dec(v_next_2433_);
lean_dec(v___x_2427_);
lean_dec_ref(v_resOrders_2425_);
lean_dec(v___x_2422_);
goto v___jp_2451_;
}
}
}
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_inc(v_toBind_2428_);
v___x_2449_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v___y_2448_, v___f_2429_);
v___x_2450_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v___x_2449_, v___f_2446_);
return v___x_2450_;
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2430_);
v___x_2453_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2452_);
v___y_2448_ = v___x_2453_;
goto v___jp_2447_;
}
v___jp_2454_:
{
uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2455_ = lean_nat_dec_eq(v_next_2431_, v___x_2427_);
lean_dec(v___x_2427_);
v___x_2456_ = lean_box(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2440_);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2432_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
v___x_2461_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2460_);
v___y_2448_ = v___x_2461_;
goto v___jp_2447_;
}
v___jp_2462_:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_lt(v___y_2465_, v___y_2467_);
if (v___x_2468_ == 0)
{
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec_ref(v___x_2430_);
goto v___jp_2454_;
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2469_ = lean_usize_of_nat(v___y_2465_);
lean_dec(v___y_2465_);
v___x_2470_ = lean_usize_of_nat(v___y_2467_);
lean_dec(v___y_2467_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2464_, v___y_2463_, v___y_2466_, v___x_2469_, v___x_2470_);
v___x_2472_ = lean_unbox(v___x_2471_);
lean_dec(v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v___x_2430_);
goto v___jp_2454_;
}
else
{
lean_dec(v___x_2440_);
lean_dec(v___x_2427_);
goto v___jp_2451_;
}
}
}
v___jp_2477_:
{
if (v___y_2478_ == 0)
{
lean_dec_ref(v___f_2476_);
lean_dec(v___x_2440_);
lean_dec(v_next_2433_);
lean_dec(v___x_2427_);
lean_dec_ref(v_resOrders_2425_);
lean_dec(v___x_2422_);
goto v___jp_2451_;
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_array_2482_; lean_object* v_start_2483_; lean_object* v_stop_2484_; uint8_t v___x_2485_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_next_2433_, v___x_2479_);
lean_dec(v_next_2433_);
v___x_2481_ = l_Array_toSubarray___redArg(v_resOrders_2425_, v___x_2480_, v___x_2422_);
v_array_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_array_2482_);
v_start_2483_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_start_2483_);
v_stop_2484_ = lean_ctor_get(v___x_2481_, 2);
lean_inc(v_stop_2484_);
lean_dec_ref(v___x_2481_);
v___x_2485_ = lean_nat_dec_lt(v_start_2483_, v_stop_2484_);
if (v___x_2485_ == 0)
{
lean_dec(v_stop_2484_);
lean_dec(v_start_2483_);
lean_dec_ref(v_array_2482_);
lean_dec_ref(v___f_2476_);
lean_dec_ref(v___x_2430_);
goto v___jp_2454_;
}
else
{
lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2486_ = lean_box(v___y_2478_);
v___f_2487_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2487_, 0, v___f_2476_);
lean_closure_set(v___f_2487_, 1, v___x_2486_);
v___x_2488_ = lean_array_get_size(v_array_2482_);
v___x_2489_ = lean_nat_dec_le(v_stop_2484_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_dec(v_stop_2484_);
v___y_2463_ = v___f_2487_;
v___y_2464_ = v___x_2442_;
v___y_2465_ = v_start_2483_;
v___y_2466_ = v_array_2482_;
v___y_2467_ = v___x_2488_;
goto v___jp_2462_;
}
else
{
v___y_2463_ = v___f_2487_;
v___y_2464_ = v___x_2442_;
v___y_2465_ = v_start_2483_;
v___y_2466_ = v_array_2482_;
v___y_2467_ = v_stop_2484_;
goto v___jp_2462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2502_, lean_object* v_toPure_2503_, lean_object* v___x_2504_, lean_object* v_resOrders_2505_, lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v_toBind_2508_, lean_object* v___f_2509_, lean_object* v___x_2510_, lean_object* v_next_2511_, lean_object* v___x_2512_, lean_object* v_next_2513_, lean_object* v_acc_2514_, lean_object* v_h_2515_, lean_object* v_G_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2502_, v_toPure_2503_, v___x_2504_, v_resOrders_2505_, v___x_2506_, v___x_2507_, v_toBind_2508_, v___f_2509_, v___x_2510_, v_next_2511_, v___x_2512_, v_next_2513_, v_acc_2514_, v_h_2515_, v_G_2516_);
lean_dec(v_next_2511_);
lean_dec(v___x_2506_);
lean_dec_ref(v___x_2504_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2518_, lean_object* v_toPure_2519_, lean_object* v___x_2520_, lean_object* v_resOrders_2521_, lean_object* v___x_2522_, lean_object* v___x_2523_, lean_object* v_toBind_2524_, lean_object* v___f_2525_, lean_object* v___x_2526_, lean_object* v___x_2527_, lean_object* v___f_2528_, lean_object* v___f_2529_, lean_object* v_next_2530_, lean_object* v_acc_2531_, lean_object* v_h_2532_, lean_object* v_G_2533_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_lt(v_next_2530_, v___x_2518_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec(v_G_2533_);
lean_dec(v_next_2530_);
lean_dec(v___f_2529_);
lean_dec(v___f_2528_);
lean_dec_ref(v___x_2526_);
lean_dec(v___f_2525_);
lean_dec(v_toBind_2524_);
lean_dec(v___x_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_resOrders_2521_);
lean_dec_ref(v___x_2520_);
v___x_2535_ = lean_apply_2(v_toPure_2519_, lean_box(0), v_acc_2531_);
return v___x_2535_;
}
else
{
lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v_acc_2531_);
lean_inc(v_next_2530_);
lean_inc(v_toPure_2519_);
v___f_2536_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2536_, 0, v_toPure_2519_);
lean_closure_set(v___f_2536_, 1, v_next_2530_);
lean_closure_set(v___f_2536_, 2, v_G_2533_);
v___x_2537_ = lean_nat_sub(v___x_2518_, v_next_2530_);
lean_inc_ref(v___x_2526_);
lean_inc_n(v_toBind_2524_, 3);
lean_inc(v___x_2523_);
v___f_2538_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2538_, 0, v___x_2537_);
lean_closure_set(v___f_2538_, 1, v_toPure_2519_);
lean_closure_set(v___f_2538_, 2, v___x_2520_);
lean_closure_set(v___f_2538_, 3, v_resOrders_2521_);
lean_closure_set(v___f_2538_, 4, v___x_2522_);
lean_closure_set(v___f_2538_, 5, v___x_2523_);
lean_closure_set(v___f_2538_, 6, v_toBind_2524_);
lean_closure_set(v___f_2538_, 7, v___f_2525_);
lean_closure_set(v___f_2538_, 8, v___x_2526_);
lean_closure_set(v___f_2538_, 9, v_next_2530_);
lean_closure_set(v___f_2538_, 10, v___x_2527_);
v___x_2539_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2538_, v___x_2523_, v___x_2526_, lean_box(0));
v___x_2540_ = lean_apply_4(v_toBind_2524_, lean_box(0), lean_box(0), v___x_2539_, v___f_2528_);
v___x_2541_ = lean_apply_4(v_toBind_2524_, lean_box(0), lean_box(0), v___x_2540_, v___f_2529_);
v___x_2542_ = lean_apply_4(v_toBind_2524_, lean_box(0), lean_box(0), v___x_2541_, v___f_2536_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2543_, lean_object* v_toPure_2544_, lean_object* v___x_2545_, lean_object* v_resOrders_2546_, lean_object* v___x_2547_, lean_object* v___x_2548_, lean_object* v_toBind_2549_, lean_object* v___f_2550_, lean_object* v___x_2551_, lean_object* v___x_2552_, lean_object* v___f_2553_, lean_object* v___f_2554_, lean_object* v_next_2555_, lean_object* v_acc_2556_, lean_object* v_h_2557_, lean_object* v_G_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2543_, v_toPure_2544_, v___x_2545_, v_resOrders_2546_, v___x_2547_, v___x_2548_, v_toBind_2549_, v___f_2550_, v___x_2551_, v___x_2552_, v___f_2553_, v___f_2554_, v_next_2555_, v_acc_2556_, v_h_2557_, v_G_2558_);
lean_dec(v___x_2543_);
return v_res_2559_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Array_instInhabited___redArg();
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2564_, lean_object* v_resOrders_2565_){
_start:
{
lean_object* v_toApplicative_2566_; lean_object* v_toBind_2567_; lean_object* v_toPure_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_toApplicative_2566_ = lean_ctor_get(v_inst_2564_, 0);
lean_inc_ref(v_toApplicative_2566_);
v_toBind_2567_ = lean_ctor_get(v_inst_2564_, 1);
lean_inc_n(v_toBind_2567_, 2);
lean_dec_ref(v_inst_2564_);
v_toPure_2568_ = lean_ctor_get(v_toApplicative_2566_, 1);
lean_inc_n(v_toPure_2568_, 4);
lean_dec_ref(v_toApplicative_2566_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2571_ = lean_array_get_size(v_resOrders_2565_);
lean_inc_ref(v_resOrders_2565_);
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2572_, 0, v___x_2570_);
lean_closure_set(v___f_2572_, 1, v_resOrders_2565_);
lean_closure_set(v___f_2572_, 2, v___x_2569_);
lean_closure_set(v___f_2572_, 3, v_toPure_2568_);
v___f_2573_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2573_, 0, v_toPure_2568_);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_box(0);
v___x_2576_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2577_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2577_, 0, v___x_2576_);
lean_closure_set(v___f_2577_, 1, v_toPure_2568_);
lean_closure_set(v___f_2577_, 2, v___x_2575_);
lean_inc_ref(v___f_2573_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2578_, 0, v___x_2571_);
lean_closure_set(v___f_2578_, 1, v_toPure_2568_);
lean_closure_set(v___f_2578_, 2, v___x_2570_);
lean_closure_set(v___f_2578_, 3, v_resOrders_2565_);
lean_closure_set(v___f_2578_, 4, v___x_2569_);
lean_closure_set(v___f_2578_, 5, v___x_2574_);
lean_closure_set(v___f_2578_, 6, v_toBind_2567_);
lean_closure_set(v___f_2578_, 7, v___f_2573_);
lean_closure_set(v___f_2578_, 8, v___x_2576_);
lean_closure_set(v___f_2578_, 9, v___x_2575_);
lean_closure_set(v___f_2578_, 10, v___f_2577_);
lean_closure_set(v___f_2578_, 11, v___f_2573_);
v___x_2579_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2578_, v___x_2574_, v___x_2576_, lean_box(0));
v___x_2580_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v___x_2579_, v___f_2572_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2581_, lean_object* v_inst_2582_, lean_object* v_resOrders_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2582_, v_resOrders_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2585_){
_start:
{
lean_object* v_structName_2586_; 
v_structName_2586_ = lean_ctor_get(v_x_2585_, 0);
lean_inc(v_structName_2586_);
return v_structName_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2587_);
lean_dec_ref(v_x_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2589_, lean_object* v_result_2590_, lean_object* v_____r_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_apply_2(v_toPure_2589_, lean_box(0), v_result_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2593_, lean_object* v_inst_2594_, lean_object* v_structName_2595_, lean_object* v_toBind_2596_, lean_object* v_result_2597_){
_start:
{
lean_object* v_resolutionOrder_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_resolutionOrder_2598_ = lean_ctor_get(v_result_2597_, 0);
lean_inc_ref(v_resolutionOrder_2598_);
v___f_2599_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2599_, 0, v_toPure_2593_);
lean_closure_set(v___f_2599_, 1, v_result_2597_);
v___x_2600_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2594_, v_structName_2595_, v_resolutionOrder_2598_);
v___x_2601_ = lean_apply_4(v_toBind_2596_, lean_box(0), lean_box(0), v___x_2600_, v___f_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_toPure_2602_, lean_object* v_____s_2603_){
_start:
{
lean_object* v_snd_2604_; lean_object* v_fst_2605_; lean_object* v_snd_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_snd_2604_ = lean_ctor_get(v_____s_2603_, 1);
lean_inc(v_snd_2604_);
lean_dec_ref(v_____s_2603_);
v_fst_2605_ = lean_ctor_get(v_snd_2604_, 0);
v_snd_2606_ = lean_ctor_get(v_snd_2604_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_snd_2604_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v_snd_2604_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_snd_2606_);
lean_inc(v_fst_2605_);
lean_dec(v_snd_2604_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fst_2605_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_snd_2606_);
v___x_2611_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_apply_2(v_toPure_2602_, lean_box(0), v___x_2611_);
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2615_, lean_object* v_____do__lift_2616_){
_start:
{
if (lean_obj_tag(v_____do__lift_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_a_2617_ = lean_ctor_get(v_____do__lift_2616_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_____do__lift_2616_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v_____do__lift_2616_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v_____do__lift_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_apply_2(v_toPure_2615_, lean_box(0), v___x_2622_);
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2634_; 
v_a_2626_ = lean_ctor_get(v_____do__lift_2616_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_____do__lift_2616_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2628_ = v_____do__lift_2616_;
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v_____do__lift_2616_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 0);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_apply_2(v_toPure_2615_, lean_box(0), v___x_2631_);
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2635_, lean_object* v___f_2636_, lean_object* v_x_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_array_get_size(v_x_2637_);
v___x_2639_ = lean_mk_empty_array_with_capacity(v___x_2635_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2641_ = lean_nat_dec_lt(v___x_2635_, v___x_2638_);
if (v___x_2641_ == 0)
{
lean_dec_ref(v_x_2637_);
lean_dec_ref(v___f_2636_);
return v___x_2639_;
}
else
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_le(v___x_2638_, v___x_2638_);
if (v___x_2642_ == 0)
{
if (v___x_2641_ == 0)
{
lean_dec_ref(v_x_2637_);
lean_dec_ref(v___f_2636_);
return v___x_2639_;
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = lean_usize_of_nat(v___x_2638_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2640_, v___f_2636_, v_x_2637_, v___x_2643_, v___x_2644_, v___x_2639_);
return v___x_2645_;
}
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2638_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2640_, v___f_2636_, v_x_2637_, v___x_2646_, v___x_2647_, v___x_2639_);
return v___x_2648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v___x_2649_, lean_object* v___f_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v___x_2649_, v___f_2650_, v_x_2651_);
lean_dec(v___x_2649_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v_snd_2653_, lean_object* v_x1_2654_, lean_object* v_x2_2655_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_name_eq(v_x2_2655_, v_snd_2653_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_array_push(v_x1_2654_, v_x2_2655_);
return v___x_2657_;
}
else
{
lean_dec(v_x2_2655_);
return v_x1_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v_snd_2658_, lean_object* v_x1_2659_, lean_object* v_x2_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v_snd_2658_, v_x1_2659_, v_x2_2660_);
lean_dec(v_snd_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2662_, lean_object* v___f_2663_, lean_object* v_x1_2664_, lean_object* v_x2_2665_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_array_2669_; lean_object* v_start_2670_; lean_object* v_stop_2671_; lean_object* v___y_2673_; uint8_t v___x_2680_; 
v___x_2666_ = lean_array_get_size(v_x2_2665_);
lean_inc_ref(v_x2_2665_);
v___x_2667_ = l_Array_toSubarray___redArg(v_x2_2665_, v___x_2662_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2669_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref(v_array_2669_);
v_start_2670_ = lean_ctor_get(v___x_2667_, 1);
lean_inc(v_start_2670_);
v_stop_2671_ = lean_ctor_get(v___x_2667_, 2);
lean_inc(v_stop_2671_);
lean_dec_ref(v___x_2667_);
v___x_2680_ = lean_nat_dec_lt(v_start_2670_, v_stop_2671_);
if (v___x_2680_ == 0)
{
lean_dec(v_stop_2671_);
lean_dec(v_start_2670_);
lean_dec_ref(v_array_2669_);
lean_dec_ref(v_x2_2665_);
lean_dec_ref(v___f_2663_);
return v_x1_2664_;
}
else
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = lean_array_get_size(v_array_2669_);
v___x_2682_ = lean_nat_dec_le(v_stop_2671_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec(v_stop_2671_);
v___y_2673_ = v___x_2681_;
goto v___jp_2672_;
}
else
{
v___y_2673_ = v_stop_2671_;
goto v___jp_2672_;
}
}
v___jp_2672_:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_nat_dec_lt(v_start_2670_, v___y_2673_);
if (v___x_2674_ == 0)
{
lean_dec(v___y_2673_);
lean_dec(v_start_2670_);
lean_dec_ref(v_array_2669_);
lean_dec_ref(v_x2_2665_);
lean_dec_ref(v___f_2663_);
return v_x1_2664_;
}
else
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2675_ = lean_usize_of_nat(v_start_2670_);
lean_dec(v_start_2670_);
v___x_2676_ = lean_usize_of_nat(v___y_2673_);
lean_dec(v___y_2673_);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2668_, v___f_2663_, v_array_2669_, v___x_2675_, v___x_2676_);
v___x_2678_ = lean_unbox(v___x_2677_);
lean_dec(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v_x2_2665_);
return v_x1_2664_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_array_push(v_x1_2664_, v_x2_2665_);
return v___x_2679_;
}
}
}
}
}
uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2683_, lean_object* v_x_2684_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_name_eq(v_x_2684_, v_snd_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2683_ = stack[0].m_obj;
lean_object* v_x_2684_ = stack[1].m_obj;
uint8_t v_res_2686_;
v_res_2686_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2683_, v_x_2684_);
stack->m_num = v_res_2686_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2687_, v_x_2688_);
lean_dec(v_x_2688_);
lean_dec(v_snd_2687_);
v_r_2690_ = lean_box(v_res_2689_);
return v_r_2690_;
}
}
lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2692_, lean_object* v___x_2693_, lean_object* v_fst_2694_, lean_object* v_fst_2695_, lean_object* v___f_2696_, uint8_t v_relaxed_2697_, lean_object* v___x_2698_, lean_object* v_parentNames_2699_, lean_object* v___f_2700_, lean_object* v_snd_2701_, lean_object* v___f_2702_, lean_object* v___x_2703_, lean_object* v_____x_2704_){
_start:
{
lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; lean_object* v_defects_2718_; lean_object* v___y_2733_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2757_; uint8_t v___x_2767_; 
v_fst_2713_ = lean_ctor_get(v_____x_2704_, 0);
lean_inc(v_fst_2713_);
v_snd_2714_ = lean_ctor_get(v_____x_2704_, 1);
lean_inc_n(v_snd_2714_, 2);
lean_dec_ref(v_____x_2704_);
v___f_2715_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2715_, 0, v_snd_2714_);
lean_inc(v___x_2693_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 3, 2);
lean_closure_set(v___f_2716_, 0, v___x_2693_);
lean_closure_set(v___f_2716_, 1, v___f_2715_);
v___x_2767_ = lean_unbox(v_fst_2713_);
lean_dec(v_fst_2713_);
if (v___x_2767_ == 0)
{
if (v_relaxed_2697_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2768_ = lean_array_get_size(v_fst_2695_);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2693_);
v___x_2770_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2771_ = lean_nat_dec_lt(v___x_2693_, v___x_2768_);
if (v___x_2771_ == 0)
{
v___y_2757_ = v___x_2769_;
goto v___jp_2756_;
}
else
{
lean_object* v___f_2772_; lean_object* v___f_2773_; uint8_t v___x_2774_; 
lean_inc(v_snd_2714_);
v___f_2772_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2772_, 0, v_snd_2714_);
lean_inc(v___x_2703_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2773_, 0, v___x_2703_);
lean_closure_set(v___f_2773_, 1, v___f_2772_);
v___x_2774_ = lean_nat_dec_le(v___x_2768_, v___x_2768_);
if (v___x_2774_ == 0)
{
if (v___x_2771_ == 0)
{
lean_dec_ref(v___f_2773_);
v___y_2757_ = v___x_2769_;
goto v___jp_2756_;
}
else
{
size_t v___x_2775_; size_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = ((size_t)0ULL);
v___x_2776_ = lean_usize_of_nat(v___x_2768_);
lean_inc(v_fst_2695_);
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2770_, v___f_2773_, v_fst_2695_, v___x_2775_, v___x_2776_, v___x_2769_);
v___y_2757_ = v___x_2777_;
goto v___jp_2756_;
}
}
else
{
size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = ((size_t)0ULL);
v___x_2779_ = lean_usize_of_nat(v___x_2768_);
lean_inc(v_fst_2695_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2770_, v___f_2773_, v_fst_2695_, v___x_2778_, v___x_2779_, v___x_2769_);
v___y_2757_ = v___x_2780_;
goto v___jp_2756_;
}
}
}
else
{
lean_dec(v___x_2703_);
lean_dec_ref(v___f_2702_);
lean_dec_ref(v___f_2700_);
lean_dec_ref(v_parentNames_2699_);
lean_dec_ref(v___x_2698_);
v_defects_2718_ = v_snd_2701_;
goto v___jp_2717_;
}
}
else
{
lean_dec(v___x_2703_);
lean_dec_ref(v___f_2702_);
lean_dec_ref(v___f_2700_);
lean_dec_ref(v_parentNames_2699_);
lean_dec_ref(v___x_2698_);
v_defects_2718_ = v_snd_2701_;
goto v___jp_2717_;
}
v___jp_2705_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2706_);
lean_ctor_set(v___x_2709_, 1, v___y_2707_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
v___x_2712_ = lean_apply_2(v_toPure_2692_, lean_box(0), v___x_2711_);
return v___x_2712_;
}
v___jp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; size_t v_sz_2721_; size_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2719_ = lean_array_push(v_fst_2694_, v_snd_2714_);
v___x_2720_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2721_ = lean_array_size(v_fst_2695_);
v___x_2722_ = ((size_t)0ULL);
v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2720_, v___f_2716_, v_sz_2721_, v___x_2722_, v_fst_2695_);
v___x_2724_ = lean_array_get_size(v___x_2723_);
v___x_2725_ = lean_mk_empty_array_with_capacity(v___x_2693_);
v___x_2726_ = lean_nat_dec_lt(v___x_2693_, v___x_2724_);
lean_dec(v___x_2693_);
if (v___x_2726_ == 0)
{
lean_dec(v___x_2723_);
lean_dec_ref(v___f_2696_);
v___y_2706_ = v___x_2719_;
v___y_2707_ = v_defects_2718_;
v___y_2708_ = v___x_2725_;
goto v___jp_2705_;
}
else
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_nat_dec_le(v___x_2724_, v___x_2724_);
if (v___x_2727_ == 0)
{
if (v___x_2726_ == 0)
{
lean_dec(v___x_2723_);
lean_dec_ref(v___f_2696_);
v___y_2706_ = v___x_2719_;
v___y_2707_ = v_defects_2718_;
v___y_2708_ = v___x_2725_;
goto v___jp_2705_;
}
else
{
size_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2720_, v___f_2696_, v___x_2723_, v___x_2722_, v___x_2728_, v___x_2725_);
v___y_2706_ = v___x_2719_;
v___y_2707_ = v_defects_2718_;
v___y_2708_ = v___x_2729_;
goto v___jp_2705_;
}
}
else
{
size_t v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_usize_of_nat(v___x_2724_);
v___x_2731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2720_, v___f_2696_, v___x_2723_, v___x_2722_, v___x_2730_, v___x_2725_);
v___y_2706_ = v___x_2719_;
v___y_2707_ = v_defects_2718_;
v___y_2708_ = v___x_2731_;
goto v___jp_2705_;
}
}
}
v___jp_2732_:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_inc_ref(v___x_2698_);
v___x_2734_ = l_Array_eraseReps___redArg(v___x_2698_, v___y_2733_);
lean_inc_n(v_snd_2714_, 2);
v___x_2735_ = l_Array_contains___redArg(v___x_2698_, v_parentNames_2699_, v_snd_2714_);
v___x_2736_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2737_ = lean_array_size(v___x_2734_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2736_, v___f_2700_, v_sz_2737_, v___x_2738_, v___x_2734_);
v___x_2740_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2740_, 0, v_snd_2714_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*2, v___x_2735_);
v___x_2741_ = lean_array_push(v_snd_2701_, v___x_2740_);
v_defects_2718_ = v___x_2741_;
goto v___jp_2717_;
}
v___jp_2742_:
{
lean_object* v___x_2748_; 
lean_inc_ref(v___y_2743_);
v___x_2748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2747_);
lean_dec(v___y_2744_);
v___y_2733_ = v___x_2748_;
goto v___jp_2732_;
}
v___jp_2749_:
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_nat_dec_le(v___y_2754_, v___y_2752_);
if (v___x_2755_ == 0)
{
lean_dec(v___y_2752_);
lean_inc(v___y_2754_);
v___y_2743_ = v___y_2750_;
v___y_2744_ = v___y_2751_;
v___y_2745_ = v___y_2753_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2754_;
goto v___jp_2742_;
}
else
{
v___y_2743_ = v___y_2750_;
v___y_2744_ = v___y_2751_;
v___y_2745_ = v___y_2753_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2752_;
goto v___jp_2742_;
}
}
v___jp_2756_:
{
lean_object* v___x_2758_; size_t v_sz_2759_; size_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2758_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2759_ = lean_array_size(v___y_2757_);
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2758_, v___f_2702_, v_sz_2759_, v___x_2760_, v___y_2757_);
v___x_2762_ = lean_array_get_size(v___x_2761_);
v___x_2763_ = lean_nat_dec_eq(v___x_2762_, v___x_2693_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2765_ = lean_nat_sub(v___x_2762_, v___x_2703_);
lean_dec(v___x_2703_);
v___x_2766_ = lean_nat_dec_le(v___x_2693_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_inc(v___x_2765_);
v___y_2750_ = v___x_2764_;
v___y_2751_ = v___x_2762_;
v___y_2752_ = v___x_2765_;
v___y_2753_ = v___x_2761_;
v___y_2754_ = v___x_2765_;
goto v___jp_2749_;
}
else
{
lean_inc(v___x_2693_);
v___y_2750_ = v___x_2764_;
v___y_2751_ = v___x_2762_;
v___y_2752_ = v___x_2765_;
v___y_2753_ = v___x_2761_;
v___y_2754_ = v___x_2693_;
goto v___jp_2749_;
}
}
else
{
lean_dec(v___x_2703_);
v___y_2733_ = v___x_2761_;
goto v___jp_2732_;
}
}
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2692_ = stack[0].m_obj;
lean_object* v___x_2693_ = stack[1].m_obj;
lean_object* v_fst_2694_ = stack[2].m_obj;
lean_object* v_fst_2695_ = stack[3].m_obj;
lean_object* v___f_2696_ = stack[4].m_obj;
uint8_t v_relaxed_2697_ = stack[5].m_num;
lean_object* v___x_2698_ = stack[6].m_obj;
lean_object* v_parentNames_2699_ = stack[7].m_obj;
lean_object* v___f_2700_ = stack[8].m_obj;
lean_object* v_snd_2701_ = stack[9].m_obj;
lean_object* v___f_2702_ = stack[10].m_obj;
lean_object* v___x_2703_ = stack[11].m_obj;
lean_object* v_____x_2704_ = stack[12].m_obj;
lean_object* v_res_2781_;
v_res_2781_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2692_, v___x_2693_, v_fst_2694_, v_fst_2695_, v___f_2696_, v_relaxed_2697_, v___x_2698_, v_parentNames_2699_, v___f_2700_, v_snd_2701_, v___f_2702_, v___x_2703_, v_____x_2704_);
stack->m_obj
 = v_res_2781_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2782_, lean_object* v___x_2783_, lean_object* v_fst_2784_, lean_object* v_fst_2785_, lean_object* v___f_2786_, lean_object* v_relaxed_2787_, lean_object* v___x_2788_, lean_object* v_parentNames_2789_, lean_object* v___f_2790_, lean_object* v_snd_2791_, lean_object* v___f_2792_, lean_object* v___x_2793_, lean_object* v_____x_2794_){
_start:
{
uint8_t v_relaxed_boxed_2795_; lean_object* v_res_2796_; 
v_relaxed_boxed_2795_ = lean_unbox(v_relaxed_2787_);
v_res_2796_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2782_, v___x_2783_, v_fst_2784_, v_fst_2785_, v___f_2786_, v_relaxed_boxed_2795_, v___x_2788_, v_parentNames_2789_, v___f_2790_, v_snd_2791_, v___f_2792_, v___x_2793_, v_____x_2794_);
return v_res_2796_;
}
}
lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2797_, lean_object* v_toPure_2798_, lean_object* v___f_2799_, uint8_t v_relaxed_2800_, lean_object* v___x_2801_, lean_object* v_parentNames_2802_, lean_object* v___f_2803_, lean_object* v___f_2804_, lean_object* v___x_2805_, lean_object* v_inst_2806_, lean_object* v_toBind_2807_, lean_object* v___f_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v_snd_2810_; lean_object* v_fst_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2837_; 
v_snd_2810_ = lean_ctor_get(v_b_2809_, 1);
v_fst_2811_ = lean_ctor_get(v_b_2809_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_b_2809_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2813_ = v_b_2809_;
v_isShared_2814_ = v_isSharedCheck_2837_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_snd_2810_);
lean_inc(v_fst_2811_);
lean_dec(v_b_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2837_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2836_; 
v_fst_2815_ = lean_ctor_get(v_snd_2810_, 0);
v_snd_2816_ = lean_ctor_get(v_snd_2810_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_snd_2810_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2818_ = v_snd_2810_;
v_isShared_2819_ = v_isSharedCheck_2836_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_snd_2816_);
lean_inc(v_fst_2815_);
lean_dec(v_snd_2810_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2836_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = lean_array_get_size(v_fst_2811_);
v___x_2821_ = lean_nat_dec_eq(v___x_2820_, v___x_2797_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_del_object(v___x_2818_);
lean_del_object(v___x_2813_);
v___x_2822_ = lean_box(v_relaxed_2800_);
lean_inc(v_fst_2811_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 13, 12);
lean_closure_set(v___f_2823_, 0, v_toPure_2798_);
lean_closure_set(v___f_2823_, 1, v___x_2797_);
lean_closure_set(v___f_2823_, 2, v_fst_2815_);
lean_closure_set(v___f_2823_, 3, v_fst_2811_);
lean_closure_set(v___f_2823_, 4, v___f_2799_);
lean_closure_set(v___f_2823_, 5, v___x_2822_);
lean_closure_set(v___f_2823_, 6, v___x_2801_);
lean_closure_set(v___f_2823_, 7, v_parentNames_2802_);
lean_closure_set(v___f_2823_, 8, v___f_2803_);
lean_closure_set(v___f_2823_, 9, v_snd_2816_);
lean_closure_set(v___f_2823_, 10, v___f_2804_);
lean_closure_set(v___f_2823_, 11, v___x_2805_);
v___x_2824_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2806_, v_fst_2811_);
lean_inc(v_toBind_2807_);
v___x_2825_ = lean_apply_4(v_toBind_2807_, lean_box(0), lean_box(0), v___x_2824_, v___f_2823_);
v___x_2826_ = lean_apply_4(v_toBind_2807_, lean_box(0), lean_box(0), v___x_2825_, v___f_2808_);
return v___x_2826_;
}
else
{
lean_object* v___x_2828_; 
lean_dec_ref(v_inst_2806_);
lean_dec(v___x_2805_);
lean_dec_ref(v___f_2804_);
lean_dec_ref(v___f_2803_);
lean_dec_ref(v_parentNames_2802_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v___f_2799_);
lean_dec(v___x_2797_);
if (v_isShared_2819_ == 0)
{
v___x_2828_ = v___x_2818_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_fst_2815_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_snd_2816_);
v___x_2828_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 1, v___x_2828_);
v___x_2830_ = v___x_2813_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_fst_2811_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
v___x_2832_ = lean_apply_2(v_toPure_2798_, lean_box(0), v___x_2831_);
v___x_2833_ = lean_apply_4(v_toBind_2807_, lean_box(0), lean_box(0), v___x_2832_, v___f_2808_);
return v___x_2833_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2797_ = stack[0].m_obj;
lean_object* v_toPure_2798_ = stack[1].m_obj;
lean_object* v___f_2799_ = stack[2].m_obj;
uint8_t v_relaxed_2800_ = stack[3].m_num;
lean_object* v___x_2801_ = stack[4].m_obj;
lean_object* v_parentNames_2802_ = stack[5].m_obj;
lean_object* v___f_2803_ = stack[6].m_obj;
lean_object* v___f_2804_ = stack[7].m_obj;
lean_object* v___x_2805_ = stack[8].m_obj;
lean_object* v_inst_2806_ = stack[9].m_obj;
lean_object* v_toBind_2807_ = stack[10].m_obj;
lean_object* v___f_2808_ = stack[11].m_obj;
lean_object* v_b_2809_ = stack[12].m_obj;
lean_object* v_res_2838_;
v_res_2838_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2797_, v_toPure_2798_, v___f_2799_, v_relaxed_2800_, v___x_2801_, v_parentNames_2802_, v___f_2803_, v___f_2804_, v___x_2805_, v_inst_2806_, v_toBind_2807_, v___f_2808_, v_b_2809_);
stack->m_obj
 = v_res_2838_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2839_, lean_object* v_toPure_2840_, lean_object* v___f_2841_, lean_object* v_relaxed_2842_, lean_object* v___x_2843_, lean_object* v_parentNames_2844_, lean_object* v___f_2845_, lean_object* v___f_2846_, lean_object* v___x_2847_, lean_object* v_inst_2848_, lean_object* v_toBind_2849_, lean_object* v___f_2850_, lean_object* v_b_2851_){
_start:
{
uint8_t v_relaxed_boxed_2852_; lean_object* v_res_2853_; 
v_relaxed_boxed_2852_ = lean_unbox(v_relaxed_2842_);
v_res_2853_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2839_, v_toPure_2840_, v___f_2841_, v_relaxed_boxed_2852_, v___x_2843_, v_parentNames_2844_, v___f_2845_, v___f_2846_, v___x_2847_, v_inst_2848_, v_toBind_2849_, v___f_2850_, v_b_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_x_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_array_get_borrowed(v___x_2854_, v_x_2856_, v___x_2855_);
lean_inc(v___x_2857_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2858_, v___x_2859_, v_x_2860_);
lean_dec_ref(v_x_2860_);
lean_dec(v___x_2859_);
lean_dec(v___x_2858_);
return v_res_2861_;
}
}
lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v___x_2864_, lean_object* v_toPure_2865_, lean_object* v___f_2866_, uint8_t v_relaxed_2867_, lean_object* v___x_2868_, lean_object* v_parentNames_2869_, lean_object* v___f_2870_, lean_object* v_inst_2871_, lean_object* v_toBind_2872_, lean_object* v___f_2873_, lean_object* v_structName_2874_, lean_object* v___f_2875_, lean_object* v___f_2876_, lean_object* v_parentResOrders_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___y_2881_; lean_object* v_j_2892_; lean_object* v_as_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2879_, 0, v___x_2864_);
lean_closure_set(v___f_2879_, 1, v___x_2878_);
v_j_2892_ = lean_array_get_size(v_parentResOrders_2877_);
lean_inc_ref(v_parentNames_2869_);
v_as_2893_ = lean_array_push(v_parentResOrders_2877_, v_parentNames_2869_);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2878_, v_as_2893_, v_j_2892_);
v___x_2895_ = lean_array_get_size(v___x_2894_);
v___x_2896_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v___x_2897_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2898_ = lean_nat_dec_lt(v___x_2878_, v___x_2895_);
if (v___x_2898_ == 0)
{
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___f_2876_);
v___y_2881_ = v___x_2896_;
goto v___jp_2880_;
}
else
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_nat_dec_le(v___x_2895_, v___x_2895_);
if (v___x_2899_ == 0)
{
if (v___x_2898_ == 0)
{
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___f_2876_);
v___y_2881_ = v___x_2896_;
goto v___jp_2880_;
}
else
{
size_t v___x_2900_; size_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = ((size_t)0ULL);
v___x_2901_ = lean_usize_of_nat(v___x_2895_);
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2897_, v___f_2876_, v___x_2894_, v___x_2900_, v___x_2901_, v___x_2896_);
v___y_2881_ = v___x_2902_;
goto v___jp_2880_;
}
}
else
{
size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = ((size_t)0ULL);
v___x_2904_ = lean_usize_of_nat(v___x_2895_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2897_, v___f_2876_, v___x_2894_, v___x_2903_, v___x_2904_, v___x_2896_);
v___y_2881_ = v___x_2905_;
goto v___jp_2880_;
}
}
v___jp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___f_2884_; lean_object* v___x_2885_; lean_object* v_resOrder_2886_; lean_object* v_defects_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_box(v_relaxed_2867_);
lean_inc(v_toBind_2872_);
lean_inc_ref(v_inst_2871_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_2884_, 0, v___x_2878_);
lean_closure_set(v___f_2884_, 1, v_toPure_2865_);
lean_closure_set(v___f_2884_, 2, v___f_2866_);
lean_closure_set(v___f_2884_, 3, v___x_2883_);
lean_closure_set(v___f_2884_, 4, v___x_2868_);
lean_closure_set(v___f_2884_, 5, v_parentNames_2869_);
lean_closure_set(v___f_2884_, 6, v___f_2870_);
lean_closure_set(v___f_2884_, 7, v___f_2879_);
lean_closure_set(v___f_2884_, 8, v___x_2882_);
lean_closure_set(v___f_2884_, 9, v_inst_2871_);
lean_closure_set(v___f_2884_, 10, v_toBind_2872_);
lean_closure_set(v___f_2884_, 11, v___f_2873_);
v___x_2885_ = lean_mk_empty_array_with_capacity(v___x_2882_);
v_resOrder_2886_ = lean_array_push(v___x_2885_, v_structName_2874_);
v_defects_2887_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_resOrder_2886_);
lean_ctor_set(v___x_2888_, 1, v_defects_2887_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2881_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2871_, v___f_2884_, v___x_2889_);
v___x_2891_ = lean_apply_4(v_toBind_2872_, lean_box(0), lean_box(0), v___x_2890_, v___f_2875_);
return v___x_2891_;
}
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2864_ = stack[0].m_obj;
lean_object* v_toPure_2865_ = stack[1].m_obj;
lean_object* v___f_2866_ = stack[2].m_obj;
uint8_t v_relaxed_2867_ = stack[3].m_num;
lean_object* v___x_2868_ = stack[4].m_obj;
lean_object* v_parentNames_2869_ = stack[5].m_obj;
lean_object* v___f_2870_ = stack[6].m_obj;
lean_object* v_inst_2871_ = stack[7].m_obj;
lean_object* v_toBind_2872_ = stack[8].m_obj;
lean_object* v___f_2873_ = stack[9].m_obj;
lean_object* v_structName_2874_ = stack[10].m_obj;
lean_object* v___f_2875_ = stack[11].m_obj;
lean_object* v___f_2876_ = stack[12].m_obj;
lean_object* v_parentResOrders_2877_ = stack[13].m_obj;
lean_object* v_res_2906_;
v_res_2906_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v___x_2864_, v_toPure_2865_, v___f_2866_, v_relaxed_2867_, v___x_2868_, v_parentNames_2869_, v___f_2870_, v_inst_2871_, v_toBind_2872_, v___f_2873_, v_structName_2874_, v___f_2875_, v___f_2876_, v_parentResOrders_2877_);
stack->m_obj
 = v_res_2906_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v___x_2907_, lean_object* v_toPure_2908_, lean_object* v___f_2909_, lean_object* v_relaxed_2910_, lean_object* v___x_2911_, lean_object* v_parentNames_2912_, lean_object* v___f_2913_, lean_object* v_inst_2914_, lean_object* v_toBind_2915_, lean_object* v___f_2916_, lean_object* v_structName_2917_, lean_object* v___f_2918_, lean_object* v___f_2919_, lean_object* v_parentResOrders_2920_){
_start:
{
uint8_t v_relaxed_boxed_2921_; lean_object* v_res_2922_; 
v_relaxed_boxed_2921_ = lean_unbox(v_relaxed_2910_);
v_res_2922_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v___x_2907_, v_toPure_2908_, v___f_2909_, v_relaxed_boxed_2921_, v___x_2911_, v_parentNames_2912_, v___f_2913_, v_inst_2914_, v_toBind_2915_, v___f_2916_, v_structName_2917_, v___f_2918_, v___f_2919_, v_parentResOrders_2920_);
return v_res_2922_;
}
}
uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = lean_array_get_size(v_x_2923_);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = lean_nat_dec_eq(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
uint8_t v___x_2927_; 
v___x_2927_ = 1;
return v___x_2927_;
}
else
{
uint8_t v___x_2928_; 
v___x_2928_ = 0;
return v___x_2928_;
}
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2923_ = stack[0].m_obj;
uint8_t v_res_2929_;
v_res_2929_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2923_);
stack->m_num = v_res_2929_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2930_);
lean_dec_ref(v_x_2930_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2933_, lean_object* v_x1_2934_, lean_object* v_x2_2935_){
_start:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
lean_inc_ref(v_x2_2935_);
v___x_2936_ = lean_apply_1(v___f_2933_, v_x2_2935_);
v___x_2937_ = lean_unbox(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_dec_ref(v_x2_2935_);
return v_x1_2934_;
}
else
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_array_push(v_x1_2934_, v_x2_2935_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_toPure_2939_, lean_object* v_____do__lift_2940_){
_start:
{
lean_object* v_resolutionOrder_2941_; lean_object* v___x_2942_; 
v_resolutionOrder_2941_ = lean_ctor_get(v_____do__lift_2940_, 0);
lean_inc_ref(v_resolutionOrder_2941_);
lean_dec_ref(v_____do__lift_2940_);
v___x_2942_ = lean_apply_2(v_toPure_2939_, lean_box(0), v_resolutionOrder_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v___x_2943_, lean_object* v_parentNames_2944_, lean_object* v_x_2945_){
_start:
{
uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_inc(v_x_2945_);
v___x_2946_ = l_Array_contains___redArg(v___x_2943_, v_parentNames_2944_, v_x_2945_);
v___x_2947_ = lean_box(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v_x_2945_);
return v___x_2948_;
}
}
lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_structName_2955_, lean_object* v_parentNames_2956_, uint8_t v_relaxed_2957_){
_start:
{
lean_object* v_toApplicative_2958_; lean_object* v_toBind_2959_; lean_object* v_toPure_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___x_2964_; lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___f_2970_; size_t v_sz_2971_; size_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_toApplicative_2958_ = lean_ctor_get(v_inst_2953_, 0);
v_toBind_2959_ = lean_ctor_get(v_inst_2953_, 1);
lean_inc_n(v_toBind_2959_, 3);
v_toPure_2960_ = lean_ctor_get(v_toApplicative_2958_, 1);
v___f_2961_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
v___x_2962_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref_n(v_parentNames_2956_, 2);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 3, 2);
lean_closure_set(v___f_2963_, 0, v___x_2962_);
lean_closure_set(v___f_2963_, 1, v_parentNames_2956_);
v___x_2964_ = lean_box(0);
lean_inc_n(v_toPure_2960_, 4);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2965_, 0, v_toPure_2960_);
lean_inc_ref_n(v_inst_2953_, 2);
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2966_, 0, v_inst_2953_);
lean_closure_set(v___f_2966_, 1, v_inst_2954_);
lean_closure_set(v___f_2966_, 2, v_toBind_2959_);
lean_closure_set(v___f_2966_, 3, v___f_2965_);
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2967_, 0, v_toPure_2960_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6), 2, 1);
lean_closure_set(v___f_2968_, 0, v_toPure_2960_);
v___x_2969_ = lean_box(v_relaxed_2957_);
v___f_2970_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 14, 13);
lean_closure_set(v___f_2970_, 0, v___x_2964_);
lean_closure_set(v___f_2970_, 1, v_toPure_2960_);
lean_closure_set(v___f_2970_, 2, v___f_2961_);
lean_closure_set(v___f_2970_, 3, v___x_2969_);
lean_closure_set(v___f_2970_, 4, v___x_2962_);
lean_closure_set(v___f_2970_, 5, v_parentNames_2956_);
lean_closure_set(v___f_2970_, 6, v___f_2963_);
lean_closure_set(v___f_2970_, 7, v_inst_2953_);
lean_closure_set(v___f_2970_, 8, v_toBind_2959_);
lean_closure_set(v___f_2970_, 9, v___f_2967_);
lean_closure_set(v___f_2970_, 10, v_structName_2955_);
lean_closure_set(v___f_2970_, 11, v___f_2968_);
lean_closure_set(v___f_2970_, 12, v___f_2961_);
v_sz_2971_ = lean_array_size(v_parentNames_2956_);
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2953_, v___f_2966_, v_sz_2971_, v___x_2972_, v_parentNames_2956_);
v___x_2974_ = lean_apply_4(v_toBind_2959_, lean_box(0), lean_box(0), v___x_2973_, v___f_2970_);
return v___x_2974_;
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2953_ = stack[0].m_obj;
lean_object* v_inst_2954_ = stack[1].m_obj;
lean_object* v_structName_2955_ = stack[2].m_obj;
lean_object* v_parentNames_2956_ = stack[3].m_obj;
uint8_t v_relaxed_2957_ = stack[4].m_num;
lean_object* v_res_2975_;
v_res_2975_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2953_, v_inst_2954_, v_structName_2955_, v_parentNames_2956_, v_relaxed_2957_);
stack->m_obj
 = v_res_2975_;
}
lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2976_, lean_object* v_toPure_2977_, lean_object* v___f_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, uint8_t v_relaxed_2981_, lean_object* v_toBind_2982_, lean_object* v___f_2983_, lean_object* v_env_2984_){
_start:
{
lean_object* v___x_2985_; 
lean_inc_ref(v_env_2984_);
v___x_2985_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2984_, v_structName_2976_);
if (lean_obj_tag(v___x_2985_) == 1)
{
lean_object* v_val_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v_env_2984_);
lean_dec(v___f_2983_);
lean_dec(v_toBind_2982_);
lean_dec_ref(v_inst_2980_);
lean_dec_ref(v_inst_2979_);
lean_dec_ref(v___f_2978_);
lean_dec(v_structName_2976_);
v_val_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_val_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_val_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_apply_2(v_toPure_2977_, lean_box(0), v___x_2988_);
return v___x_2989_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v_parentNames_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v___x_2985_);
lean_dec(v_toPure_2977_);
lean_inc(v_structName_2976_);
v___x_2990_ = l_Lean_getStructureParentInfo(v_env_2984_, v_structName_2976_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2992_ = lean_array_size(v___x_2990_);
v___x_2993_ = ((size_t)0ULL);
v_parentNames_2994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2991_, v___f_2978_, v_sz_2992_, v___x_2993_, v___x_2990_);
v___x_2995_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2979_, v_inst_2980_, v_structName_2976_, v_parentNames_2994_, v_relaxed_2981_);
v___x_2996_ = lean_apply_4(v_toBind_2982_, lean_box(0), lean_box(0), v___x_2995_, v___f_2983_);
return v___x_2996_;
}
}
}
LEAN_EXPORT void l_Lean_computeStructureResolutionOrder___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_2976_ = stack[0].m_obj;
lean_object* v_toPure_2977_ = stack[1].m_obj;
lean_object* v___f_2978_ = stack[2].m_obj;
lean_object* v_inst_2979_ = stack[3].m_obj;
lean_object* v_inst_2980_ = stack[4].m_obj;
uint8_t v_relaxed_2981_ = stack[5].m_num;
lean_object* v_toBind_2982_ = stack[6].m_obj;
lean_object* v___f_2983_ = stack[7].m_obj;
lean_object* v_env_2984_ = stack[8].m_obj;
lean_object* v_res_2997_;
v_res_2997_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2976_, v_toPure_2977_, v___f_2978_, v_inst_2979_, v_inst_2980_, v_relaxed_2981_, v_toBind_2982_, v___f_2983_, v_env_2984_);
stack->m_obj
 = v_res_2997_;
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2998_, lean_object* v_toPure_2999_, lean_object* v___f_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_relaxed_3003_, lean_object* v_toBind_3004_, lean_object* v___f_3005_, lean_object* v_env_3006_){
_start:
{
uint8_t v_relaxed_boxed_3007_; lean_object* v_res_3008_; 
v_relaxed_boxed_3007_ = lean_unbox(v_relaxed_3003_);
v_res_3008_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2998_, v_toPure_2999_, v___f_3000_, v_inst_3001_, v_inst_3002_, v_relaxed_boxed_3007_, v_toBind_3004_, v___f_3005_, v_env_3006_);
return v_res_3008_;
}
}
lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_structName_3011_, uint8_t v_relaxed_3012_){
_start:
{
lean_object* v_toApplicative_3013_; lean_object* v_toBind_3014_; lean_object* v_getEnv_3015_; lean_object* v_toPure_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; 
v_toApplicative_3013_ = lean_ctor_get(v_inst_3009_, 0);
v_toBind_3014_ = lean_ctor_get(v_inst_3009_, 1);
lean_inc_n(v_toBind_3014_, 3);
v_getEnv_3015_ = lean_ctor_get(v_inst_3010_, 0);
lean_inc(v_getEnv_3015_);
v_toPure_3016_ = lean_ctor_get(v_toApplicative_3013_, 1);
lean_inc_n(v_toPure_3016_, 2);
v___f_3017_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_3011_);
lean_inc_ref(v_inst_3010_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3018_, 0, v_toPure_3016_);
lean_closure_set(v___f_3018_, 1, v_inst_3010_);
lean_closure_set(v___f_3018_, 2, v_structName_3011_);
lean_closure_set(v___f_3018_, 3, v_toBind_3014_);
v___x_3019_ = lean_box(v_relaxed_3012_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_3020_, 0, v_structName_3011_);
lean_closure_set(v___f_3020_, 1, v_toPure_3016_);
lean_closure_set(v___f_3020_, 2, v___f_3017_);
lean_closure_set(v___f_3020_, 3, v_inst_3009_);
lean_closure_set(v___f_3020_, 4, v_inst_3010_);
lean_closure_set(v___f_3020_, 5, v___x_3019_);
lean_closure_set(v___f_3020_, 6, v_toBind_3014_);
lean_closure_set(v___f_3020_, 7, v___f_3018_);
v___x_3021_ = lean_apply_4(v_toBind_3014_, lean_box(0), lean_box(0), v_getEnv_3015_, v___f_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT void l_Lean_computeStructureResolutionOrder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3009_ = stack[0].m_obj;
lean_object* v_inst_3010_ = stack[1].m_obj;
lean_object* v_structName_3011_ = stack[2].m_obj;
uint8_t v_relaxed_3012_ = stack[3].m_num;
lean_object* v_res_3022_;
v_res_3022_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3009_, v_inst_3010_, v_structName_3011_, v_relaxed_3012_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_toBind_3025_, lean_object* v___f_3026_, lean_object* v_parentName_3027_){
_start:
{
uint8_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = 1;
v___x_3029_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3023_, v_inst_3024_, v_parentName_3027_, v___x_3028_);
v___x_3030_ = lean_apply_4(v_toBind_3025_, lean_box(0), lean_box(0), v___x_3029_, v___f_3026_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_structName_3033_, lean_object* v_relaxed_3034_){
_start:
{
uint8_t v_relaxed_boxed_3035_; lean_object* v_res_3036_; 
v_relaxed_boxed_3035_ = lean_unbox(v_relaxed_3034_);
v_res_3036_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3031_, v_inst_3032_, v_structName_3033_, v_relaxed_boxed_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_structName_3039_, lean_object* v_parentNames_3040_, lean_object* v_relaxed_3041_){
_start:
{
uint8_t v_relaxed_boxed_3042_; lean_object* v_res_3043_; 
v_relaxed_boxed_3042_ = lean_unbox(v_relaxed_3041_);
v_res_3043_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_3037_, v_inst_3038_, v_structName_3039_, v_parentNames_3040_, v_relaxed_boxed_3042_);
return v_res_3043_;
}
}
lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_structName_3047_, uint8_t v_relaxed_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3045_, v_inst_3046_, v_structName_3047_, v_relaxed_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT void l_Lean_computeStructureResolutionOrder_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3045_ = stack[1].m_obj;
lean_object* v_inst_3046_ = stack[2].m_obj;
lean_object* v_structName_3047_ = stack[3].m_obj;
uint8_t v_relaxed_3048_ = stack[4].m_num;
lean_object* v_res_3050_;
v_res_3050_ = l_Lean_computeStructureResolutionOrder(lean_box(0), v_inst_3045_, v_inst_3046_, v_structName_3047_, v_relaxed_3048_);
stack->m_obj
 = v_res_3050_;
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_structName_3054_, lean_object* v_relaxed_3055_){
_start:
{
uint8_t v_relaxed_boxed_3056_; lean_object* v_res_3057_; 
v_relaxed_boxed_3056_ = lean_unbox(v_relaxed_3055_);
v_res_3057_ = l_Lean_computeStructureResolutionOrder(v_m_3051_, v_inst_3052_, v_inst_3053_, v_structName_3054_, v_relaxed_boxed_3056_);
return v_res_3057_;
}
}
lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_structName_3061_, lean_object* v_parentNames_3062_, uint8_t v_relaxed_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_3059_, v_inst_3060_, v_structName_3061_, v_parentNames_3062_, v_relaxed_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT void l_Lean_mergeStructureResolutionOrders_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3059_ = stack[1].m_obj;
lean_object* v_inst_3060_ = stack[2].m_obj;
lean_object* v_structName_3061_ = stack[3].m_obj;
lean_object* v_parentNames_3062_ = stack[4].m_obj;
uint8_t v_relaxed_3063_ = stack[5].m_num;
lean_object* v_res_3065_;
v_res_3065_ = l_Lean_mergeStructureResolutionOrders(lean_box(0), v_inst_3059_, v_inst_3060_, v_structName_3061_, v_parentNames_3062_, v_relaxed_3063_);
stack->m_obj
 = v_res_3065_;
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_structName_3069_, lean_object* v_parentNames_3070_, lean_object* v_relaxed_3071_){
_start:
{
uint8_t v_relaxed_boxed_3072_; lean_object* v_res_3073_; 
v_relaxed_boxed_3072_ = lean_unbox(v_relaxed_3071_);
v_res_3073_ = l_Lean_mergeStructureResolutionOrders(v_m_3066_, v_inst_3067_, v_inst_3068_, v_structName_3069_, v_parentNames_3070_, v_relaxed_boxed_3072_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_3074_){
_start:
{
lean_object* v_resolutionOrder_3075_; 
v_resolutionOrder_3075_ = lean_ctor_get(v_x_3074_, 0);
lean_inc_ref(v_resolutionOrder_3075_);
return v_resolutionOrder_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_3076_);
lean_dec_ref(v_x_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_structName_3081_){
_start:
{
lean_object* v_toApplicative_3082_; lean_object* v_toFunctor_3083_; lean_object* v_map_3084_; lean_object* v___f_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_toApplicative_3082_ = lean_ctor_get(v_inst_3079_, 0);
v_toFunctor_3083_ = lean_ctor_get(v_toApplicative_3082_, 0);
v_map_3084_ = lean_ctor_get(v_toFunctor_3083_, 0);
lean_inc(v_map_3084_);
v___f_3085_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_3086_ = 1;
v___x_3087_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3079_, v_inst_3080_, v_structName_3081_, v___x_3086_);
v___x_3088_ = lean_apply_4(v_map_3084_, lean_box(0), lean_box(0), v___f_3085_, v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_structName_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_3090_, v_inst_3091_, v_structName_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_3094_, lean_object* v_structName_3095_, lean_object* v_x_3096_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Array_erase___redArg(v___x_3094_, v_x_3096_, v_structName_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_structName_3100_){
_start:
{
lean_object* v_toApplicative_3101_; lean_object* v_toFunctor_3102_; lean_object* v_map_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_toApplicative_3101_ = lean_ctor_get(v_inst_3098_, 0);
v_toFunctor_3102_ = lean_ctor_get(v_toApplicative_3101_, 0);
v_map_3103_ = lean_ctor_get(v_toFunctor_3102_, 0);
lean_inc(v_map_3103_);
v___x_3104_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_3100_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3105_, 0, v___x_3104_);
lean_closure_set(v___f_3105_, 1, v_structName_3100_);
v___x_3106_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_3098_, v_inst_3099_, v_structName_3100_);
v___x_3107_ = lean_apply_4(v_map_3103_, lean_box(0), lean_box(0), v___f_3105_, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_structName_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_getAllParentStructures___redArg(v_inst_3109_, v_inst_3110_, v_structName_3111_);
return v___x_3112_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedStructureState_default = _init_l_Lean_instInhabitedStructureState_default();
lean_mark_persistent(l_Lean_instInhabitedStructureState_default);
l___private_Lean_Structure_0__Lean_instInhabitedStructureState = _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_instInhabitedStructureState);
res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Structure_0__Lean_structureExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Structure_0__Lean_structureExt);
lean_dec_ref(res);
l_Lean_instInhabitedStructureResolutionState_default = _init_l_Lean_instInhabitedStructureResolutionState_default();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState_default);
l_Lean_instInhabitedStructureResolutionState = _init_l_Lean_instInhabitedStructureResolutionState();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState);
res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_structureResolutionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_structureResolutionExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Structure(builtin);
}
#ifdef __cplusplus
}
#endif
