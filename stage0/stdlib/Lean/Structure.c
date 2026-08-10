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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Array_erase___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Structure"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 99, 41, 156, 128, 75, 220, 191)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(95, 65, 245, 208, 160, 42, 187, 12)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 218, 80, 170, 109, 89, 69, 212)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structureExt"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 77, 126, 118, 66, 118, 83, 124)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_structureExt;
static const lean_array_object l_Lean_instInhabitedStructureDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureDescr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr_default = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_registerStructure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerStructure___closed__0 = (const lean_object*)&l_Lean_registerStructure___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_setStructureParents___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "cannot set structure parents for `"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_setStructureParents___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, structure not defined in current module"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__0_value;
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__1 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__1_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___closed__2;
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
static const lean_string_object l_Lean_getStructureInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Structure"};
static const lean_object* l_Lean_getStructureInfo___closed__0 = (const lean_object*)&l_Lean_getStructureInfo___closed__0_value;
static const lean_string_object l_Lean_getStructureInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.getStructureInfo"};
static const lean_object* l_Lean_getStructureInfo___closed__1 = (const lean_object*)&l_Lean_getStructureInfo___closed__1_value;
static const lean_string_object l_Lean_getStructureInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structure expected"};
static const lean_object* l_Lean_getStructureInfo___closed__2 = (const lean_object*)&l_Lean_getStructureInfo___closed__2_value;
static lean_once_cell_t l_Lean_getStructureInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureInfo___closed__3;
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
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0_value;
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_StructureFieldInfo_lt(lean_object* v_i_u2081_152_, lean_object* v_i_u2082_153_){
_start:
{
lean_object* v_fieldName_154_; lean_object* v_fieldName_155_; uint8_t v___x_156_; 
v_fieldName_154_ = lean_ctor_get(v_i_u2081_152_, 0);
v_fieldName_155_ = lean_ctor_get(v_i_u2082_153_, 0);
v___x_156_ = l_Lean_Name_quickLt(v_fieldName_154_, v_fieldName_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureFieldInfo_lt___boxed(lean_object* v_i_u2081_157_, lean_object* v_i_u2082_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_StructureFieldInfo_lt(v_i_u2081_157_, v_i_u2082_158_);
lean_dec_ref(v_i_u2082_158_);
lean_dec_ref(v_i_u2081_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_StructureInfo_lt(lean_object* v_i_u2081_173_, lean_object* v_i_u2082_174_){
_start:
{
lean_object* v_structName_175_; lean_object* v_structName_176_; uint8_t v___x_177_; 
v_structName_175_ = lean_ctor_get(v_i_u2081_173_, 0);
v_structName_176_ = lean_ctor_get(v_i_u2082_174_, 0);
v___x_177_ = l_Lean_Name_quickLt(v_structName_175_, v_structName_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object* v_i_u2081_178_, lean_object* v_i_u2082_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_StructureInfo_lt(v_i_u2081_178_, v_i_u2082_179_);
lean_dec_ref(v_i_u2082_179_);
lean_dec_ref(v_i_u2081_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object* v_as_182_, lean_object* v_k_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_m_188_; lean_object* v_a_189_; uint8_t v___x_190_; 
v___x_186_ = lean_nat_add(v_x_184_, v_x_185_);
v___x_187_ = lean_unsigned_to_nat(1u);
v_m_188_ = lean_nat_shiftr(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v_a_189_ = lean_array_fget_borrowed(v_as_182_, v_m_188_);
v___x_190_ = l_Lean_StructureFieldInfo_lt(v_a_189_, v_k_183_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
lean_dec(v_x_185_);
v___x_191_ = l_Lean_StructureFieldInfo_lt(v_k_183_, v_a_189_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_dec(v_m_188_);
lean_dec(v_x_184_);
lean_inc(v_a_189_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_a_189_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_eq(v_m_188_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_nat_sub(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v_x_184_);
if (v___x_196_ == 0)
{
v_x_185_ = v___x_195_;
goto _start;
}
else
{
lean_object* v___x_198_; 
lean_dec(v___x_195_);
lean_dec(v_x_184_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_m_188_);
lean_dec(v_x_184_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
lean_dec(v_x_184_);
v___x_200_ = lean_nat_add(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
v___x_201_ = lean_nat_dec_le(v___x_200_, v_x_185_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec(v___x_200_);
lean_dec(v_x_185_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
v_x_184_ = v___x_200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object* v_as_204_, lean_object* v_k_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_204_, v_k_205_, v_x_206_, v_x_207_);
lean_dec_ref(v_k_205_);
lean_dec_ref(v_as_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object* v_info_209_, lean_object* v_i_210_){
_start:
{
lean_object* v_fieldNames_211_; lean_object* v_fieldInfo_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_fieldNames_211_ = lean_ctor_get(v_info_209_, 1);
v_fieldInfo_212_ = lean_ctor_get(v_info_209_, 2);
v___x_213_ = lean_array_get_size(v_fieldNames_211_);
v___x_214_ = lean_nat_dec_lt(v_i_210_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_fieldInfo_212_);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_sub(v___x_217_, v___x_221_);
v___x_223_ = lean_nat_dec_le(v___x_216_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v___x_222_);
return v___x_220_;
}
else
{
lean_object* v_fieldName_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_fieldName_224_ = lean_array_fget_borrowed(v_fieldNames_211_, v_i_210_);
v___x_225_ = lean_box(0);
v___x_226_ = 0;
lean_inc(v_fieldName_224_);
v___x_227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_227_, 0, v_fieldName_224_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_220_);
lean_ctor_set(v___x_227_, 3, v___x_220_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*4, v___x_226_);
v___x_228_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_212_, v___x_227_, v___x_216_, v___x_222_);
lean_dec_ref_known(v___x_227_, 4);
if (lean_obj_tag(v___x_228_) == 0)
{
return v___x_220_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_projFn_233_; lean_object* v___x_235_; 
v_projFn_233_ = lean_ctor_get(v_val_229_, 1);
lean_inc(v_projFn_233_);
lean_dec(v_val_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v_projFn_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_projFn_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object* v_info_238_, lean_object* v_i_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_StructureInfo_getProjFn_x3f(v_info_238_, v_i_239_);
lean_dec(v_i_239_);
lean_dec_ref(v_info_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object* v_as_241_, lean_object* v_k_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_241_, v_k_242_, v_x_243_, v_x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object* v_as_247_, lean_object* v_k_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(v_as_247_, v_k_248_, v_x_249_, v_x_250_, v_x_251_);
lean_dec_ref(v_k_248_);
lean_dec_ref(v_as_247_);
return v_res_252_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__0(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_253_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_instInhabitedStructureState_default;
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t v_sz_262_, size_t v_i_263_, lean_object* v_bs_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_265_ == 0)
{
return v_bs_264_;
}
else
{
lean_object* v_v_266_; lean_object* v_snd_267_; lean_object* v___x_268_; lean_object* v_bs_x27_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v_v_266_ = lean_array_uget_borrowed(v_bs_264_, v_i_263_);
v_snd_267_ = lean_ctor_get(v_v_266_, 1);
lean_inc(v_snd_267_);
v___x_268_ = lean_unsigned_to_nat(0u);
v_bs_x27_269_ = lean_array_uset(v_bs_264_, v_i_263_, v___x_268_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_263_, v___x_270_);
v___x_272_ = lean_array_uset(v_bs_x27_269_, v_i_263_, v_snd_267_);
v_i_263_ = v___x_271_;
v_bs_264_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_274_, lean_object* v_i_275_, lean_object* v_bs_276_){
_start:
{
size_t v_sz_boxed_277_; size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_sz_boxed_277_ = lean_unbox_usize(v_sz_274_);
lean_dec(v_sz_274_);
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_boxed_277_, v_i_boxed_278_, v_bs_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_ps_280_, lean_object* v_k_281_, lean_object* v_v_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_k_281_);
lean_ctor_set(v___x_283_, 1, v_v_282_);
v___x_284_ = lean_array_push(v_ps_280_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_f_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_acc_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_keys_286_);
v___x_291_ = lean_nat_dec_lt(v_i_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_288_);
lean_dec(v_f_285_);
return v_acc_289_;
}
else
{
lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_k_292_ = lean_array_fget_borrowed(v_keys_286_, v_i_288_);
v_v_293_ = lean_array_fget_borrowed(v_vals_287_, v_i_288_);
lean_inc(v_f_285_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v___x_294_ = lean_apply_3(v_f_285_, v_acc_289_, v_k_292_, v_v_293_);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_i_288_, v___x_295_);
lean_dec(v_i_288_);
v_i_288_ = v___x_296_;
v_acc_289_ = v___x_294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_f_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_298_, v_keys_299_, v_vals_300_, v_i_301_, v_acc_302_);
lean_dec_ref(v_vals_300_);
lean_dec_ref(v_keys_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v_es_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_es_307_ = lean_ctor_get(v_x_305_, 0);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_es_307_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec(v_f_304_);
return v_x_306_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_311_ == 0)
{
if (v___x_310_ == 0)
{
lean_dec(v_f_304_);
return v_x_306_;
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_309_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_304_, v_es_307_, v___x_312_, v___x_313_, v_x_306_);
return v___x_314_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_309_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_304_, v_es_307_, v___x_315_, v___x_316_, v_x_306_);
return v___x_317_;
}
}
}
else
{
lean_object* v_ks_318_; lean_object* v_vs_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_ks_318_ = lean_ctor_get(v_x_305_, 0);
v_vs_319_ = lean_ctor_get(v_x_305_, 1);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_304_, v_ks_318_, v_vs_319_, v___x_320_, v_x_306_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_322_, lean_object* v_as_323_, size_t v_i_324_, size_t v_stop_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___y_328_; uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_eq(v_i_324_, v_stop_325_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_array_uget_borrowed(v_as_323_, v_i_324_);
switch(lean_obj_tag(v___x_333_))
{
case 0:
{
lean_object* v_key_334_; lean_object* v_val_335_; lean_object* v___x_336_; 
v_key_334_ = lean_ctor_get(v___x_333_, 0);
v_val_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_f_322_);
lean_inc(v_val_335_);
lean_inc(v_key_334_);
v___x_336_ = lean_apply_3(v_f_322_, v_b_326_, v_key_334_, v_val_335_);
v___y_328_ = v___x_336_;
goto v___jp_327_;
}
case 1:
{
lean_object* v_node_337_; lean_object* v___x_338_; 
v_node_337_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_f_322_);
v___x_338_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_322_, v_node_337_, v_b_326_);
v___y_328_ = v___x_338_;
goto v___jp_327_;
}
default: 
{
v___y_328_ = v_b_326_;
goto v___jp_327_;
}
}
}
else
{
lean_dec(v_f_322_);
return v_b_326_;
}
v___jp_327_:
{
size_t v___x_329_; size_t v___x_330_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_324_, v___x_329_);
v_i_324_ = v___x_330_;
v_b_326_ = v___y_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_339_, v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_347_, v_x_348_, v_x_349_);
lean_dec_ref(v_x_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object* v_f_351_, lean_object* v_x1_352_, lean_object* v_x2_353_, lean_object* v_x3_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_apply_3(v_f_351_, v_x1_352_, v_x2_353_, v_x3_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_356_, lean_object* v_f_357_, lean_object* v_init_358_){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; 
v___f_359_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_359_, 0, v_f_357_);
v___x_360_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_359_, v_map_356_, v_init_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_361_, lean_object* v_f_362_, lean_object* v_init_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_361_, v_f_362_, v_init_363_);
lean_dec_ref(v_map_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_368_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___f_369_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_370_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1));
v___x_371_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_368_, v___f_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_372_);
lean_dec_ref(v_m_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_374_, lean_object* v_pivot_375_, lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_k_378_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_392_, lean_object* v_pivot_393_, lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_392_, v_pivot_393_, v_as_394_, v_i_395_, v_k_396_);
lean_dec_ref(v_pivot_393_);
lean_dec(v_hi_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_398_, lean_object* v_as_399_, lean_object* v_lo_400_, lean_object* v_hi_401_){
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
v___x_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_401_, v_pivot_404_, v___y_403_, v_lo_400_, v_lo_400_);
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
v___x_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_398_, v_snd_407_, v_lo_400_, v_fst_406_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_433_, lean_object* v_as_434_, lean_object* v_lo_435_, lean_object* v_hi_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_433_, v_as_434_, v_lo_435_, v_hi_436_);
lean_dec(v_hi_436_);
lean_dec(v_n_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_438_, lean_object* v_x_439_, lean_object* v_s_440_){
_start:
{
lean_object* v_snd_441_; lean_object* v___x_442_; size_t v_sz_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___x_452_; 
v_snd_441_ = lean_ctor_get(v_s_440_, 1);
v___x_442_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_441_);
v_sz_443_ = lean_array_size(v___x_442_);
v___x_444_ = ((size_t)0ULL);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_443_, v___x_444_, v___x_442_);
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
v___x_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_446_, v___x_445_, v___y_448_, v___y_449_);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_460_, lean_object* v_x_461_, lean_object* v_s_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_460_, v_x_461_, v_s_462_);
lean_dec_ref(v_s_462_);
lean_dec_ref(v_x_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_snd_466_; lean_object* v___x_467_; size_t v_sz_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_snd_466_ = lean_ctor_get(v_x_465_, 1);
v___x_467_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_466_);
v_sz_468_ = lean_array_size(v___x_467_);
v___x_469_ = ((size_t)0ULL);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_468_, v___x_469_, v___x_467_);
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
v___x_478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_471_, v___x_470_, v___y_476_, v___y_476_);
lean_dec(v___y_476_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_471_, v___x_470_, v___y_476_, v___x_474_);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_481_, v_x_482_);
lean_dec_ref(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_n_514_, lean_object* v_k_515_, lean_object* v_v_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_n_514_, v___x_517_, v_k_515_, v_v_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_520_, size_t v_x_521_, size_t v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
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
v___x_563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_555_, v___x_560_, v___x_562_, v_x_523_, v_x_524_);
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
lean_object* v_ks_571_; lean_object* v_vs_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_592_; 
v_ks_571_ = lean_ctor_get(v_x_520_, 0);
v_vs_572_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_592_ == 0)
{
v___x_574_ = v_x_520_;
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_vs_572_);
lean_inc(v_ks_571_);
lean_dec(v_x_520_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_592_;
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
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_ks_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_vs_572_);
v___x_577_ = v_reuseFailAlloc_591_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v_newNode_578_; uint8_t v___y_580_; size_t v___x_586_; uint8_t v___x_587_; 
v_newNode_578_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_577_, v_x_523_, v_x_524_);
v___x_586_ = ((size_t)7ULL);
v___x_587_ = lean_usize_dec_le(v___x_586_, v_x_522_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_578_);
v___x_589_ = lean_unsigned_to_nat(4u);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___y_580_ = v___x_590_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___x_587_;
goto v___jp_579_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v_ks_581_; lean_object* v_vs_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_ks_581_ = lean_ctor_get(v_newNode_578_, 0);
lean_inc_ref(v_ks_581_);
v_vs_582_ = lean_ctor_get(v_newNode_578_, 1);
lean_inc_ref(v_vs_582_);
lean_dec_ref(v_newNode_578_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_522_, v_ks_581_, v_vs_582_, v___x_583_, v___x_584_);
lean_dec_ref(v_vs_582_);
lean_dec_ref(v_ks_581_);
return v___x_585_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_i_596_, lean_object* v_entries_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_keys_594_);
v___x_599_ = lean_nat_dec_lt(v_i_596_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v_i_596_);
return v_entries_597_;
}
else
{
lean_object* v_k_600_; lean_object* v_v_601_; uint64_t v___y_603_; 
v_k_600_ = lean_array_fget_borrowed(v_keys_594_, v_i_596_);
v_v_601_ = lean_array_fget_borrowed(v_vals_595_, v_i_596_);
if (lean_obj_tag(v_k_600_) == 0)
{
uint64_t v___x_614_; 
v___x_614_ = 1723ULL;
v___y_603_ = v___x_614_;
goto v___jp_602_;
}
else
{
uint64_t v_hash_615_; 
v_hash_615_ = lean_ctor_get_uint64(v_k_600_, sizeof(void*)*2);
v___y_603_ = v_hash_615_;
goto v___jp_602_;
}
v___jp_602_:
{
size_t v_h_604_; size_t v___x_605_; lean_object* v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v_h_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_h_604_ = lean_uint64_to_usize(v___y_603_);
v___x_605_ = ((size_t)5ULL);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_sub(v_depth_593_, v___x_607_);
v___x_609_ = lean_usize_mul(v___x_605_, v___x_608_);
v_h_610_ = lean_usize_shift_right(v_h_604_, v___x_609_);
v___x_611_ = lean_nat_add(v_i_596_, v___x_606_);
lean_dec(v_i_596_);
lean_inc(v_v_601_);
lean_inc(v_k_600_);
v___x_612_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_597_, v_h_610_, v_depth_593_, v_k_600_, v_v_601_);
v_i_596_ = v___x_611_;
v_entries_597_ = v___x_612_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_616_, lean_object* v_keys_617_, lean_object* v_vals_618_, lean_object* v_i_619_, lean_object* v_entries_620_){
_start:
{
size_t v_depth_boxed_621_; lean_object* v_res_622_; 
v_depth_boxed_621_ = lean_unbox_usize(v_depth_616_);
lean_dec(v_depth_616_);
v_res_622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_621_, v_keys_617_, v_vals_618_, v_i_619_, v_entries_620_);
lean_dec_ref(v_vals_618_);
lean_dec_ref(v_keys_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
size_t v_x_1822__boxed_628_; size_t v_x_1823__boxed_629_; lean_object* v_res_630_; 
v_x_1822__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_x_1823__boxed_629_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_623_, v_x_1822__boxed_628_, v_x_1823__boxed_629_, v_x_626_, v_x_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
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
v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_631_, v___x_636_, v___x_637_, v_x_632_, v_x_633_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_641_, lean_object* v_x_642_, lean_object* v_e_643_){
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
v___x_649_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_644_, v_structName_648_, v_e_643_);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_661_, lean_object* v_x_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_666_, v_x_667_, v___y_668_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v_x_667_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_701_ = lean_box(0);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_703_; lean_object* v___f_704_; 
v___x_703_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_704_, 0, v___x_703_);
return v___f_704_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_705_; lean_object* v___f_706_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_706_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_706_, 0, v___x_705_);
return v___f_706_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_box(2);
v___f_709_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_710_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_711_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_712_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_713_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_714_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_715_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___f_713_);
lean_ctor_set(v___x_715_, 2, v___f_712_);
lean_ctor_set(v___x_715_, 3, v___f_711_);
lean_ctor_set(v___x_715_, 4, v___f_710_);
lean_ctor_set(v___x_715_, 5, v___f_709_);
lean_ctor_set(v___x_715_, 6, v___x_708_);
lean_ctor_set(v___x_715_, 7, v___x_707_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___f_716_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_717_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___f_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_721_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_724_, lean_object* v_m_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_727_, lean_object* v_m_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_727_, v_m_728_);
lean_dec_ref(v_m_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_730_, lean_object* v_as_731_, lean_object* v_lo_732_, lean_object* v_hi_733_, lean_object* v_w_734_, lean_object* v_hlo_735_, lean_object* v_hhi_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_730_, v_as_731_, v_lo_732_, v_hi_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_738_, lean_object* v_as_739_, lean_object* v_lo_740_, lean_object* v_hi_741_, lean_object* v_w_742_, lean_object* v_hlo_743_, lean_object* v_hhi_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_738_, v_as_739_, v_lo_740_, v_hi_741_, v_w_742_, v_hlo_743_, v_hhi_744_);
lean_dec(v_hi_741_);
lean_dec(v_n_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_747_, v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_751_, lean_object* v_00_u03b2_752_, lean_object* v_map_753_, lean_object* v_f_754_, lean_object* v_init_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_753_, v_f_754_, v_init_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_757_, lean_object* v_00_u03b2_758_, lean_object* v_map_759_, lean_object* v_f_760_, lean_object* v_init_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_757_, v_00_u03b2_758_, v_map_759_, v_f_760_, v_init_761_);
lean_dec_ref(v_map_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_763_, lean_object* v_lo_764_, lean_object* v_hi_765_, lean_object* v_hhi_766_, lean_object* v_pivot_767_, lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_k_770_, lean_object* v_ilo_771_, lean_object* v_ik_772_, lean_object* v_w_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_765_, v_pivot_767_, v_as_768_, v_i_769_, v_k_770_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_775_, lean_object* v_lo_776_, lean_object* v_hi_777_, lean_object* v_hhi_778_, lean_object* v_pivot_779_, lean_object* v_as_780_, lean_object* v_i_781_, lean_object* v_k_782_, lean_object* v_ilo_783_, lean_object* v_ik_784_, lean_object* v_w_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_775_, v_lo_776_, v_hi_777_, v_hhi_778_, v_pivot_779_, v_as_780_, v_i_781_, v_k_782_, v_ilo_783_, v_ik_784_, v_w_785_);
lean_dec_ref(v_pivot_779_);
lean_dec(v_hi_777_);
lean_dec(v_lo_776_);
lean_dec(v_n_775_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, size_t v_x_789_, size_t v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_788_, v_x_789_, v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
size_t v_x_2214__boxed_800_; size_t v_x_2215__boxed_801_; lean_object* v_res_802_; 
v_x_2214__boxed_800_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_x_2215__boxed_801_ = lean_unbox_usize(v_x_797_);
lean_dec(v_x_797_);
v_res_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_794_, v_x_795_, v_x_2214__boxed_800_, v_x_2215__boxed_801_, v_x_798_, v_x_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_803_, lean_object* v_f_804_, lean_object* v_init_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_804_, v_map_803_, v_init_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_807_, lean_object* v_f_808_, lean_object* v_init_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_807_, v_f_808_, v_init_809_);
lean_dec_ref(v_map_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_811_, lean_object* v_00_u03b2_812_, lean_object* v_map_813_, lean_object* v_f_814_, lean_object* v_init_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_814_, v_map_813_, v_init_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_817_, lean_object* v_00_u03b2_818_, lean_object* v_map_819_, lean_object* v_f_820_, lean_object* v_init_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_817_, v_00_u03b2_818_, v_map_819_, v_f_820_, v_init_821_);
lean_dec_ref(v_map_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_823_, lean_object* v_n_824_, lean_object* v_k_825_, lean_object* v_v_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_824_, v_k_825_, v_v_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_828_, size_t v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_heq_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_829_, v_keys_830_, v_vals_831_, v_i_833_, v_entries_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_836_, lean_object* v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
size_t v_depth_boxed_843_; lean_object* v_res_844_; 
v_depth_boxed_843_ = lean_unbox_usize(v_depth_837_);
lean_dec(v_depth_837_);
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_836_, v_depth_boxed_843_, v_keys_838_, v_vals_839_, v_heq_840_, v_i_841_, v_entries_842_);
lean_dec_ref(v_vals_839_);
lean_dec_ref(v_keys_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_845_, lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_f_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_852_, lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_f_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_852_, v_00_u03b1_853_, v_00_u03b2_854_, v_f_855_, v_x_856_, v_x_857_);
lean_dec_ref(v_x_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_860_, v_x_861_, v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_00_u03c3_867_, lean_object* v_f_868_, lean_object* v_as_869_, size_t v_i_870_, size_t v_stop_871_, lean_object* v_b_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_868_, v_as_869_, v_i_870_, v_stop_871_, v_b_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_00_u03c3_876_, lean_object* v_f_877_, lean_object* v_as_878_, lean_object* v_i_879_, lean_object* v_stop_880_, lean_object* v_b_881_){
_start:
{
size_t v_i_boxed_882_; size_t v_stop_boxed_883_; lean_object* v_res_884_; 
v_i_boxed_882_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_stop_boxed_883_ = lean_unbox_usize(v_stop_880_);
lean_dec(v_stop_880_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_874_, v_00_u03b2_875_, v_00_u03c3_876_, v_f_877_, v_as_878_, v_i_boxed_882_, v_stop_boxed_883_, v_b_881_);
lean_dec_ref(v_as_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_885_, lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_f_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_heq_891_, lean_object* v_i_892_, lean_object* v_acc_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_888_, v_keys_889_, v_vals_890_, v_i_892_, v_acc_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_895_, lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_f_898_, lean_object* v_keys_899_, lean_object* v_vals_900_, lean_object* v_heq_901_, lean_object* v_i_902_, lean_object* v_acc_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_895_, v_00_u03b1_896_, v_00_u03b2_897_, v_f_898_, v_keys_899_, v_vals_900_, v_heq_901_, v_i_902_, v_acc_903_);
lean_dec_ref(v_vals_900_);
lean_dec_ref(v_keys_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_912_, size_t v_i_913_, lean_object* v_bs_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_lt(v_i_913_, v_sz_912_);
if (v___x_915_ == 0)
{
return v_bs_914_;
}
else
{
lean_object* v_v_916_; lean_object* v_fieldName_917_; lean_object* v___x_918_; lean_object* v_bs_x27_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v_v_916_ = lean_array_uget_borrowed(v_bs_914_, v_i_913_);
v_fieldName_917_ = lean_ctor_get(v_v_916_, 0);
lean_inc(v_fieldName_917_);
v___x_918_ = lean_unsigned_to_nat(0u);
v_bs_x27_919_ = lean_array_uset(v_bs_914_, v_i_913_, v___x_918_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_i_913_, v___x_920_);
v___x_922_ = lean_array_uset(v_bs_x27_919_, v_i_913_, v_fieldName_917_);
v_i_913_ = v___x_921_;
v_bs_914_ = v___x_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_bs_926_){
_start:
{
size_t v_sz_boxed_927_; size_t v_i_boxed_928_; lean_object* v_res_929_; 
v_sz_boxed_927_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_928_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_927_, v_i_boxed_928_, v_bs_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object* v_hi_930_, lean_object* v_pivot_931_, lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_k_934_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_nat_dec_lt(v_k_934_, v_hi_930_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_k_934_);
v___x_936_ = lean_array_fswap(v_as_932_, v_i_933_, v_hi_930_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_i_933_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_array_fget_borrowed(v_as_932_, v_k_934_);
v___x_939_ = l_Lean_StructureFieldInfo_lt(v___x_938_, v_pivot_931_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_k_934_, v___x_940_);
lean_dec(v_k_934_);
v_k_934_ = v___x_941_;
goto _start;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_array_fswap(v_as_932_, v_i_933_, v_k_934_);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_i_933_, v___x_944_);
lean_dec(v_i_933_);
v___x_946_ = lean_nat_add(v_k_934_, v___x_944_);
lean_dec(v_k_934_);
v_as_932_ = v___x_943_;
v_i_933_ = v___x_945_;
v_k_934_ = v___x_946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object* v_hi_948_, lean_object* v_pivot_949_, lean_object* v_as_950_, lean_object* v_i_951_, lean_object* v_k_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_948_, v_pivot_949_, v_as_950_, v_i_951_, v_k_952_);
lean_dec_ref(v_pivot_949_);
lean_dec(v_hi_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_n_954_, lean_object* v_as_955_, lean_object* v_lo_956_, lean_object* v_hi_957_){
_start:
{
lean_object* v___y_959_; uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_lt(v_lo_956_, v_hi_957_);
if (v___x_969_ == 0)
{
lean_dec(v_lo_956_);
return v_as_955_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_mid_972_; lean_object* v___y_974_; lean_object* v___y_980_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_970_ = lean_nat_add(v_lo_956_, v_hi_957_);
v___x_971_ = lean_unsigned_to_nat(1u);
v_mid_972_ = lean_nat_shiftr(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
v___x_985_ = lean_array_fget_borrowed(v_as_955_, v_mid_972_);
v___x_986_ = lean_array_fget_borrowed(v_as_955_, v_lo_956_);
v___x_987_ = l_Lean_StructureFieldInfo_lt(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
v___y_980_ = v_as_955_;
goto v___jp_979_;
}
else
{
lean_object* v___x_988_; 
v___x_988_ = lean_array_fswap(v_as_955_, v_lo_956_, v_mid_972_);
v___y_980_ = v___x_988_;
goto v___jp_979_;
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_array_fget_borrowed(v___y_974_, v_mid_972_);
v___x_976_ = lean_array_fget_borrowed(v___y_974_, v_hi_957_);
v___x_977_ = l_Lean_StructureFieldInfo_lt(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_dec(v_mid_972_);
v___y_959_ = v___y_974_;
goto v___jp_958_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_array_fswap(v___y_974_, v_mid_972_, v_hi_957_);
lean_dec(v_mid_972_);
v___y_959_ = v___x_978_;
goto v___jp_958_;
}
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = lean_array_fget_borrowed(v___y_980_, v_hi_957_);
v___x_982_ = lean_array_fget_borrowed(v___y_980_, v_lo_956_);
v___x_983_ = l_Lean_StructureFieldInfo_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
v___y_974_ = v___y_980_;
goto v___jp_973_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = lean_array_fswap(v___y_980_, v_lo_956_, v_hi_957_);
v___y_974_ = v___x_984_;
goto v___jp_973_;
}
}
}
v___jp_958_:
{
lean_object* v_pivot_960_; lean_object* v___x_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; uint8_t v___x_964_; 
v_pivot_960_ = lean_array_fget(v___y_959_, v_hi_957_);
lean_inc_n(v_lo_956_, 2);
v___x_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_957_, v_pivot_960_, v___y_959_, v_lo_956_, v_lo_956_);
lean_dec(v_pivot_960_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
v___x_964_ = lean_nat_dec_le(v_hi_957_, v_fst_962_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_954_, v_snd_963_, v_lo_956_, v_fst_962_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_fst_962_, v___x_966_);
lean_dec(v_fst_962_);
v_as_955_ = v___x_965_;
v_lo_956_ = v___x_967_;
goto _start;
}
else
{
lean_dec(v_fst_962_);
lean_dec(v_lo_956_);
return v_snd_963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_n_989_, lean_object* v_as_990_, lean_object* v_lo_991_, lean_object* v_hi_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_989_, v_as_990_, v_lo_991_, v_hi_992_);
lean_dec(v_hi_992_);
lean_dec(v_n_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_996_, lean_object* v_e_997_){
_start:
{
lean_object* v_structName_998_; lean_object* v_fields_999_; lean_object* v___x_1000_; size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___y_1005_; lean_object* v___x_1012_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_structName_998_ = lean_ctor_get(v_e_997_, 0);
lean_inc(v_structName_998_);
v_fields_999_ = lean_ctor_get(v_e_997_, 1);
lean_inc_ref_n(v_fields_999_, 2);
lean_dec_ref(v_e_997_);
v___x_1000_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_1001_ = lean_array_size(v_fields_999_);
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_1001_, v___x_1002_, v_fields_999_);
v___x_1012_ = lean_array_get_size(v_fields_999_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_nat_dec_eq(v___x_1012_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___y_1022_; uint8_t v___x_1024_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_sub(v___x_1012_, v___x_1019_);
v___x_1024_ = lean_nat_dec_le(v___x_1017_, v___x_1020_);
if (v___x_1024_ == 0)
{
lean_inc(v___x_1020_);
v___y_1022_ = v___x_1020_;
goto v___jp_1021_;
}
else
{
v___y_1022_ = v___x_1017_;
goto v___jp_1021_;
}
v___jp_1021_:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_nat_dec_le(v___y_1022_, v___x_1020_);
if (v___x_1023_ == 0)
{
lean_dec(v___x_1020_);
lean_inc(v___y_1022_);
v___y_1014_ = v___y_1022_;
v___y_1015_ = v___y_1022_;
goto v___jp_1013_;
}
else
{
v___y_1014_ = v___y_1022_;
v___y_1015_ = v___x_1020_;
goto v___jp_1013_;
}
}
}
else
{
v___y_1005_ = v_fields_999_;
goto v___jp_1004_;
}
v___jp_1004_:
{
lean_object* v_toEnvExtension_1006_; lean_object* v_asyncMode_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_toEnvExtension_1006_ = lean_ctor_get(v___x_1000_, 0);
v_asyncMode_1007_ = lean_ctor_get(v_toEnvExtension_1006_, 2);
v___x_1008_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_1009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1009_, 0, v_structName_998_);
lean_ctor_set(v___x_1009_, 1, v___x_1003_);
lean_ctor_set(v___x_1009_, 2, v___y_1005_);
lean_ctor_set(v___x_1009_, 3, v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1000_, v_env_996_, v___x_1009_, v_asyncMode_1007_, v___x_1010_);
return v___x_1011_;
}
v___jp_1013_:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_1012_, v_fields_999_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
v___y_1005_ = v___x_1016_;
goto v___jp_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_1025_, lean_object* v_as_1026_, lean_object* v_lo_1027_, lean_object* v_hi_1028_, lean_object* v_w_1029_, lean_object* v_hlo_1030_, lean_object* v_hhi_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_1025_, v_as_1026_, v_lo_1027_, v_hi_1028_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_1033_, lean_object* v_as_1034_, lean_object* v_lo_1035_, lean_object* v_hi_1036_, lean_object* v_w_1037_, lean_object* v_hlo_1038_, lean_object* v_hhi_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_1033_, v_as_1034_, v_lo_1035_, v_hi_1036_, v_w_1037_, v_hlo_1038_, v_hhi_1039_);
lean_dec(v_hi_1036_);
lean_dec(v_n_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object* v_n_1041_, lean_object* v_lo_1042_, lean_object* v_hi_1043_, lean_object* v_hhi_1044_, lean_object* v_pivot_1045_, lean_object* v_as_1046_, lean_object* v_i_1047_, lean_object* v_k_1048_, lean_object* v_ilo_1049_, lean_object* v_ik_1050_, lean_object* v_w_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_1043_, v_pivot_1045_, v_as_1046_, v_i_1047_, v_k_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object* v_n_1053_, lean_object* v_lo_1054_, lean_object* v_hi_1055_, lean_object* v_hhi_1056_, lean_object* v_pivot_1057_, lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_k_1060_, lean_object* v_ilo_1061_, lean_object* v_ik_1062_, lean_object* v_w_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_1053_, v_lo_1054_, v_hi_1055_, v_hhi_1056_, v_pivot_1057_, v_as_1058_, v_i_1059_, v_k_1060_, v_ilo_1061_, v_ik_1062_, v_w_1063_);
lean_dec_ref(v_pivot_1057_);
lean_dec(v_hi_1055_);
lean_dec(v_lo_1054_);
lean_dec(v_n_1053_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_1065_, lean_object* v_parentInfo_1066_, lean_object* v___x_1067_, lean_object* v_asyncMode_1068_, lean_object* v___x_1069_, lean_object* v_env_1070_){
_start:
{
lean_object* v_structName_1071_; lean_object* v_fieldNames_1072_; lean_object* v_fieldInfo_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_structName_1071_ = lean_ctor_get(v_val_1065_, 0);
v_fieldNames_1072_ = lean_ctor_get(v_val_1065_, 1);
v_fieldInfo_1073_ = lean_ctor_get(v_val_1065_, 2);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_val_1065_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_val_1065_, 3);
lean_dec(v_unused_1082_);
v___x_1075_ = v_val_1065_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_fieldInfo_1073_);
lean_inc(v_fieldNames_1072_);
lean_inc(v_structName_1071_);
lean_dec(v_val_1065_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 3, v_parentInfo_1066_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_structName_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_fieldNames_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_fieldInfo_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_parentInfo_1066_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1067_, v_env_1070_, v___x_1078_, v_asyncMode_1068_, v___x_1069_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_1083_, lean_object* v_parentInfo_1084_, lean_object* v___x_1085_, lean_object* v_asyncMode_1086_, lean_object* v___x_1087_, lean_object* v_env_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_setStructureParents___redArg___lam__0(v_val_1083_, v_parentInfo_1084_, v___x_1085_, v_asyncMode_1086_, v___x_1087_, v_env_1088_);
lean_dec(v_asyncMode_1086_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v_structName_1099_, lean_object* v_parentInfo_1100_, lean_object* v_modifyEnv_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_____do__lift_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v_toEnvExtension_1106_; lean_object* v_asyncMode_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_snd_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1126_; 
v___x_1105_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1106_ = lean_ctor_get(v___x_1105_, 0);
v_asyncMode_1107_ = lean_ctor_get(v_toEnvExtension_1106_, 2);
v___x_1108_ = lean_box(0);
v___x_1109_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1096_, v___x_1105_, v_____do__lift_1104_, v_asyncMode_1107_, v___x_1108_);
v_snd_1110_ = lean_ctor_get(v___x_1109_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1127_);
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1126_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_snd_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1126_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; 
lean_inc(v_structName_1099_);
v___x_1114_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1097_, v___x_1098_, v_snd_1110_, v_structName_1099_);
lean_dec(v_snd_1110_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; 
lean_del_object(v___x_1112_);
lean_dec_ref(v_inst_1103_);
lean_dec_ref(v_inst_1102_);
lean_dec(v_structName_1099_);
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc(v_asyncMode_1107_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1116_, 0, v_val_1115_);
lean_closure_set(v___f_1116_, 1, v_parentInfo_1100_);
lean_closure_set(v___f_1116_, 2, v___x_1105_);
lean_closure_set(v___f_1116_, 3, v_asyncMode_1107_);
lean_closure_set(v___f_1116_, 4, v___x_1108_);
v___x_1117_ = lean_apply_1(v_modifyEnv_1101_, v___f_1116_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec(v___x_1114_);
lean_dec(v_modifyEnv_1101_);
lean_dec_ref(v_parentInfo_1100_);
v___x_1118_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_1119_ = l_Lean_MessageData_ofName(v_structName_1099_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 7);
lean_ctor_set(v___x_1112_, 1, v___x_1119_);
lean_ctor_set(v___x_1112_, 0, v___x_1118_);
v___x_1121_ = v___x_1112_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_throwError___redArg(v_inst_1102_, v_inst_1103_, v___x_1123_);
return v___x_1124_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_instInhabitedStructureState_default;
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_structName_1136_, lean_object* v_parentInfo_1137_){
_start:
{
lean_object* v_toBind_1138_; lean_object* v_getEnv_1139_; lean_object* v_modifyEnv_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; 
v_toBind_1138_ = lean_ctor_get(v_inst_1133_, 1);
lean_inc(v_toBind_1138_);
v_getEnv_1139_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc(v_getEnv_1139_);
v_modifyEnv_1140_ = lean_ctor_get(v_inst_1134_, 1);
lean_inc(v_modifyEnv_1140_);
lean_dec_ref(v_inst_1134_);
v___x_1141_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1142_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1143_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1144_, 0, v___x_1143_);
lean_closure_set(v___f_1144_, 1, v___x_1141_);
lean_closure_set(v___f_1144_, 2, v___x_1142_);
lean_closure_set(v___f_1144_, 3, v_structName_1136_);
lean_closure_set(v___f_1144_, 4, v_parentInfo_1137_);
lean_closure_set(v___f_1144_, 5, v_modifyEnv_1140_);
lean_closure_set(v___f_1144_, 6, v_inst_1133_);
lean_closure_set(v___f_1144_, 7, v_inst_1135_);
v___x_1145_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v_getEnv_1139_, v___f_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_structName_1150_, lean_object* v_parentInfo_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_setStructureParents___redArg(v_inst_1147_, v_inst_1148_, v_inst_1149_, v_structName_1150_, v_parentInfo_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1153_, lean_object* v_k_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_m_1159_; lean_object* v_a_1160_; uint8_t v___x_1161_; 
v___x_1157_ = lean_nat_add(v_x_1155_, v_x_1156_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v_m_1159_ = lean_nat_shiftr(v___x_1157_, v___x_1158_);
lean_dec(v___x_1157_);
v_a_1160_ = lean_array_fget_borrowed(v_as_1153_, v_m_1159_);
v___x_1161_ = l_Lean_StructureInfo_lt(v_a_1160_, v_k_1154_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
lean_dec(v_x_1156_);
v___x_1162_ = l_Lean_StructureInfo_lt(v_k_1154_, v_a_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec(v_m_1159_);
lean_dec(v_x_1155_);
lean_inc(v_a_1160_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_a_1160_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = lean_nat_dec_eq(v_m_1159_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_nat_sub(v_m_1159_, v___x_1158_);
lean_dec(v_m_1159_);
v___x_1167_ = lean_nat_dec_lt(v___x_1166_, v_x_1155_);
if (v___x_1167_ == 0)
{
v_x_1156_ = v___x_1166_;
goto _start;
}
else
{
lean_object* v___x_1169_; 
lean_dec(v___x_1166_);
lean_dec(v_x_1155_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; 
lean_dec(v_m_1159_);
lean_dec(v_x_1155_);
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
}
}
else
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
lean_dec(v_x_1155_);
v___x_1171_ = lean_nat_add(v_m_1159_, v___x_1158_);
lean_dec(v_m_1159_);
v___x_1172_ = lean_nat_dec_le(v___x_1171_, v_x_1156_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v___x_1171_);
lean_dec(v_x_1156_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
v_x_1155_ = v___x_1171_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1175_, lean_object* v_k_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1175_, v_k_1176_, v_x_1177_, v_x_1178_);
lean_dec_ref(v_k_1176_);
lean_dec_ref(v_as_1175_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1180_, lean_object* v_vals_1181_, lean_object* v_i_1182_, lean_object* v_k_1183_){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_array_get_size(v_keys_1180_);
v___x_1185_ = lean_nat_dec_lt(v_i_1182_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec(v_i_1182_);
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
else
{
lean_object* v_k_x27_1187_; uint8_t v___x_1188_; 
v_k_x27_1187_ = lean_array_fget_borrowed(v_keys_1180_, v_i_1182_);
v___x_1188_ = lean_name_eq(v_k_1183_, v_k_x27_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_add(v_i_1182_, v___x_1189_);
lean_dec(v_i_1182_);
v_i_1182_ = v___x_1190_;
goto _start;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_array_fget_borrowed(v_vals_1181_, v_i_1182_);
lean_dec(v_i_1182_);
lean_inc(v___x_1192_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1194_, lean_object* v_vals_1195_, lean_object* v_i_1196_, lean_object* v_k_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1194_, v_vals_1195_, v_i_1196_, v_k_1197_);
lean_dec(v_k_1197_);
lean_dec_ref(v_vals_1195_);
lean_dec_ref(v_keys_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1199_, size_t v_x_1200_, lean_object* v_x_1201_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v_es_1202_; lean_object* v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v_j_1206_; lean_object* v___x_1207_; 
v_es_1202_ = lean_ctor_get(v_x_1199_, 0);
v___x_1203_ = lean_box(2);
v___x_1204_ = ((size_t)31ULL);
v___x_1205_ = lean_usize_land(v_x_1200_, v___x_1204_);
v_j_1206_ = lean_usize_to_nat(v___x_1205_);
v___x_1207_ = lean_array_get_borrowed(v___x_1203_, v_es_1202_, v_j_1206_);
lean_dec(v_j_1206_);
switch(lean_obj_tag(v___x_1207_))
{
case 0:
{
lean_object* v_key_1208_; lean_object* v_val_1209_; uint8_t v___x_1210_; 
v_key_1208_ = lean_ctor_get(v___x_1207_, 0);
v_val_1209_ = lean_ctor_get(v___x_1207_, 1);
v___x_1210_ = lean_name_eq(v_x_1201_, v_key_1208_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_box(0);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; 
lean_inc(v_val_1209_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_val_1209_);
return v___x_1212_;
}
}
case 1:
{
lean_object* v_node_1213_; size_t v___x_1214_; size_t v___x_1215_; 
v_node_1213_ = lean_ctor_get(v___x_1207_, 0);
v___x_1214_ = ((size_t)5ULL);
v___x_1215_ = lean_usize_shift_right(v_x_1200_, v___x_1214_);
v_x_1199_ = v_node_1213_;
v_x_1200_ = v___x_1215_;
goto _start;
}
default: 
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_box(0);
return v___x_1217_;
}
}
}
else
{
lean_object* v_ks_1218_; lean_object* v_vs_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_ks_1218_ = lean_ctor_get(v_x_1199_, 0);
v_vs_1219_ = lean_ctor_get(v_x_1199_, 1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1218_, v_vs_1219_, v___x_1220_, v_x_1201_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
size_t v_x_384__boxed_1225_; lean_object* v_res_1226_; 
v_x_384__boxed_1225_ = lean_unbox_usize(v_x_1223_);
lean_dec(v_x_1223_);
v_res_1226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1222_, v_x_384__boxed_1225_, v_x_1224_);
lean_dec(v_x_1224_);
lean_dec_ref(v_x_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
uint64_t v___y_1230_; 
if (lean_obj_tag(v_x_1228_) == 0)
{
uint64_t v___x_1233_; 
v___x_1233_ = 1723ULL;
v___y_1230_ = v___x_1233_;
goto v___jp_1229_;
}
else
{
uint64_t v_hash_1234_; 
v_hash_1234_ = lean_ctor_get_uint64(v_x_1228_, sizeof(void*)*2);
v___y_1230_ = v_hash_1234_;
goto v___jp_1229_;
}
v___jp_1229_:
{
size_t v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_uint64_to_usize(v___y_1230_);
v___x_1232_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1227_, v___x_1231_, v_x_1228_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1235_, v_x_1236_);
lean_dec(v_x_1236_);
lean_dec_ref(v_x_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1238_, lean_object* v_structName_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1241_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1238_, v_structName_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; lean_object* v_toEnvExtension_1243_; lean_object* v_asyncMode_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; 
v___x_1242_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1243_ = lean_ctor_get(v___x_1242_, 0);
v_asyncMode_1244_ = lean_ctor_get(v_toEnvExtension_1243_, 2);
v___x_1245_ = lean_box(0);
v___x_1246_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1240_, v___x_1242_, v_env_1238_, v_asyncMode_1244_, v___x_1245_);
v_snd_1247_ = lean_ctor_get(v___x_1246_, 1);
lean_inc(v_snd_1247_);
lean_dec(v___x_1246_);
v___x_1248_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1247_, v_structName_1239_);
lean_dec(v_structName_1239_);
lean_dec(v_snd_1247_);
return v___x_1248_;
}
else
{
lean_object* v_val_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_val_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1250_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1251_ = 0;
v___x_1252_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1240_, v___x_1250_, v_env_1238_, v_val_1249_, v___x_1251_);
lean_dec(v_val_1249_);
lean_dec_ref(v_env_1238_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_array_get_size(v___x_1252_);
v___x_1255_ = lean_nat_dec_lt(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___x_1252_);
lean_dec(v_structName_1239_);
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_sub(v___x_1254_, v___x_1257_);
v___x_1259_ = lean_nat_dec_le(v___x_1253_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec(v___x_1258_);
lean_dec_ref(v___x_1252_);
lean_dec(v_structName_1239_);
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1262_, 0, v_structName_1239_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
v___x_1263_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1252_, v___x_1262_, v___x_1253_, v___x_1258_);
lean_dec_ref_known(v___x_1262_, 4);
lean_dec_ref(v___x_1252_);
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1268_, v_x_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec_ref(v_x_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1272_, lean_object* v_k_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1272_, v_k_1273_, v_x_1274_, v_x_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1278_, lean_object* v_k_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1278_, v_k_1279_, v_x_1280_, v_x_1281_, v_x_1282_);
lean_dec_ref(v_k_1279_);
lean_dec_ref(v_as_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, size_t v_x_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1285_, v_x_1286_, v_x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
size_t v_x_515__boxed_1293_; lean_object* v_res_1294_; 
v_x_515__boxed_1293_ = lean_unbox_usize(v_x_1291_);
lean_dec(v_x_1291_);
v_res_1294_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1289_, v_x_1290_, v_x_515__boxed_1293_, v_x_1292_);
lean_dec(v_x_1292_);
lean_dec_ref(v_x_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_k_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1296_, v_vals_1297_, v_i_1299_, v_k_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_keys_1303_, lean_object* v_vals_1304_, lean_object* v_heq_1305_, lean_object* v_i_1306_, lean_object* v_k_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1302_, v_keys_1303_, v_vals_1304_, v_heq_1305_, v_i_1306_, v_k_1307_);
lean_dec(v_k_1307_);
lean_dec_ref(v_vals_1304_);
lean_dec_ref(v_keys_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1311_ = lean_panic_fn_borrowed(v___x_1310_, v_msg_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1315_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1316_ = lean_unsigned_to_nat(4u);
v___x_1317_ = lean_unsigned_to_nat(139u);
v___x_1318_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1319_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1320_ = l_mkPanicMessageWithDecl(v___x_1319_, v___x_1318_, v___x_1317_, v___x_1316_, v___x_1315_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1321_, lean_object* v_structName_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_getStructureInfo_x3f(v_env_1321_, v_structName_1322_);
if (lean_obj_tag(v___x_1323_) == 1)
{
lean_object* v_val_1324_; 
v_val_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___x_1323_, 1);
return v_val_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v___x_1323_);
v___x_1325_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1326_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1325_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1329_ = lean_panic_fn_borrowed(v___x_1328_, v_msg_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1332_ = lean_unsigned_to_nat(9u);
v___x_1333_ = lean_unsigned_to_nat(154u);
v___x_1334_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1335_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1336_ = l_mkPanicMessageWithDecl(v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_, v___x_1331_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1339_ = lean_unsigned_to_nat(11u);
v___x_1340_ = lean_unsigned_to_nat(153u);
v___x_1341_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1342_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1343_ = l_mkPanicMessageWithDecl(v___x_1342_, v___x_1341_, v___x_1340_, v___x_1339_, v___x_1338_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1344_, lean_object* v_constName_1345_){
_start:
{
uint8_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = 0;
lean_inc_ref(v_env_1344_);
v___x_1353_ = l_Lean_Environment_find_x3f(v_env_1344_, v_constName_1345_, v___x_1352_);
if (lean_obj_tag(v___x_1353_) == 1)
{
lean_object* v_val_1354_; 
v_val_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v___x_1353_, 1);
if (lean_obj_tag(v_val_1354_) == 5)
{
lean_object* v_val_1355_; lean_object* v_ctors_1356_; 
v_val_1355_ = lean_ctor_get(v_val_1354_, 0);
lean_inc_ref(v_val_1355_);
lean_dec_ref_known(v_val_1354_, 1);
v_ctors_1356_ = lean_ctor_get(v_val_1355_, 4);
lean_inc(v_ctors_1356_);
lean_dec_ref(v_val_1355_);
if (lean_obj_tag(v_ctors_1356_) == 1)
{
lean_object* v_tail_1357_; 
v_tail_1357_ = lean_ctor_get(v_ctors_1356_, 1);
if (lean_obj_tag(v_tail_1357_) == 0)
{
lean_object* v_head_1358_; lean_object* v___x_1359_; 
v_head_1358_ = lean_ctor_get(v_ctors_1356_, 0);
lean_inc(v_head_1358_);
lean_dec_ref_known(v_ctors_1356_, 2);
v___x_1359_ = l_Lean_Environment_find_x3f(v_env_1344_, v_head_1358_, v___x_1352_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v_val_1360_; 
v_val_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v___x_1359_, 1);
if (lean_obj_tag(v_val_1360_) == 6)
{
lean_object* v_val_1361_; 
v_val_1361_ = lean_ctor_get(v_val_1360_, 0);
lean_inc_ref(v_val_1361_);
lean_dec_ref_known(v_val_1360_, 1);
return v_val_1361_;
}
else
{
lean_dec(v_val_1360_);
goto v___jp_1349_;
}
}
else
{
lean_dec(v___x_1359_);
goto v___jp_1349_;
}
}
else
{
lean_dec_ref_known(v_ctors_1356_, 2);
lean_dec_ref(v_env_1344_);
goto v___jp_1346_;
}
}
else
{
lean_dec(v_ctors_1356_);
lean_dec_ref(v_env_1344_);
goto v___jp_1346_;
}
}
else
{
lean_dec(v_val_1354_);
lean_dec_ref(v_env_1344_);
goto v___jp_1346_;
}
}
else
{
lean_dec(v___x_1353_);
lean_dec_ref(v_env_1344_);
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1348_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1347_);
return v___x_1348_;
}
v___jp_1349_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1351_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1350_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1362_, lean_object* v_structName_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v_fieldNames_1365_; 
v___x_1364_ = l_Lean_getStructureInfo(v_env_1362_, v_structName_1363_);
v_fieldNames_1365_ = lean_ctor_get(v___x_1364_, 1);
lean_inc_ref(v_fieldNames_1365_);
lean_dec_ref(v___x_1364_);
return v_fieldNames_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1366_, lean_object* v_structName_1367_, lean_object* v_fieldName_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_getStructureInfo_x3f(v_env_1366_, v_structName_1367_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v_val_1370_; lean_object* v_fieldInfo_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_fieldInfo_1371_ = lean_ctor_get(v_val_1370_, 2);
lean_inc_ref(v_fieldInfo_1371_);
lean_dec(v_val_1370_);
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = lean_array_get_size(v_fieldInfo_1371_);
v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec_ref(v_fieldInfo_1371_);
lean_dec(v_fieldName_1368_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_sub(v___x_1373_, v___x_1376_);
v___x_1378_ = lean_nat_dec_le(v___x_1372_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v___x_1377_);
lean_dec_ref(v_fieldInfo_1371_);
lean_dec(v_fieldName_1368_);
v___x_1379_ = lean_box(0);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_box(0);
v___x_1382_ = 0;
v___x_1383_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1383_, 0, v_fieldName_1368_);
lean_ctor_set(v___x_1383_, 1, v___x_1380_);
lean_ctor_set(v___x_1383_, 2, v___x_1381_);
lean_ctor_set(v___x_1383_, 3, v___x_1381_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*4, v___x_1382_);
v___x_1384_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1371_, v___x_1383_, v___x_1372_, v___x_1377_);
lean_dec_ref_known(v___x_1383_, 4);
lean_dec_ref(v_fieldInfo_1371_);
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1385_; 
lean_dec(v___x_1369_);
lean_dec(v_fieldName_1368_);
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1386_, lean_object* v_structName_1387_, lean_object* v_fieldName_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_getFieldInfo_x3f(v_env_1386_, v_structName_1387_, v_fieldName_1388_);
if (lean_obj_tag(v___x_1389_) == 1)
{
lean_object* v_val_1390_; lean_object* v_subobject_x3f_1391_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_subobject_x3f_1391_ = lean_ctor_get(v_val_1390_, 2);
lean_inc(v_subobject_x3f_1391_);
lean_dec(v_val_1390_);
return v_subobject_x3f_1391_;
}
else
{
lean_object* v___x_1392_; 
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1393_, lean_object* v_structName_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v_parentInfo_1396_; 
v___x_1395_ = l_Lean_getStructureInfo(v_env_1393_, v_structName_1394_);
v_parentInfo_1396_ = lean_ctor_get(v___x_1395_, 3);
lean_inc_ref(v_parentInfo_1396_);
lean_dec_ref(v___x_1395_);
return v_parentInfo_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1397_, lean_object* v_structName_1398_, lean_object* v_as_1399_, size_t v_i_1400_, size_t v_stop_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v___y_1404_; uint8_t v___x_1408_; 
v___x_1408_ = lean_usize_dec_eq(v_i_1400_, v_stop_1401_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_array_uget_borrowed(v_as_1399_, v_i_1400_);
lean_inc(v___x_1409_);
lean_inc(v_structName_1398_);
lean_inc_ref(v_env_1397_);
v___x_1410_ = l_Lean_isSubobjectField_x3f(v_env_1397_, v_structName_1398_, v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
v___y_1404_ = v_b_1402_;
goto v___jp_1403_;
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1412_; 
v_val_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = lean_array_push(v_b_1402_, v_val_1411_);
v___y_1404_ = v___x_1412_;
goto v___jp_1403_;
}
}
else
{
lean_dec(v_structName_1398_);
lean_dec_ref(v_env_1397_);
return v_b_1402_;
}
v___jp_1403_:
{
size_t v___x_1405_; size_t v___x_1406_; 
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_add(v_i_1400_, v___x_1405_);
v_i_1400_ = v___x_1406_;
v_b_1402_ = v___y_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1413_, lean_object* v_structName_1414_, lean_object* v_as_1415_, lean_object* v_i_1416_, lean_object* v_stop_1417_, lean_object* v_b_1418_){
_start:
{
size_t v_i_boxed_1419_; size_t v_stop_boxed_1420_; lean_object* v_res_1421_; 
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_stop_boxed_1420_ = lean_unbox_usize(v_stop_1417_);
lean_dec(v_stop_1417_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1413_, v_structName_1414_, v_as_1415_, v_i_boxed_1419_, v_stop_boxed_1420_, v_b_1418_);
lean_dec_ref(v_as_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1422_, lean_object* v_structName_1423_, lean_object* v_as_1424_, lean_object* v_start_1425_, lean_object* v_stop_1426_){
_start:
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1428_ = lean_nat_dec_lt(v_start_1425_, v_stop_1426_);
if (v___x_1428_ == 0)
{
lean_dec(v_structName_1423_);
lean_dec_ref(v_env_1422_);
return v___x_1427_;
}
else
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_get_size(v_as_1424_);
v___x_1430_ = lean_nat_dec_le(v_stop_1426_, v___x_1429_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_lt(v_start_1425_, v___x_1429_);
if (v___x_1431_ == 0)
{
lean_dec(v_structName_1423_);
lean_dec_ref(v_env_1422_);
return v___x_1427_;
}
else
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_usize_of_nat(v_start_1425_);
v___x_1433_ = lean_usize_of_nat(v___x_1429_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1422_, v_structName_1423_, v_as_1424_, v___x_1432_, v___x_1433_, v___x_1427_);
return v___x_1434_;
}
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_usize_of_nat(v_start_1425_);
v___x_1436_ = lean_usize_of_nat(v_stop_1426_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1422_, v_structName_1423_, v_as_1424_, v___x_1435_, v___x_1436_, v___x_1427_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1438_, lean_object* v_structName_1439_, lean_object* v_as_1440_, lean_object* v_start_1441_, lean_object* v_stop_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1438_, v_structName_1439_, v_as_1440_, v_start_1441_, v_stop_1442_);
lean_dec(v_stop_1442_);
lean_dec(v_start_1441_);
lean_dec_ref(v_as_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1444_, lean_object* v_structName_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc(v_structName_1445_);
lean_inc_ref(v_env_1444_);
v___x_1446_ = l_Lean_getStructureFields(v_env_1444_, v_structName_1445_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_array_get_size(v___x_1446_);
v___x_1449_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1444_, v_structName_1445_, v___x_1446_, v___x_1447_, v___x_1448_);
lean_dec_ref(v___x_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1450_, lean_object* v_as_1451_, size_t v_i_1452_, size_t v_stop_1453_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_eq(v_i_1452_, v_stop_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_array_uget_borrowed(v_as_1451_, v_i_1452_);
v___x_1456_ = lean_name_eq(v_a_1450_, v___x_1455_);
if (v___x_1456_ == 0)
{
size_t v___x_1457_; size_t v___x_1458_; 
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1452_, v___x_1457_);
v_i_1452_ = v___x_1458_;
goto _start;
}
else
{
return v___x_1456_;
}
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = 0;
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1461_, lean_object* v_as_1462_, lean_object* v_i_1463_, lean_object* v_stop_1464_){
_start:
{
size_t v_i_boxed_1465_; size_t v_stop_boxed_1466_; uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_i_boxed_1465_ = lean_unbox_usize(v_i_1463_);
lean_dec(v_i_1463_);
v_stop_boxed_1466_ = lean_unbox_usize(v_stop_1464_);
lean_dec(v_stop_1464_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1461_, v_as_1462_, v_i_boxed_1465_, v_stop_boxed_1466_);
lean_dec_ref(v_as_1462_);
lean_dec(v_a_1461_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_array_get_size(v_as_1469_);
v___x_1473_ = lean_nat_dec_lt(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
return v___x_1473_;
}
else
{
if (v___x_1473_ == 0)
{
return v___x_1473_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = lean_usize_of_nat(v___x_1472_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1470_, v_as_1469_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1477_, lean_object* v_a_1478_){
_start:
{
uint8_t v_res_1479_; lean_object* v_r_1480_; 
v_res_1479_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_as_1477_);
v_r_1480_ = lean_box(v_res_1479_);
return v_r_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1484_, lean_object* v_structName_1485_, lean_object* v_fieldName_1486_){
_start:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
lean_inc(v_structName_1485_);
lean_inc_ref(v_env_1484_);
v___x_1487_ = l_Lean_getStructureFields(v_env_1484_, v_structName_1485_);
v___x_1488_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1487_, v_fieldName_1486_);
lean_dec_ref(v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; size_t v_sz_1492_; size_t v___x_1493_; lean_object* v___x_1494_; lean_object* v_fst_1495_; 
lean_inc_ref(v_env_1484_);
v___x_1489_ = l_Lean_getStructureSubobjects(v_env_1484_, v_structName_1485_);
v___x_1490_ = lean_box(0);
v___x_1491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1492_ = lean_array_size(v___x_1489_);
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1484_, v_fieldName_1486_, v___x_1489_, v_sz_1492_, v___x_1493_, v___x_1491_);
lean_dec_ref(v___x_1489_);
v_fst_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_fst_1495_);
lean_dec_ref(v___x_1494_);
if (lean_obj_tag(v_fst_1495_) == 0)
{
return v___x_1490_;
}
else
{
lean_object* v_val_1496_; 
v_val_1496_ = lean_ctor_get(v_fst_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v_fst_1495_, 1);
return v_val_1496_;
}
}
else
{
lean_object* v___x_1497_; 
lean_dec_ref(v_env_1484_);
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_structName_1485_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1498_, lean_object* v_fieldName_1499_, lean_object* v_as_1500_, size_t v_sz_1501_, size_t v_i_1502_, lean_object* v_b_1503_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1502_, v_sz_1501_);
if (v___x_1504_ == 0)
{
lean_dec_ref(v_env_1498_);
lean_inc_ref(v_b_1503_);
return v_b_1503_;
}
else
{
lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(0);
v_a_1506_ = lean_array_uget_borrowed(v_as_1500_, v_i_1502_);
lean_inc(v_a_1506_);
lean_inc_ref(v_env_1498_);
v___x_1507_ = l_Lean_findField_x3f(v_env_1498_, v_a_1506_, v_fieldName_1499_);
if (lean_obj_tag(v___x_1507_) == 1)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec_ref(v_env_1498_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1505_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; 
lean_dec(v___x_1507_);
v___x_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1502_, v___x_1511_);
v_i_1502_ = v___x_1512_;
v_b_1503_ = v___x_1510_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1514_, lean_object* v_fieldName_1515_, lean_object* v_as_1516_, lean_object* v_sz_1517_, lean_object* v_i_1518_, lean_object* v_b_1519_){
_start:
{
size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1517_);
lean_dec(v_sz_1517_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1514_, v_fieldName_1515_, v_as_1516_, v_sz_boxed_1520_, v_i_boxed_1521_, v_b_1519_);
lean_dec_ref(v_b_1519_);
lean_dec_ref(v_as_1516_);
lean_dec(v_fieldName_1515_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1523_, lean_object* v_structName_1524_, lean_object* v_fieldName_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_findField_x3f(v_env_1523_, v_structName_1524_, v_fieldName_1525_);
lean_dec(v_fieldName_1525_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1530_, lean_object* v_as_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_b_1534_){
_start:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1535_ == 0)
{
lean_inc_ref(v_b_1534_);
return v_b_1534_;
}
else
{
lean_object* v_a_1536_; lean_object* v_projFn_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_a_1536_ = lean_array_uget_borrowed(v_as_1531_, v_i_1533_);
v_projFn_1537_ = lean_ctor_get(v_a_1536_, 1);
v___x_1538_ = lean_box(0);
v___x_1539_ = l_Lean_Name_isSuffixOf(v_projName_1530_, v_projFn_1537_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; 
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1533_, v___x_1541_);
v_i_1533_ = v___x_1542_;
v_b_1534_ = v___x_1540_;
goto _start;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc(v_a_1536_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_a_1536_);
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1538_);
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1547_, lean_object* v_as_1548_, lean_object* v_sz_1549_, lean_object* v_i_1550_, lean_object* v_b_1551_){
_start:
{
size_t v_sz_boxed_1552_; size_t v_i_boxed_1553_; lean_object* v_res_1554_; 
v_sz_boxed_1552_ = lean_unbox_usize(v_sz_1549_);
lean_dec(v_sz_1549_);
v_i_boxed_1553_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_res_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1547_, v_as_1548_, v_sz_boxed_1552_, v_i_boxed_1553_, v_b_1551_);
lean_dec_ref(v_b_1551_);
lean_dec_ref(v_as_1548_);
lean_dec(v_projName_1547_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1555_, lean_object* v_projName_1556_, lean_object* v_structName_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_NameSet_contains(v_a_1558_, v_structName_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; lean_object* v_fst_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1605_; 
lean_inc(v_structName_1557_);
lean_inc_ref(v_env_1555_);
v___x_1560_ = l_Lean_getStructureParentInfo(v_env_1555_, v_structName_1557_);
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1585_ = lean_array_size(v___x_1560_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1556_, v___x_1560_, v_sz_1585_, v___x_1586_, v___x_1584_);
v_fst_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1587_, 1);
lean_dec(v_unused_1606_);
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_fst_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v_fst_1568_; lean_object* v_fst_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1582_; 
v___x_1562_ = l_Lean_NameSet_insert(v_a_1558_, v_structName_1557_);
v___x_1563_ = lean_box(0);
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1565_ = lean_array_size(v___x_1560_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1555_, v_projName_1556_, v___x_1560_, v_sz_1565_, v___x_1566_, v___x_1564_, v___x_1562_);
lean_dec_ref(v___x_1560_);
v_fst_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_fst_1568_);
v_fst_1569_ = lean_ctor_get(v_fst_1568_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_fst_1568_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_fst_1568_, 1);
lean_dec(v_unused_1583_);
v___x_1571_ = v_fst_1568_;
v_isShared_1572_ = v_isSharedCheck_1582_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_fst_1569_);
lean_dec(v_fst_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1582_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
if (lean_obj_tag(v_fst_1569_) == 0)
{
lean_object* v_snd_1573_; lean_object* v___x_1575_; 
v_snd_1573_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1567_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_snd_1573_);
lean_ctor_set(v___x_1571_, 0, v___x_1563_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_snd_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v_snd_1577_; lean_object* v_val_1578_; lean_object* v___x_1580_; 
v_snd_1577_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_snd_1577_);
lean_dec_ref(v___x_1567_);
v_val_1578_ = lean_ctor_get(v_fst_1569_, 0);
lean_inc(v_val_1578_);
lean_dec_ref_known(v_fst_1569_, 1);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_snd_1577_);
lean_ctor_set(v___x_1571_, 0, v_val_1578_);
v___x_1580_ = v___x_1571_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_val_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1577_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
v_resetjp_1589_:
{
if (lean_obj_tag(v_fst_1588_) == 0)
{
lean_del_object(v___x_1590_);
goto v___jp_1561_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v_fst_1588_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_fst_1588_, 1);
if (lean_obj_tag(v_val_1592_) == 1)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___x_1560_);
lean_dec(v_structName_1557_);
lean_dec_ref(v_env_1555_);
v_val_1593_ = lean_ctor_get(v_val_1592_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_val_1592_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1595_ = v_val_1592_;
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v_val_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_structName_1597_; lean_object* v___x_1599_; 
v_structName_1597_ = lean_ctor_get(v_val_1593_, 0);
lean_inc(v_structName_1597_);
lean_dec(v_val_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_structName_1597_);
v___x_1599_ = v___x_1595_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_structName_1597_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v_a_1558_);
lean_ctor_set(v___x_1590_, 0, v___x_1599_);
v___x_1601_ = v___x_1590_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1558_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_dec(v_val_1592_);
lean_del_object(v___x_1590_);
goto v___jp_1561_;
}
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_structName_1557_);
lean_dec_ref(v_env_1555_);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_a_1558_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1609_, lean_object* v_projName_1610_, lean_object* v_as_1611_, size_t v_sz_1612_, size_t v_i_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_usize_dec_lt(v_i_1613_, v_sz_1612_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
lean_dec_ref(v_env_1609_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_b_1614_);
lean_ctor_set(v___x_1617_, 1, v___y_1615_);
return v___x_1617_;
}
else
{
lean_object* v_a_1618_; lean_object* v_structName_1619_; lean_object* v___x_1620_; lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_b_1614_);
v_a_1618_ = lean_array_uget_borrowed(v_as_1611_, v_i_1613_);
v_structName_1619_ = lean_ctor_get(v_a_1618_, 0);
lean_inc(v_structName_1619_);
lean_inc_ref(v_env_1609_);
v___x_1620_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1609_, v_projName_1610_, v_structName_1619_, v___y_1615_);
v_fst_1621_ = lean_ctor_get(v___x_1620_, 0);
v_snd_1622_ = lean_ctor_get(v___x_1620_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1624_ = v___x_1620_;
v_isShared_1625_ = v_isSharedCheck_1636_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_snd_1622_);
lean_inc(v_fst_1621_);
lean_dec(v___x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1636_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_box(0);
if (lean_obj_tag(v_fst_1621_) == 1)
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec_ref(v_env_1609_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_fst_1621_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1626_);
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1626_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_snd_1622_);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; 
lean_del_object(v___x_1624_);
lean_dec(v_fst_1621_);
v___x_1632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1633_ = ((size_t)1ULL);
v___x_1634_ = lean_usize_add(v_i_1613_, v___x_1633_);
v_i_1613_ = v___x_1634_;
v_b_1614_ = v___x_1632_;
v___y_1615_ = v_snd_1622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1637_, lean_object* v_projName_1638_, lean_object* v_as_1639_, lean_object* v_sz_1640_, lean_object* v_i_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_){
_start:
{
size_t v_sz_boxed_1644_; size_t v_i_boxed_1645_; lean_object* v_res_1646_; 
v_sz_boxed_1644_ = lean_unbox_usize(v_sz_1640_);
lean_dec(v_sz_1640_);
v_i_boxed_1645_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v_res_1646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1637_, v_projName_1638_, v_as_1639_, v_sz_boxed_1644_, v_i_boxed_1645_, v_b_1642_, v___y_1643_);
lean_dec_ref(v_as_1639_);
lean_dec(v_projName_1638_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1647_, lean_object* v_projName_1648_, lean_object* v_structName_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1647_, v_projName_1648_, v_structName_1649_, v_a_1650_);
lean_dec(v_projName_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1652_, lean_object* v_structName_1653_, lean_object* v_projName_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_fst_1657_; 
v___x_1655_ = l_Lean_NameSet_empty;
v___x_1656_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1652_, v_projName_1654_, v_structName_1653_, v___x_1655_);
v_fst_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_fst_1657_);
lean_dec_ref(v___x_1656_);
return v_fst_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1658_, lean_object* v_structName_1659_, lean_object* v_projName_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_findParentProjStruct_x3f(v_env_1658_, v_structName_1659_, v_projName_1660_);
lean_dec(v_projName_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1667_ = l_Lean_Name_append(v_structCtorName_1665_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1668_, lean_object* v_structName_1669_, uint8_t v_includeSubobjectFields_1670_, lean_object* v_as_1671_, size_t v_i_1672_, size_t v_stop_1673_, lean_object* v_b_1674_){
_start:
{
lean_object* v___y_1676_; uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_eq(v_i_1672_, v_stop_1673_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_array_uget_borrowed(v_as_1671_, v_i_1672_);
lean_inc(v___x_1681_);
lean_inc(v_structName_1669_);
lean_inc_ref(v_env_1668_);
v___x_1682_ = l_Lean_isSubobjectField_x3f(v_env_1668_, v_structName_1669_, v___x_1681_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; 
lean_inc(v___x_1681_);
v___x_1683_ = lean_array_push(v_b_1674_, v___x_1681_);
v___y_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
if (v_includeSubobjectFields_1670_ == 0)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
v_val_1684_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1682_, 1);
lean_inc_ref(v_env_1668_);
v___x_1685_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1668_, v_val_1684_, v_b_1674_, v_includeSubobjectFields_1670_);
v___y_1676_ = v___x_1685_;
goto v___jp_1675_;
}
else
{
lean_object* v_val_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_val_1686_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1682_, 1);
lean_inc(v___x_1681_);
v___x_1687_ = lean_array_push(v_b_1674_, v___x_1681_);
lean_inc_ref(v_env_1668_);
v___x_1688_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1668_, v_val_1686_, v___x_1687_, v_includeSubobjectFields_1670_);
v___y_1676_ = v___x_1688_;
goto v___jp_1675_;
}
}
}
else
{
lean_dec(v_structName_1669_);
lean_dec_ref(v_env_1668_);
return v_b_1674_;
}
v___jp_1675_:
{
size_t v___x_1677_; size_t v___x_1678_; 
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1672_, v___x_1677_);
v_i_1672_ = v___x_1678_;
v_b_1674_ = v___y_1676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1689_, lean_object* v_structName_1690_, lean_object* v_fullNames_1691_, uint8_t v_includeSubobjectFields_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
lean_inc(v_structName_1690_);
lean_inc_ref(v_env_1689_);
v___x_1693_ = l_Lean_getStructureFields(v_env_1689_, v_structName_1690_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = lean_array_get_size(v___x_1693_);
v___x_1696_ = lean_nat_dec_lt(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v___x_1693_);
lean_dec(v_structName_1690_);
lean_dec_ref(v_env_1689_);
return v_fullNames_1691_;
}
else
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_nat_dec_le(v___x_1695_, v___x_1695_);
if (v___x_1697_ == 0)
{
if (v___x_1696_ == 0)
{
lean_dec_ref(v___x_1693_);
lean_dec(v_structName_1690_);
lean_dec_ref(v_env_1689_);
return v_fullNames_1691_;
}
else
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_of_nat(v___x_1695_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1689_, v_structName_1690_, v_includeSubobjectFields_1692_, v___x_1693_, v___x_1698_, v___x_1699_, v_fullNames_1691_);
lean_dec_ref(v___x_1693_);
return v___x_1700_;
}
}
else
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = lean_usize_of_nat(v___x_1695_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1689_, v_structName_1690_, v_includeSubobjectFields_1692_, v___x_1693_, v___x_1701_, v___x_1702_, v_fullNames_1691_);
lean_dec_ref(v___x_1693_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1704_, lean_object* v_structName_1705_, lean_object* v_fullNames_1706_, lean_object* v_includeSubobjectFields_1707_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1708_; lean_object* v_res_1709_; 
v_includeSubobjectFields_boxed_1708_ = lean_unbox(v_includeSubobjectFields_1707_);
v_res_1709_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1704_, v_structName_1705_, v_fullNames_1706_, v_includeSubobjectFields_boxed_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1710_, lean_object* v_structName_1711_, lean_object* v_includeSubobjectFields_1712_, lean_object* v_as_1713_, lean_object* v_i_1714_, lean_object* v_stop_1715_, lean_object* v_b_1716_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1717_; size_t v_i_boxed_1718_; size_t v_stop_boxed_1719_; lean_object* v_res_1720_; 
v_includeSubobjectFields_boxed_1717_ = lean_unbox(v_includeSubobjectFields_1712_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_stop_boxed_1719_ = lean_unbox_usize(v_stop_1715_);
lean_dec(v_stop_1715_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1710_, v_structName_1711_, v_includeSubobjectFields_boxed_1717_, v_as_1713_, v_i_boxed_1718_, v_stop_boxed_1719_, v_b_1716_);
lean_dec_ref(v_as_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1721_, lean_object* v_structName_1722_, uint8_t v_includeSubobjectFields_1723_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1725_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1721_, v_structName_1722_, v___x_1724_, v_includeSubobjectFields_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1726_, lean_object* v_structName_1727_, lean_object* v_includeSubobjectFields_1728_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1729_; lean_object* v_res_1730_; 
v_includeSubobjectFields_boxed_1729_ = lean_unbox(v_includeSubobjectFields_1728_);
v_res_1730_ = l_Lean_getStructureFieldsFlattened(v_env_1726_, v_structName_1727_, v_includeSubobjectFields_boxed_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1731_, lean_object* v_constName_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_getStructureInfo_x3f(v_env_1731_, v_constName_1732_);
if (lean_obj_tag(v___x_1733_) == 0)
{
uint8_t v___x_1734_; 
v___x_1734_ = 0;
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = 1;
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1736_, lean_object* v_constName_1737_){
_start:
{
uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_res_1738_ = l_Lean_isStructure(v_env_1736_, v_constName_1737_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1740_, lean_object* v_structName_1741_, lean_object* v_fieldName_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_getFieldInfo_x3f(v_env_1740_, v_structName_1741_, v_fieldName_1742_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_val_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_projFn_1748_; lean_object* v___x_1750_; 
v_projFn_1748_ = lean_ctor_get(v_val_1744_, 1);
lean_inc(v_projFn_1748_);
lean_dec(v_val_1744_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v_projFn_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_projFn_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v___x_1753_; 
lean_dec(v___x_1743_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1754_, lean_object* v_structName_1755_, lean_object* v_fieldName_1756_){
_start:
{
lean_object* v___x_1757_; 
lean_inc_ref(v_env_1754_);
v___x_1757_ = l_Lean_getProjFnForField_x3f(v_env_1754_, v_structName_1755_, v_fieldName_1756_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1759_; 
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_n(v_val_1758_, 2);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1754_, v_val_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_val_1758_);
v___x_1760_ = lean_box(0);
return v___x_1760_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1769_; 
v_val_1761_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_val_1758_);
lean_ctor_set(v___x_1765_, 1, v_val_1761_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v___x_1757_);
lean_dec_ref(v_env_1754_);
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1776_ = l_Lean_Name_append(v_projFn_1774_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1782_ = l_Lean_Name_append(v_projFn_1780_, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1783_, lean_object* v_env_1784_, lean_object* v_structName_1785_, lean_object* v_fieldName_1786_){
_start:
{
lean_object* v___x_1787_; 
lean_inc(v_fieldName_1786_);
lean_inc(v_structName_1785_);
lean_inc_ref(v_env_1784_);
v___x_1787_ = l_Lean_getProjFnForField_x3f(v_env_1784_, v_structName_1785_, v_fieldName_1786_);
if (lean_obj_tag(v___x_1787_) == 1)
{
lean_object* v_val_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_fieldName_1786_);
lean_dec(v_structName_1785_);
v_val_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_val_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_defFn_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; 
v_defFn_1792_ = lean_apply_1(v_mkName_1783_, v_val_1788_);
v___x_1793_ = 1;
lean_inc(v_defFn_1792_);
v___x_1794_ = l_Lean_Environment_contains(v_env_1784_, v_defFn_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_dec(v_defFn_1792_);
lean_del_object(v___x_1790_);
v___x_1795_ = lean_box(0);
return v___x_1795_;
}
else
{
lean_object* v___x_1797_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_defFn_1792_);
v___x_1797_ = v___x_1790_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_defFn_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v_defFn_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; 
lean_dec(v___x_1787_);
v___x_1800_ = l_Lean_Name_append(v_structName_1785_, v_fieldName_1786_);
v_defFn_1801_ = lean_apply_1(v_mkName_1783_, v___x_1800_);
v___x_1802_ = 1;
lean_inc(v_defFn_1801_);
v___x_1803_ = l_Lean_Environment_contains(v_env_1784_, v_defFn_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec(v_defFn_1801_);
v___x_1804_ = lean_box(0);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_defFn_1801_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1807_, lean_object* v_structName_1808_, lean_object* v_fieldName_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1811_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1810_, v_env_1807_, v_structName_1808_, v_fieldName_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1813_, lean_object* v_structName_1814_, lean_object* v_fieldName_1815_){
_start:
{
lean_object* v___x_1816_; 
lean_inc(v_fieldName_1815_);
lean_inc(v_structName_1814_);
lean_inc_ref(v_env_1813_);
v___x_1816_ = l_Lean_getDefaultFnForField_x3f(v_env_1813_, v_structName_1814_, v_fieldName_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1818_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1817_, v_env_1813_, v_structName_1814_, v_fieldName_1815_);
return v___x_1818_;
}
else
{
lean_dec(v_fieldName_1815_);
lean_dec(v_structName_1814_);
lean_dec_ref(v_env_1813_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1824_ = l_Lean_Name_append(v_projFn_1822_, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1826_, lean_object* v_structName_1827_, lean_object* v_fieldName_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1830_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1829_, v_env_1826_, v_structName_1827_, v_fieldName_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1831_, lean_object* v_env_1832_, lean_object* v_baseStructName_1833_, lean_object* v_as_1834_, lean_object* v_i_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_snd_1838_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_array_get_size(v_as_1834_);
v___x_1843_ = lean_nat_dec_lt(v_i_1835_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_i_1835_);
lean_dec_ref(v_env_1832_);
lean_dec(v_path_1831_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___y_1836_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v_subobject_x3f_1847_; 
v___x_1846_ = lean_array_fget_borrowed(v_as_1834_, v_i_1835_);
v_subobject_x3f_1847_ = lean_ctor_get(v___x_1846_, 2);
if (lean_obj_tag(v_subobject_x3f_1847_) == 1)
{
lean_object* v_projFn_1848_; lean_object* v_val_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_fst_1852_; 
v_projFn_1848_ = lean_ctor_get(v___x_1846_, 1);
v_val_1849_ = lean_ctor_get(v_subobject_x3f_1847_, 0);
lean_inc(v_path_1831_);
lean_inc(v_projFn_1848_);
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_projFn_1848_);
lean_ctor_set(v___x_1850_, 1, v_path_1831_);
lean_inc(v_val_1849_);
lean_inc_ref(v_env_1832_);
v___x_1851_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1832_, v_baseStructName_1833_, v_val_1849_, v___x_1850_, v___y_1836_);
v_fst_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_fst_1852_);
if (lean_obj_tag(v_fst_1852_) == 0)
{
lean_object* v_snd_1853_; 
v_snd_1853_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_snd_1853_);
lean_dec_ref(v___x_1851_);
v_snd_1838_ = v_snd_1853_;
goto v___jp_1837_;
}
else
{
lean_dec_ref_known(v_fst_1852_, 1);
lean_dec(v_i_1835_);
lean_dec_ref(v_env_1832_);
lean_dec(v_path_1831_);
return v___x_1851_;
}
}
else
{
v_snd_1838_ = v___y_1836_;
goto v___jp_1837_;
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_add(v_i_1835_, v___x_1839_);
lean_dec(v_i_1835_);
v_i_1835_ = v___x_1840_;
v___y_1836_ = v_snd_1838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1854_, lean_object* v_baseStructName_1855_, lean_object* v_structName_1856_, lean_object* v_path_1857_, lean_object* v_a_1858_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_name_eq(v_baseStructName_1855_, v_structName_1856_);
if (v___x_1872_ == 0)
{
uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_NameSet_contains(v_a_1858_, v_structName_1856_);
if (v___x_1873_ == 0)
{
goto v___jp_1859_;
}
else
{
if (v___x_1872_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_path_1857_);
lean_dec(v_structName_1856_);
lean_dec_ref(v_env_1854_);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1858_);
return v___x_1875_;
}
else
{
goto v___jp_1859_;
}
}
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_structName_1856_);
lean_dec_ref(v_env_1854_);
v___x_1876_ = l_List_reverse___redArg(v_path_1857_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_a_1858_);
return v___x_1878_;
}
v___jp_1859_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_inc(v_structName_1856_);
v___x_1860_ = l_Lean_NameSet_insert(v_a_1858_, v_structName_1856_);
lean_inc_ref(v_env_1854_);
v___x_1861_ = l_Lean_getStructureInfo_x3f(v_env_1854_, v_structName_1856_);
if (lean_obj_tag(v___x_1861_) == 1)
{
lean_object* v_val_1862_; lean_object* v_fieldInfo_1863_; lean_object* v_parentInfo_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_fst_1867_; 
v_val_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v_fieldInfo_1863_ = lean_ctor_get(v_val_1862_, 2);
lean_inc_ref(v_fieldInfo_1863_);
v_parentInfo_1864_ = lean_ctor_get(v_val_1862_, 3);
lean_inc_ref(v_parentInfo_1864_);
lean_dec(v_val_1862_);
v___x_1865_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1854_);
lean_inc(v_path_1857_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1857_, v_env_1854_, v_baseStructName_1855_, v_fieldInfo_1863_, v___x_1865_, v___x_1860_);
lean_dec_ref(v_fieldInfo_1863_);
v_fst_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_fst_1867_);
if (lean_obj_tag(v_fst_1867_) == 0)
{
lean_object* v_snd_1868_; lean_object* v___x_1869_; 
v_snd_1868_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_snd_1868_);
lean_dec_ref(v___x_1866_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1857_, v_env_1854_, v_baseStructName_1855_, v_parentInfo_1864_, v___x_1865_, v_snd_1868_);
lean_dec_ref(v_parentInfo_1864_);
return v___x_1869_;
}
else
{
lean_dec_ref_known(v_fst_1867_, 1);
lean_dec_ref(v_parentInfo_1864_);
lean_dec(v_path_1857_);
lean_dec_ref(v_env_1854_);
return v___x_1866_;
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v___x_1861_);
lean_dec(v_path_1857_);
lean_dec_ref(v_env_1854_);
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1860_);
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1879_, lean_object* v_env_1880_, lean_object* v_baseStructName_1881_, lean_object* v_as_1882_, lean_object* v_i_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_get_size(v_as_1882_);
v___x_1886_ = lean_nat_dec_lt(v_i_1883_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_i_1883_);
lean_dec_ref(v_env_1880_);
lean_dec(v_path_1879_);
v___x_1887_ = lean_box(0);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___y_1884_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; lean_object* v_structName_1890_; lean_object* v_projFn_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_fst_1894_; 
v___x_1889_ = lean_array_fget_borrowed(v_as_1882_, v_i_1883_);
v_structName_1890_ = lean_ctor_get(v___x_1889_, 0);
v_projFn_1891_ = lean_ctor_get(v___x_1889_, 1);
lean_inc(v_path_1879_);
lean_inc(v_projFn_1891_);
v___x_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_projFn_1891_);
lean_ctor_set(v___x_1892_, 1, v_path_1879_);
lean_inc(v_structName_1890_);
lean_inc_ref(v_env_1880_);
v___x_1893_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1880_, v_baseStructName_1881_, v_structName_1890_, v___x_1892_, v___y_1884_);
v_fst_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_fst_1894_);
if (lean_obj_tag(v_fst_1894_) == 0)
{
lean_object* v_snd_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_snd_1895_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_snd_1895_);
lean_dec_ref(v___x_1893_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_nat_add(v_i_1883_, v___x_1896_);
lean_dec(v_i_1883_);
v_i_1883_ = v___x_1897_;
v___y_1884_ = v_snd_1895_;
goto _start;
}
else
{
lean_dec_ref_known(v_fst_1894_, 1);
lean_dec(v_i_1883_);
lean_dec_ref(v_env_1880_);
lean_dec(v_path_1879_);
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1899_, lean_object* v_env_1900_, lean_object* v_baseStructName_1901_, lean_object* v_as_1902_, lean_object* v_i_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1899_, v_env_1900_, v_baseStructName_1901_, v_as_1902_, v_i_1903_, v___y_1904_);
lean_dec_ref(v_as_1902_);
lean_dec(v_baseStructName_1901_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1906_, lean_object* v_env_1907_, lean_object* v_baseStructName_1908_, lean_object* v_as_1909_, lean_object* v_i_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1906_, v_env_1907_, v_baseStructName_1908_, v_as_1909_, v_i_1910_, v___y_1911_);
lean_dec_ref(v_as_1909_);
lean_dec(v_baseStructName_1908_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1913_, lean_object* v_baseStructName_1914_, lean_object* v_structName_1915_, lean_object* v_path_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1913_, v_baseStructName_1914_, v_structName_1915_, v_path_1916_, v_a_1917_);
lean_dec(v_baseStructName_1914_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1919_, lean_object* v_baseStructName_1920_, lean_object* v_structName_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_fst_1925_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = l_Lean_NameSet_empty;
v___x_1924_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1919_, v_baseStructName_1920_, v_structName_1921_, v___x_1922_, v___x_1923_);
v_fst_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_fst_1925_);
lean_dec_ref(v___x_1924_);
return v_fst_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1926_, lean_object* v_baseStructName_1927_, lean_object* v_structName_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_getPathToBaseStructure_x3f(v_env_1926_, v_baseStructName_1927_, v_structName_1928_);
lean_dec(v_baseStructName_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1930_, lean_object* v_constName_1931_){
_start:
{
uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = 0;
v___x_1933_ = l_Lean_Environment_find_x3f(v_env_1930_, v_constName_1931_, v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 1)
{
lean_object* v_val_1934_; 
v_val_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v___x_1933_, 1);
if (lean_obj_tag(v_val_1934_) == 5)
{
lean_object* v_val_1935_; lean_object* v_numIndices_1936_; lean_object* v_ctors_1937_; uint8_t v_isRec_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_val_1935_ = lean_ctor_get(v_val_1934_, 0);
lean_inc_ref(v_val_1935_);
lean_dec_ref_known(v_val_1934_, 1);
v_numIndices_1936_ = lean_ctor_get(v_val_1935_, 2);
lean_inc(v_numIndices_1936_);
v_ctors_1937_ = lean_ctor_get(v_val_1935_, 4);
lean_inc(v_ctors_1937_);
v_isRec_1938_ = lean_ctor_get_uint8(v_val_1935_, sizeof(void*)*6);
lean_dec_ref(v_val_1935_);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_nat_dec_eq(v_numIndices_1936_, v___x_1939_);
lean_dec(v_numIndices_1936_);
if (v___x_1940_ == 0)
{
lean_dec(v_ctors_1937_);
return v___x_1932_;
}
else
{
if (lean_obj_tag(v_ctors_1937_) == 1)
{
lean_object* v_tail_1941_; 
v_tail_1941_ = lean_ctor_get(v_ctors_1937_, 1);
lean_inc(v_tail_1941_);
lean_dec_ref_known(v_ctors_1937_, 2);
if (lean_obj_tag(v_tail_1941_) == 0)
{
if (v_isRec_1938_ == 0)
{
return v___x_1940_;
}
else
{
return v___x_1932_;
}
}
else
{
lean_dec(v_tail_1941_);
return v___x_1932_;
}
}
else
{
lean_dec(v_ctors_1937_);
return v___x_1932_;
}
}
}
else
{
lean_dec(v_val_1934_);
return v___x_1932_;
}
}
else
{
lean_dec(v___x_1933_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1942_, lean_object* v_constName_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Lean_isNonRecStructure(v_env_1942_, v_constName_1943_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1946_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_panic_fn_borrowed(v___x_1947_, v_msg_1946_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1950_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1951_ = lean_unsigned_to_nat(11u);
v___x_1952_ = lean_unsigned_to_nat(374u);
v___x_1953_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1954_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1955_ = l_mkPanicMessageWithDecl(v___x_1954_, v___x_1953_, v___x_1952_, v___x_1951_, v___x_1950_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1956_, lean_object* v_constName_1957_){
_start:
{
uint8_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = 0;
lean_inc_ref(v_env_1956_);
v___x_1962_ = l_Lean_Environment_find_x3f(v_env_1956_, v_constName_1957_, v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 1)
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1962_, 1);
if (lean_obj_tag(v_val_1963_) == 5)
{
lean_object* v_val_1964_; lean_object* v_numIndices_1965_; lean_object* v_ctors_1966_; uint8_t v_isRec_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_val_1964_ = lean_ctor_get(v_val_1963_, 0);
lean_inc_ref(v_val_1964_);
lean_dec_ref_known(v_val_1963_, 1);
v_numIndices_1965_ = lean_ctor_get(v_val_1964_, 2);
lean_inc(v_numIndices_1965_);
v_ctors_1966_ = lean_ctor_get(v_val_1964_, 4);
lean_inc(v_ctors_1966_);
v_isRec_1967_ = lean_ctor_get_uint8(v_val_1964_, sizeof(void*)*6);
lean_dec_ref(v_val_1964_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_nat_dec_eq(v_numIndices_1965_, v___x_1968_);
lean_dec(v_numIndices_1965_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v_ctors_1966_);
lean_dec_ref(v_env_1956_);
v___x_1970_ = lean_box(0);
return v___x_1970_;
}
else
{
if (lean_obj_tag(v_ctors_1966_) == 1)
{
lean_object* v_tail_1971_; 
v_tail_1971_ = lean_ctor_get(v_ctors_1966_, 1);
if (lean_obj_tag(v_tail_1971_) == 0)
{
if (v_isRec_1967_ == 0)
{
lean_object* v_head_1972_; lean_object* v___x_1973_; 
v_head_1972_ = lean_ctor_get(v_ctors_1966_, 0);
lean_inc(v_head_1972_);
lean_dec_ref_known(v_ctors_1966_, 2);
v___x_1973_ = l_Lean_Environment_find_x3f(v_env_1956_, v_head_1972_, v_isRec_1967_);
if (lean_obj_tag(v___x_1973_) == 1)
{
lean_object* v_val_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_val_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_val_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
if (lean_obj_tag(v_val_1974_) == 6)
{
lean_object* v_val_1978_; lean_object* v___x_1980_; 
v_val_1978_ = lean_ctor_get(v_val_1974_, 0);
lean_inc_ref(v_val_1978_);
lean_dec_ref_known(v_val_1974_, 1);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_val_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_val_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_del_object(v___x_1976_);
lean_dec(v_val_1974_);
goto v___jp_1958_;
}
}
}
else
{
lean_dec(v___x_1973_);
goto v___jp_1958_;
}
}
else
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v_ctors_1966_, 2);
lean_dec_ref(v_env_1956_);
v___x_1983_ = lean_box(0);
return v___x_1983_;
}
}
else
{
lean_object* v___x_1984_; 
lean_dec_ref_known(v_ctors_1966_, 2);
lean_dec_ref(v_env_1956_);
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
}
else
{
lean_object* v___x_1985_; 
lean_dec(v_ctors_1966_);
lean_dec_ref(v_env_1956_);
v___x_1985_ = lean_box(0);
return v___x_1985_;
}
}
}
else
{
lean_object* v___x_1986_; 
lean_dec(v_val_1963_);
lean_dec_ref(v_env_1956_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
}
else
{
lean_object* v___x_1987_; 
lean_dec(v___x_1962_);
lean_dec_ref(v_env_1956_);
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
v___jp_1958_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1960_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1959_);
return v___x_1960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1988_, lean_object* v_constName_1989_){
_start:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = 0;
lean_inc_ref(v_env_1988_);
v___x_1991_ = l_Lean_Environment_find_x3f(v_env_1988_, v_constName_1989_, v___x_1990_);
if (lean_obj_tag(v___x_1991_) == 1)
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1991_, 1);
if (lean_obj_tag(v_val_1992_) == 5)
{
lean_object* v_val_1993_; lean_object* v_numIndices_1994_; lean_object* v_ctors_1995_; uint8_t v_isRec_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_val_1993_ = lean_ctor_get(v_val_1992_, 0);
lean_inc_ref(v_val_1993_);
lean_dec_ref_known(v_val_1992_, 1);
v_numIndices_1994_ = lean_ctor_get(v_val_1993_, 2);
lean_inc(v_numIndices_1994_);
v_ctors_1995_ = lean_ctor_get(v_val_1993_, 4);
lean_inc(v_ctors_1995_);
v_isRec_1996_ = lean_ctor_get_uint8(v_val_1993_, sizeof(void*)*6);
lean_dec_ref(v_val_1993_);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_nat_dec_eq(v_numIndices_1994_, v___x_1997_);
lean_dec(v_numIndices_1994_);
if (v___x_1998_ == 0)
{
lean_dec(v_ctors_1995_);
lean_dec_ref(v_env_1988_);
return v___x_1997_;
}
else
{
if (lean_obj_tag(v_ctors_1995_) == 1)
{
lean_object* v_tail_1999_; 
v_tail_1999_ = lean_ctor_get(v_ctors_1995_, 1);
if (lean_obj_tag(v_tail_1999_) == 0)
{
if (v_isRec_1996_ == 0)
{
lean_object* v_head_2000_; lean_object* v___x_2001_; 
v_head_2000_ = lean_ctor_get(v_ctors_1995_, 0);
lean_inc(v_head_2000_);
lean_dec_ref_known(v_ctors_1995_, 2);
v___x_2001_ = l_Lean_Environment_find_x3f(v_env_1988_, v_head_2000_, v_isRec_1996_);
if (lean_obj_tag(v___x_2001_) == 1)
{
lean_object* v_val_2002_; 
v_val_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v___x_2001_, 1);
if (lean_obj_tag(v_val_2002_) == 6)
{
lean_object* v_val_2003_; lean_object* v_numFields_2004_; 
v_val_2003_ = lean_ctor_get(v_val_2002_, 0);
lean_inc_ref(v_val_2003_);
lean_dec_ref_known(v_val_2002_, 1);
v_numFields_2004_ = lean_ctor_get(v_val_2003_, 4);
lean_inc(v_numFields_2004_);
lean_dec_ref(v_val_2003_);
return v_numFields_2004_;
}
else
{
lean_dec(v_val_2002_);
return v___x_1997_;
}
}
else
{
lean_dec(v___x_2001_);
return v___x_1997_;
}
}
else
{
lean_dec_ref_known(v_ctors_1995_, 2);
lean_dec_ref(v_env_1988_);
return v___x_1997_;
}
}
else
{
lean_dec_ref_known(v_ctors_1995_, 2);
lean_dec_ref(v_env_1988_);
return v___x_1997_;
}
}
else
{
lean_dec(v_ctors_1995_);
lean_dec_ref(v_env_1988_);
return v___x_1997_;
}
}
}
else
{
lean_object* v___x_2005_; 
lean_dec(v_val_1992_);
lean_dec_ref(v_env_1988_);
v___x_2005_ = lean_unsigned_to_nat(0u);
return v___x_2005_;
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v___x_1991_);
lean_dec_ref(v_env_1988_);
v___x_2006_ = lean_unsigned_to_nat(0u);
return v___x_2006_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_2015_);
return v_res_2017_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___f_2019_; 
v___x_2018_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_2019_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2019_, 0, v___x_2018_);
return v___f_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___f_2021_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_box(1);
v___x_2024_ = l_Lean_registerEnvExtension___redArg(v___f_2021_, v___x_2022_, v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2027_, lean_object* v_structName_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v_asyncMode_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2029_ = l_Lean_structureResolutionExt;
v_asyncMode_2030_ = lean_ctor_get(v___x_2029_, 2);
v___x_2031_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2032_ = lean_box(0);
v___x_2033_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2031_, v___x_2029_, v_env_2027_, v_asyncMode_2030_, v___x_2032_);
v___x_2034_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2033_, v_structName_2028_);
lean_dec(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2035_, lean_object* v_structName_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2035_, v_structName_2036_);
lean_dec(v_structName_2036_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2038_, lean_object* v___x_2039_, lean_object* v_structName_2040_, lean_object* v_resolutionOrder_2041_, lean_object* v_s_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2038_, v___x_2039_, v_s_2042_, v_structName_2040_, v_resolutionOrder_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2044_, lean_object* v_env_2045_){
_start:
{
lean_object* v___x_2046_; lean_object* v_asyncMode_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = l_Lean_structureResolutionExt;
v_asyncMode_2047_ = lean_ctor_get(v___x_2046_, 2);
v___x_2048_ = lean_box(0);
v___x_2049_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2046_, v_env_2045_, v___f_2044_, v_asyncMode_2047_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2050_, lean_object* v_structName_2051_, lean_object* v_resolutionOrder_2052_){
_start:
{
lean_object* v_modifyEnv_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___x_2058_; 
v_modifyEnv_2053_ = lean_ctor_get(v_inst_2050_, 1);
lean_inc(v_modifyEnv_2053_);
lean_dec_ref(v_inst_2050_);
v___x_2054_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2055_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2056_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2056_, 0, v___x_2054_);
lean_closure_set(v___f_2056_, 1, v___x_2055_);
lean_closure_set(v___f_2056_, 2, v_structName_2051_);
lean_closure_set(v___f_2056_, 3, v_resolutionOrder_2052_);
v___f_2057_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2057_, 0, v___f_2056_);
v___x_2058_ = lean_apply_1(v_modifyEnv_2053_, v___f_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2059_, lean_object* v_inst_2060_, lean_object* v_structName_2061_, lean_object* v_resolutionOrder_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2060_, v_structName_2061_, v_resolutionOrder_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2081_, lean_object* v_resOrders_2082_, lean_object* v___x_2083_, lean_object* v_toPure_2084_, lean_object* v_____s_2085_){
_start:
{
lean_object* v_fst_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2101_; 
v_fst_2086_ = lean_ctor_get(v_____s_2085_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_____s_2085_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_____s_2085_, 1);
lean_dec(v_unused_2102_);
v___x_2088_ = v_____s_2085_;
v_isShared_2089_ = v_isSharedCheck_2101_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_fst_2086_);
lean_dec(v_____s_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2101_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
if (lean_obj_tag(v_fst_2086_) == 0)
{
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2090_ = 0;
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_array_get_borrowed(v___x_2081_, v_resOrders_2082_, v___x_2091_);
v___x_2093_ = lean_array_get_borrowed(v___x_2083_, v___x_2092_, v___x_2091_);
v___x_2094_ = lean_box(v___x_2090_);
lean_inc(v___x_2093_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2093_);
lean_ctor_set(v___x_2088_, 0, v___x_2094_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2093_);
v___x_2096_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_apply_2(v_toPure_2084_, lean_box(0), v___x_2096_);
return v___x_2097_;
}
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2100_; 
lean_del_object(v___x_2088_);
v_val_2099_ = lean_ctor_get(v_fst_2086_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v_fst_2086_, 1);
v___x_2100_ = lean_apply_2(v_toPure_2084_, lean_box(0), v_val_2099_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2103_, lean_object* v_resOrders_2104_, lean_object* v___x_2105_, lean_object* v_toPure_2106_, lean_object* v_____s_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2103_, v_resOrders_2104_, v___x_2105_, v_toPure_2106_, v_____s_2107_);
lean_dec(v___x_2105_);
lean_dec_ref(v_resOrders_2104_);
lean_dec_ref(v___x_2103_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2109_, lean_object* v_____do__lift_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_apply_2(v_toPure_2109_, lean_box(0), v_____do__lift_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2112_, lean_object* v_toPure_2113_, lean_object* v___x_2114_, lean_object* v_____s_2115_){
_start:
{
lean_object* v_fst_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
v_fst_2116_ = lean_ctor_get(v_____s_2115_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_____s_2115_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_____s_2115_, 1);
lean_dec(v_unused_2135_);
v___x_2118_ = v_____s_2115_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_fst_2116_);
lean_dec(v_____s_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
if (lean_obj_tag(v_fst_2116_) == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_del_object(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2112_);
v___x_2121_ = lean_apply_2(v_toPure_2113_, lean_box(0), v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v___x_2112_);
lean_inc_ref(v_fst_2116_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v___x_2114_);
v___x_2123_ = v___x_2118_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2116_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2114_);
v___x_2123_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_isSharedCheck_2131_ = !lean_is_exclusive(v_fst_2116_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v_fst_2116_, 0);
lean_dec(v_unused_2132_);
v___x_2125_ = v_fst_2116_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_fst_2116_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2123_);
v___x_2128_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_apply_2(v_toPure_2113_, lean_box(0), v___x_2128_);
return v___x_2129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2136_, lean_object* v_next_2137_, lean_object* v_G_2138_, lean_object* v_____do__lift_2139_){
_start:
{
if (lean_obj_tag(v_____do__lift_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
lean_dec(v_G_2138_);
v_a_2140_ = lean_ctor_get(v_____do__lift_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v_____do__lift_2139_, 1);
v___x_2141_ = lean_apply_2(v_toPure_2136_, lean_box(0), v_a_2140_);
return v___x_2141_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v_toPure_2136_);
v_a_2142_ = lean_ctor_get(v_____do__lift_2139_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v_____do__lift_2139_, 1);
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_next_2137_, v___x_2143_);
v___x_2145_ = lean_apply_4(v_G_2138_, v___x_2144_, v_a_2142_, lean_box(0), lean_box(0));
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2146_, lean_object* v_next_2147_, lean_object* v_G_2148_, lean_object* v_____do__lift_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2146_, v_next_2147_, v_G_2148_, v_____do__lift_2149_);
lean_dec(v_next_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2151_, lean_object* v_v_2152_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_name_eq(v_v_2152_, v___x_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2154_, lean_object* v_v_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2154_, v_v_2155_);
lean_dec(v_v_2155_);
lean_dec(v___x_2154_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2177_, lean_object* v___f_2178_, lean_object* v_resOrder_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v_array_2184_; lean_object* v_start_2185_; lean_object* v_stop_2186_; uint8_t v___x_2187_; lean_object* v___y_2189_; 
v___x_2180_ = lean_unsigned_to_nat(1u);
v___x_2181_ = lean_array_get_size(v_resOrder_2179_);
v___x_2182_ = l_Array_toSubarray___redArg(v_resOrder_2179_, v___x_2180_, v___x_2181_);
v___x_2183_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2184_ = lean_ctor_get(v___x_2182_, 0);
lean_inc_ref(v_array_2184_);
v_start_2185_ = lean_ctor_get(v___x_2182_, 1);
lean_inc(v_start_2185_);
v_stop_2186_ = lean_ctor_get(v___x_2182_, 2);
lean_inc(v_stop_2186_);
lean_dec_ref(v___x_2182_);
v___x_2187_ = lean_nat_dec_lt(v_start_2185_, v_stop_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_stop_2186_);
lean_dec(v_start_2185_);
lean_dec_ref(v_array_2184_);
lean_dec_ref(v___f_2178_);
return v___x_2177_;
}
else
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = lean_array_get_size(v_array_2184_);
v___x_2197_ = lean_nat_dec_le(v_stop_2186_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec(v_stop_2186_);
v___y_2189_ = v___x_2196_;
goto v___jp_2188_;
}
else
{
v___y_2189_ = v_stop_2186_;
goto v___jp_2188_;
}
}
v___jp_2188_:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_nat_dec_lt(v_start_2185_, v___y_2189_);
if (v___x_2190_ == 0)
{
lean_dec(v___y_2189_);
lean_dec(v_start_2185_);
lean_dec_ref(v_array_2184_);
lean_dec_ref(v___f_2178_);
return v___x_2187_;
}
else
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2191_ = lean_usize_of_nat(v_start_2185_);
lean_dec(v_start_2185_);
v___x_2192_ = lean_usize_of_nat(v___y_2189_);
lean_dec(v___y_2189_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2183_, v___f_2178_, v_array_2184_, v___x_2191_, v___x_2192_);
v___x_2194_ = lean_unbox(v___x_2193_);
lean_dec(v___x_2193_);
if (v___x_2194_ == 0)
{
return v___x_2190_;
}
else
{
uint8_t v___x_2195_; 
v___x_2195_ = 0;
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2198_, lean_object* v___f_2199_, lean_object* v_resOrder_2200_){
_start:
{
uint8_t v___x_1715__boxed_2201_; uint8_t v_res_2202_; lean_object* v_r_2203_; 
v___x_1715__boxed_2201_ = lean_unbox(v___x_2198_);
v_res_2202_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2201_, v___f_2199_, v_resOrder_2200_);
v_r_2203_ = lean_box(v_res_2202_);
return v_r_2203_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2204_, uint8_t v___y_2205_, lean_object* v_v_2206_){
_start:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_apply_1(v___f_2204_, v_v_2206_);
v___x_2208_ = lean_unbox(v___x_2207_);
if (v___x_2208_ == 0)
{
return v___y_2205_;
}
else
{
uint8_t v___x_2209_; 
v___x_2209_ = 0;
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2210_, lean_object* v___y_2211_, lean_object* v_v_2212_){
_start:
{
uint8_t v___y_1771__boxed_2213_; uint8_t v_res_2214_; lean_object* v_r_2215_; 
v___y_1771__boxed_2213_ = lean_unbox(v___y_2211_);
v_res_2214_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2210_, v___y_1771__boxed_2213_, v_v_2212_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2216_, uint8_t v___x_2217_, lean_object* v_v_2218_){
_start:
{
lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = lean_apply_1(v___f_2216_, v_v_2218_);
v___x_2220_ = lean_unbox(v___x_2219_);
if (v___x_2220_ == 0)
{
return v___x_2217_;
}
else
{
uint8_t v___x_2221_; 
v___x_2221_ = 0;
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2222_, lean_object* v___x_2223_, lean_object* v_v_2224_){
_start:
{
uint8_t v___x_1783__boxed_2225_; uint8_t v_res_2226_; lean_object* v_r_2227_; 
v___x_1783__boxed_2225_ = lean_unbox(v___x_2223_);
v_res_2226_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2222_, v___x_1783__boxed_2225_, v_v_2224_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2228_, lean_object* v_toPure_2229_, lean_object* v___x_2230_, lean_object* v_resOrders_2231_, lean_object* v___x_2232_, lean_object* v___x_2233_, lean_object* v_toBind_2234_, lean_object* v___f_2235_, lean_object* v___x_2236_, lean_object* v_next_2237_, lean_object* v___x_2238_, lean_object* v_next_2239_, lean_object* v_acc_2240_, lean_object* v_h_2241_, lean_object* v_G_2242_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_nat_dec_lt(v_next_2239_, v___x_2228_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec(v_G_2242_);
lean_dec(v_next_2239_);
lean_dec_ref(v___x_2236_);
lean_dec(v___f_2235_);
lean_dec(v_toBind_2234_);
lean_dec(v___x_2233_);
lean_dec_ref(v_resOrders_2231_);
lean_dec(v___x_2228_);
v___x_2244_ = lean_apply_2(v_toPure_2229_, lean_box(0), v_acc_2240_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_array_2249_; lean_object* v_start_2250_; lean_object* v_stop_2251_; lean_object* v___f_2252_; lean_object* v___y_2254_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; uint8_t v___y_2283_; uint8_t v___x_2295_; 
lean_dec_ref(v_acc_2240_);
v___x_2245_ = lean_array_get_borrowed(v___x_2230_, v_resOrders_2231_, v_next_2239_);
v___x_2246_ = lean_array_get(v___x_2232_, v___x_2245_, v___x_2233_);
lean_inc_n(v_next_2239_, 2);
lean_inc(v___x_2233_);
lean_inc_ref(v_resOrders_2231_);
v___x_2247_ = l_Array_toSubarray___redArg(v_resOrders_2231_, v___x_2233_, v_next_2239_);
v___x_2248_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2249_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_array_2249_);
v_start_2250_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_start_2250_);
v_stop_2251_ = lean_ctor_get(v___x_2247_, 2);
lean_inc(v_stop_2251_);
lean_dec_ref(v___x_2247_);
lean_inc(v_toPure_2229_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2252_, 0, v_toPure_2229_);
lean_closure_set(v___f_2252_, 1, v_next_2239_);
lean_closure_set(v___f_2252_, 2, v_G_2242_);
lean_inc(v___x_2246_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2279_, 0, v___x_2246_);
v___x_2280_ = lean_box(v___x_2243_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2281_, 0, v___x_2280_);
lean_closure_set(v___f_2281_, 1, v___f_2279_);
v___x_2295_ = lean_nat_dec_lt(v_start_2250_, v_stop_2251_);
if (v___x_2295_ == 0)
{
lean_dec(v_stop_2251_);
lean_dec(v_start_2250_);
lean_dec_ref(v_array_2249_);
v___y_2283_ = v___x_2243_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___y_2299_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2296_ = lean_box(v___x_2243_);
lean_inc_ref(v___f_2281_);
v___f_2297_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2297_, 0, v___f_2281_);
lean_closure_set(v___f_2297_, 1, v___x_2296_);
v___x_2305_ = lean_array_get_size(v_array_2249_);
v___x_2306_ = lean_nat_dec_le(v_stop_2251_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec(v_stop_2251_);
v___y_2299_ = v___x_2305_;
goto v___jp_2298_;
}
else
{
v___y_2299_ = v_stop_2251_;
goto v___jp_2298_;
}
v___jp_2298_:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_nat_dec_lt(v_start_2250_, v___y_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v___y_2299_);
lean_dec_ref(v___f_2297_);
lean_dec(v_start_2250_);
lean_dec_ref(v_array_2249_);
v___y_2283_ = v___x_2295_;
goto v___jp_2282_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2301_ = lean_usize_of_nat(v_start_2250_);
lean_dec(v_start_2250_);
v___x_2302_ = lean_usize_of_nat(v___y_2299_);
lean_dec(v___y_2299_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2248_, v___f_2297_, v_array_2249_, v___x_2301_, v___x_2302_);
v___x_2304_ = lean_unbox(v___x_2303_);
lean_dec(v___x_2303_);
if (v___x_2304_ == 0)
{
v___y_2283_ = v___x_2300_;
goto v___jp_2282_;
}
else
{
lean_dec_ref(v___f_2281_);
lean_dec(v___x_2246_);
lean_dec(v_next_2239_);
lean_dec(v___x_2233_);
lean_dec_ref(v_resOrders_2231_);
lean_dec(v___x_2228_);
goto v___jp_2257_;
}
}
}
}
v___jp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_inc(v_toBind_2234_);
v___x_2255_ = lean_apply_4(v_toBind_2234_, lean_box(0), lean_box(0), v___y_2254_, v___f_2235_);
v___x_2256_ = lean_apply_4(v_toBind_2234_, lean_box(0), lean_box(0), v___x_2255_, v___f_2252_);
return v___x_2256_;
}
v___jp_2257_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2236_);
v___x_2259_ = lean_apply_2(v_toPure_2229_, lean_box(0), v___x_2258_);
v___y_2254_ = v___x_2259_;
goto v___jp_2253_;
}
v___jp_2260_:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2261_ = lean_nat_dec_eq(v_next_2237_, v___x_2233_);
lean_dec(v___x_2233_);
v___x_2262_ = lean_box(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2246_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2238_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = lean_apply_2(v_toPure_2229_, lean_box(0), v___x_2266_);
v___y_2254_ = v___x_2267_;
goto v___jp_2253_;
}
v___jp_2268_:
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_nat_dec_lt(v___y_2272_, v___y_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___x_2236_);
goto v___jp_2260_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2275_ = lean_usize_of_nat(v___y_2272_);
lean_dec(v___y_2272_);
v___x_2276_ = lean_usize_of_nat(v___y_2273_);
lean_dec(v___y_2273_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2270_, v___y_2269_, v___y_2271_, v___x_2275_, v___x_2276_);
v___x_2278_ = lean_unbox(v___x_2277_);
lean_dec(v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v___x_2236_);
goto v___jp_2260_;
}
else
{
lean_dec(v___x_2246_);
lean_dec(v___x_2233_);
goto v___jp_2257_;
}
}
}
v___jp_2282_:
{
if (v___y_2283_ == 0)
{
lean_dec_ref(v___f_2281_);
lean_dec(v___x_2246_);
lean_dec(v_next_2239_);
lean_dec(v___x_2233_);
lean_dec_ref(v_resOrders_2231_);
lean_dec(v___x_2228_);
goto v___jp_2257_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_array_2287_; lean_object* v_start_2288_; lean_object* v_stop_2289_; uint8_t v___x_2290_; 
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_next_2239_, v___x_2284_);
lean_dec(v_next_2239_);
v___x_2286_ = l_Array_toSubarray___redArg(v_resOrders_2231_, v___x_2285_, v___x_2228_);
v_array_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc_ref(v_array_2287_);
v_start_2288_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_start_2288_);
v_stop_2289_ = lean_ctor_get(v___x_2286_, 2);
lean_inc(v_stop_2289_);
lean_dec_ref(v___x_2286_);
v___x_2290_ = lean_nat_dec_lt(v_start_2288_, v_stop_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_stop_2289_);
lean_dec(v_start_2288_);
lean_dec_ref(v_array_2287_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v___x_2236_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2291_; lean_object* v___f_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2291_ = lean_box(v___y_2283_);
v___f_2292_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2292_, 0, v___f_2281_);
lean_closure_set(v___f_2292_, 1, v___x_2291_);
v___x_2293_ = lean_array_get_size(v_array_2287_);
v___x_2294_ = lean_nat_dec_le(v_stop_2289_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_dec(v_stop_2289_);
v___y_2269_ = v___f_2292_;
v___y_2270_ = v___x_2248_;
v___y_2271_ = v_array_2287_;
v___y_2272_ = v_start_2288_;
v___y_2273_ = v___x_2293_;
goto v___jp_2268_;
}
else
{
v___y_2269_ = v___f_2292_;
v___y_2270_ = v___x_2248_;
v___y_2271_ = v_array_2287_;
v___y_2272_ = v_start_2288_;
v___y_2273_ = v_stop_2289_;
goto v___jp_2268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2307_, lean_object* v_toPure_2308_, lean_object* v___x_2309_, lean_object* v_resOrders_2310_, lean_object* v___x_2311_, lean_object* v___x_2312_, lean_object* v_toBind_2313_, lean_object* v___f_2314_, lean_object* v___x_2315_, lean_object* v_next_2316_, lean_object* v___x_2317_, lean_object* v_next_2318_, lean_object* v_acc_2319_, lean_object* v_h_2320_, lean_object* v_G_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2307_, v_toPure_2308_, v___x_2309_, v_resOrders_2310_, v___x_2311_, v___x_2312_, v_toBind_2313_, v___f_2314_, v___x_2315_, v_next_2316_, v___x_2317_, v_next_2318_, v_acc_2319_, v_h_2320_, v_G_2321_);
lean_dec(v_next_2316_);
lean_dec(v___x_2311_);
lean_dec_ref(v___x_2309_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2323_, lean_object* v_toPure_2324_, lean_object* v___x_2325_, lean_object* v_resOrders_2326_, lean_object* v___x_2327_, lean_object* v___x_2328_, lean_object* v_toBind_2329_, lean_object* v___f_2330_, lean_object* v___x_2331_, lean_object* v___x_2332_, lean_object* v___f_2333_, lean_object* v___f_2334_, lean_object* v_next_2335_, lean_object* v_acc_2336_, lean_object* v_h_2337_, lean_object* v_G_2338_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_nat_dec_lt(v_next_2335_, v___x_2323_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_G_2338_);
lean_dec(v_next_2335_);
lean_dec(v___f_2334_);
lean_dec(v___f_2333_);
lean_dec_ref(v___x_2331_);
lean_dec(v___f_2330_);
lean_dec(v_toBind_2329_);
lean_dec(v___x_2328_);
lean_dec(v___x_2327_);
lean_dec_ref(v_resOrders_2326_);
lean_dec_ref(v___x_2325_);
v___x_2340_ = lean_apply_2(v_toPure_2324_, lean_box(0), v_acc_2336_);
return v___x_2340_;
}
else
{
lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref(v_acc_2336_);
lean_inc(v_next_2335_);
lean_inc(v_toPure_2324_);
v___f_2341_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2341_, 0, v_toPure_2324_);
lean_closure_set(v___f_2341_, 1, v_next_2335_);
lean_closure_set(v___f_2341_, 2, v_G_2338_);
v___x_2342_ = lean_nat_sub(v___x_2323_, v_next_2335_);
lean_inc_ref(v___x_2331_);
lean_inc_n(v_toBind_2329_, 3);
lean_inc(v___x_2328_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2343_, 0, v___x_2342_);
lean_closure_set(v___f_2343_, 1, v_toPure_2324_);
lean_closure_set(v___f_2343_, 2, v___x_2325_);
lean_closure_set(v___f_2343_, 3, v_resOrders_2326_);
lean_closure_set(v___f_2343_, 4, v___x_2327_);
lean_closure_set(v___f_2343_, 5, v___x_2328_);
lean_closure_set(v___f_2343_, 6, v_toBind_2329_);
lean_closure_set(v___f_2343_, 7, v___f_2330_);
lean_closure_set(v___f_2343_, 8, v___x_2331_);
lean_closure_set(v___f_2343_, 9, v_next_2335_);
lean_closure_set(v___f_2343_, 10, v___x_2332_);
v___x_2344_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2343_, v___x_2328_, v___x_2331_, lean_box(0));
v___x_2345_ = lean_apply_4(v_toBind_2329_, lean_box(0), lean_box(0), v___x_2344_, v___f_2333_);
v___x_2346_ = lean_apply_4(v_toBind_2329_, lean_box(0), lean_box(0), v___x_2345_, v___f_2334_);
v___x_2347_ = lean_apply_4(v_toBind_2329_, lean_box(0), lean_box(0), v___x_2346_, v___f_2341_);
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2348_, lean_object* v_toPure_2349_, lean_object* v___x_2350_, lean_object* v_resOrders_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v_toBind_2354_, lean_object* v___f_2355_, lean_object* v___x_2356_, lean_object* v___x_2357_, lean_object* v___f_2358_, lean_object* v___f_2359_, lean_object* v_next_2360_, lean_object* v_acc_2361_, lean_object* v_h_2362_, lean_object* v_G_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2348_, v_toPure_2349_, v___x_2350_, v_resOrders_2351_, v___x_2352_, v___x_2353_, v_toBind_2354_, v___f_2355_, v___x_2356_, v___x_2357_, v___f_2358_, v___f_2359_, v_next_2360_, v_acc_2361_, v_h_2362_, v_G_2363_);
lean_dec(v___x_2348_);
return v_res_2364_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Array_instInhabited(lean_box(0));
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2369_, lean_object* v_resOrders_2370_){
_start:
{
lean_object* v_toApplicative_2371_; lean_object* v_toBind_2372_; lean_object* v_toPure_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_toApplicative_2371_ = lean_ctor_get(v_inst_2369_, 0);
lean_inc_ref(v_toApplicative_2371_);
v_toBind_2372_ = lean_ctor_get(v_inst_2369_, 1);
lean_inc_n(v_toBind_2372_, 2);
lean_dec_ref(v_inst_2369_);
v_toPure_2373_ = lean_ctor_get(v_toApplicative_2371_, 1);
lean_inc_n(v_toPure_2373_, 4);
lean_dec_ref(v_toApplicative_2371_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2376_ = lean_array_get_size(v_resOrders_2370_);
lean_inc_ref(v_resOrders_2370_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2377_, 0, v___x_2375_);
lean_closure_set(v___f_2377_, 1, v_resOrders_2370_);
lean_closure_set(v___f_2377_, 2, v___x_2374_);
lean_closure_set(v___f_2377_, 3, v_toPure_2373_);
v___f_2378_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2378_, 0, v_toPure_2373_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_box(0);
v___x_2381_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2382_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2382_, 0, v___x_2381_);
lean_closure_set(v___f_2382_, 1, v_toPure_2373_);
lean_closure_set(v___f_2382_, 2, v___x_2380_);
lean_inc_ref(v___f_2378_);
v___f_2383_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2383_, 0, v___x_2376_);
lean_closure_set(v___f_2383_, 1, v_toPure_2373_);
lean_closure_set(v___f_2383_, 2, v___x_2375_);
lean_closure_set(v___f_2383_, 3, v_resOrders_2370_);
lean_closure_set(v___f_2383_, 4, v___x_2374_);
lean_closure_set(v___f_2383_, 5, v___x_2379_);
lean_closure_set(v___f_2383_, 6, v_toBind_2372_);
lean_closure_set(v___f_2383_, 7, v___f_2378_);
lean_closure_set(v___f_2383_, 8, v___x_2381_);
lean_closure_set(v___f_2383_, 9, v___x_2380_);
lean_closure_set(v___f_2383_, 10, v___f_2382_);
lean_closure_set(v___f_2383_, 11, v___f_2378_);
v___x_2384_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2383_, v___x_2379_, v___x_2381_, lean_box(0));
v___x_2385_ = lean_apply_4(v_toBind_2372_, lean_box(0), lean_box(0), v___x_2384_, v___f_2377_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2386_, lean_object* v_inst_2387_, lean_object* v_resOrders_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2387_, v_resOrders_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2390_){
_start:
{
lean_object* v_structName_2391_; 
v_structName_2391_ = lean_ctor_get(v_x_2390_, 0);
lean_inc(v_structName_2391_);
return v_structName_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2392_);
lean_dec_ref(v_x_2392_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2394_, lean_object* v_result_2395_, lean_object* v_____r_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_apply_2(v_toPure_2394_, lean_box(0), v_result_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2398_, lean_object* v_inst_2399_, lean_object* v_structName_2400_, lean_object* v_toBind_2401_, lean_object* v_result_2402_){
_start:
{
lean_object* v_resolutionOrder_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_resolutionOrder_2403_ = lean_ctor_get(v_result_2402_, 0);
lean_inc_ref(v_resolutionOrder_2403_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2404_, 0, v_toPure_2398_);
lean_closure_set(v___f_2404_, 1, v_result_2402_);
v___x_2405_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2399_, v_structName_2400_, v_resolutionOrder_2403_);
v___x_2406_ = lean_apply_4(v_toBind_2401_, lean_box(0), lean_box(0), v___x_2405_, v___f_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2407_, lean_object* v_____s_2408_){
_start:
{
lean_object* v_snd_2409_; lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_snd_2409_ = lean_ctor_get(v_____s_2408_, 1);
lean_inc(v_snd_2409_);
lean_dec_ref(v_____s_2408_);
v_fst_2410_ = lean_ctor_get(v_snd_2409_, 0);
v_snd_2411_ = lean_ctor_get(v_snd_2409_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_snd_2409_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2413_ = v_snd_2409_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snd_2411_);
lean_inc(v_fst_2410_);
lean_dec(v_snd_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_fst_2410_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2411_);
v___x_2416_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_apply_2(v_toPure_2407_, lean_box(0), v___x_2416_);
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2420_, lean_object* v_parentNames_2421_, lean_object* v_x_2422_){
_start:
{
uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_inc(v_x_2422_);
v___x_2423_ = l_Array_contains___redArg(v___x_2420_, v_parentNames_2421_, v_x_2422_);
v___x_2424_ = lean_box(v___x_2423_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v_x_2422_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2426_, lean_object* v___f_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2429_ = lean_array_get_size(v_x_2428_);
v___x_2430_ = lean_mk_empty_array_with_capacity(v___x_2426_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2432_ = lean_nat_dec_lt(v___x_2426_, v___x_2429_);
if (v___x_2432_ == 0)
{
lean_dec_ref(v_x_2428_);
lean_dec_ref(v___f_2427_);
return v___x_2430_;
}
else
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_nat_dec_le(v___x_2429_, v___x_2429_);
if (v___x_2433_ == 0)
{
if (v___x_2432_ == 0)
{
lean_dec_ref(v_x_2428_);
lean_dec_ref(v___f_2427_);
return v___x_2430_;
}
else
{
size_t v___x_2434_; size_t v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((size_t)0ULL);
v___x_2435_ = lean_usize_of_nat(v___x_2429_);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2431_, v___f_2427_, v_x_2428_, v___x_2434_, v___x_2435_, v___x_2430_);
return v___x_2436_;
}
}
else
{
size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = ((size_t)0ULL);
v___x_2438_ = lean_usize_of_nat(v___x_2429_);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2431_, v___f_2427_, v_x_2428_, v___x_2437_, v___x_2438_, v___x_2430_);
return v___x_2439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v___x_2440_, lean_object* v___f_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v___x_2440_, v___f_2441_, v_x_2442_);
lean_dec(v___x_2440_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v_snd_2444_, lean_object* v_x1_2445_, lean_object* v_x2_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_name_eq(v_x2_2446_, v_snd_2444_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_array_push(v_x1_2445_, v_x2_2446_);
return v___x_2448_;
}
else
{
lean_dec(v_x2_2446_);
return v_x1_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v_snd_2449_, lean_object* v_x1_2450_, lean_object* v_x2_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v_snd_2449_, v_x1_2450_, v_x2_2451_);
lean_dec(v_snd_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2453_, lean_object* v___f_2454_, lean_object* v_x1_2455_, lean_object* v_x2_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_array_2460_; lean_object* v_start_2461_; lean_object* v_stop_2462_; lean_object* v___y_2464_; uint8_t v___x_2471_; 
v___x_2457_ = lean_array_get_size(v_x2_2456_);
lean_inc_ref(v_x2_2456_);
v___x_2458_ = l_Array_toSubarray___redArg(v_x2_2456_, v___x_2453_, v___x_2457_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2460_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_array_2460_);
v_start_2461_ = lean_ctor_get(v___x_2458_, 1);
lean_inc(v_start_2461_);
v_stop_2462_ = lean_ctor_get(v___x_2458_, 2);
lean_inc(v_stop_2462_);
lean_dec_ref(v___x_2458_);
v___x_2471_ = lean_nat_dec_lt(v_start_2461_, v_stop_2462_);
if (v___x_2471_ == 0)
{
lean_dec(v_stop_2462_);
lean_dec(v_start_2461_);
lean_dec_ref(v_array_2460_);
lean_dec_ref(v_x2_2456_);
lean_dec_ref(v___f_2454_);
return v_x1_2455_;
}
else
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = lean_array_get_size(v_array_2460_);
v___x_2473_ = lean_nat_dec_le(v_stop_2462_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec(v_stop_2462_);
v___y_2464_ = v___x_2472_;
goto v___jp_2463_;
}
else
{
v___y_2464_ = v_stop_2462_;
goto v___jp_2463_;
}
}
v___jp_2463_:
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_start_2461_, v___y_2464_);
if (v___x_2465_ == 0)
{
lean_dec(v___y_2464_);
lean_dec(v_start_2461_);
lean_dec_ref(v_array_2460_);
lean_dec_ref(v_x2_2456_);
lean_dec_ref(v___f_2454_);
return v_x1_2455_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2466_ = lean_usize_of_nat(v_start_2461_);
lean_dec(v_start_2461_);
v___x_2467_ = lean_usize_of_nat(v___y_2464_);
lean_dec(v___y_2464_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2459_, v___f_2454_, v_array_2460_, v___x_2466_, v___x_2467_);
v___x_2469_ = lean_unbox(v___x_2468_);
lean_dec(v___x_2468_);
if (v___x_2469_ == 0)
{
lean_dec_ref(v_x2_2456_);
return v_x1_2455_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_array_push(v_x1_2455_, v_x2_2456_);
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2474_, lean_object* v_x_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_name_eq(v_x_2475_, v_snd_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2477_, lean_object* v_x_2478_){
_start:
{
uint8_t v_res_2479_; lean_object* v_r_2480_; 
v_res_2479_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2477_, v_x_2478_);
lean_dec(v_x_2478_);
lean_dec(v_snd_2477_);
v_r_2480_ = lean_box(v_res_2479_);
return v_r_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2482_, lean_object* v___x_2483_, lean_object* v_fst_2484_, lean_object* v_fst_2485_, lean_object* v___f_2486_, uint8_t v_relaxed_2487_, lean_object* v_parentNames_2488_, lean_object* v_snd_2489_, lean_object* v___f_2490_, lean_object* v___x_2491_, lean_object* v_____x_2492_){
_start:
{
lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v_fst_2501_; lean_object* v_snd_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v_defects_2506_; uint8_t v___x_2520_; 
v_fst_2501_ = lean_ctor_get(v_____x_2492_, 0);
lean_inc(v_fst_2501_);
v_snd_2502_ = lean_ctor_get(v_____x_2492_, 1);
lean_inc_n(v_snd_2502_, 2);
lean_dec_ref(v_____x_2492_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2503_, 0, v_snd_2502_);
lean_inc(v___x_2483_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2504_, 0, v___x_2483_);
lean_closure_set(v___f_2504_, 1, v___f_2503_);
v___x_2520_ = lean_unbox(v_fst_2501_);
lean_dec(v_fst_2501_);
if (v___x_2520_ == 0)
{
if (v_relaxed_2487_ == 0)
{
lean_object* v___x_2521_; lean_object* v___f_2522_; lean_object* v___y_2524_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2548_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2521_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2488_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9), 3, 2);
lean_closure_set(v___f_2522_, 0, v___x_2521_);
lean_closure_set(v___f_2522_, 1, v_parentNames_2488_);
v___x_2558_ = lean_array_get_size(v_fst_2485_);
v___x_2559_ = lean_mk_empty_array_with_capacity(v___x_2483_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2561_ = lean_nat_dec_lt(v___x_2483_, v___x_2558_);
if (v___x_2561_ == 0)
{
v___y_2548_ = v___x_2559_;
goto v___jp_2547_;
}
else
{
lean_object* v___f_2562_; lean_object* v___f_2563_; uint8_t v___x_2564_; 
lean_inc(v_snd_2502_);
v___f_2562_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2562_, 0, v_snd_2502_);
lean_inc(v___x_2491_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2563_, 0, v___x_2491_);
lean_closure_set(v___f_2563_, 1, v___f_2562_);
v___x_2564_ = lean_nat_dec_le(v___x_2558_, v___x_2558_);
if (v___x_2564_ == 0)
{
if (v___x_2561_ == 0)
{
lean_dec_ref(v___f_2563_);
v___y_2548_ = v___x_2559_;
goto v___jp_2547_;
}
else
{
size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = lean_usize_of_nat(v___x_2558_);
lean_inc(v_fst_2485_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2560_, v___f_2563_, v_fst_2485_, v___x_2565_, v___x_2566_, v___x_2559_);
v___y_2548_ = v___x_2567_;
goto v___jp_2547_;
}
}
else
{
size_t v___x_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = lean_usize_of_nat(v___x_2558_);
lean_inc(v_fst_2485_);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2560_, v___f_2563_, v_fst_2485_, v___x_2568_, v___x_2569_, v___x_2559_);
v___y_2548_ = v___x_2570_;
goto v___jp_2547_;
}
}
v___jp_2523_:
{
lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; size_t v_sz_2528_; size_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2525_ = l_Array_eraseReps___redArg(v___x_2521_, v___y_2524_);
lean_inc_n(v_snd_2502_, 2);
v___x_2526_ = l_Array_contains___redArg(v___x_2521_, v_parentNames_2488_, v_snd_2502_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2528_ = lean_array_size(v___x_2525_);
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2527_, v___f_2522_, v_sz_2528_, v___x_2529_, v___x_2525_);
v___x_2531_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2531_, 0, v_snd_2502_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
lean_ctor_set_uint8(v___x_2531_, sizeof(void*)*2, v___x_2526_);
v___x_2532_ = lean_array_push(v_snd_2489_, v___x_2531_);
v_defects_2506_ = v___x_2532_;
goto v___jp_2505_;
}
v___jp_2533_:
{
lean_object* v___x_2539_; 
lean_inc_ref(v___y_2536_);
v___x_2539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2536_, v___y_2537_, v___y_2535_, v___y_2534_, v___y_2538_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
v___y_2524_ = v___x_2539_;
goto v___jp_2523_;
}
v___jp_2540_:
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_nat_dec_le(v___y_2545_, v___y_2541_);
if (v___x_2546_ == 0)
{
lean_dec(v___y_2541_);
lean_inc(v___y_2545_);
v___y_2534_ = v___y_2545_;
v___y_2535_ = v___y_2543_;
v___y_2536_ = v___y_2542_;
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2545_;
goto v___jp_2533_;
}
else
{
v___y_2534_ = v___y_2545_;
v___y_2535_ = v___y_2543_;
v___y_2536_ = v___y_2542_;
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2541_;
goto v___jp_2533_;
}
}
v___jp_2547_:
{
lean_object* v___x_2549_; size_t v_sz_2550_; size_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2549_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2550_ = lean_array_size(v___y_2548_);
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2549_, v___f_2490_, v_sz_2550_, v___x_2551_, v___y_2548_);
v___x_2553_ = lean_array_get_size(v___x_2552_);
v___x_2554_ = lean_nat_dec_eq(v___x_2553_, v___x_2483_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2555_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2556_ = lean_nat_sub(v___x_2553_, v___x_2491_);
lean_dec(v___x_2491_);
v___x_2557_ = lean_nat_dec_le(v___x_2483_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_inc(v___x_2556_);
v___y_2541_ = v___x_2556_;
v___y_2542_ = v___x_2555_;
v___y_2543_ = v___x_2552_;
v___y_2544_ = v___x_2553_;
v___y_2545_ = v___x_2556_;
goto v___jp_2540_;
}
else
{
lean_inc(v___x_2483_);
v___y_2541_ = v___x_2556_;
v___y_2542_ = v___x_2555_;
v___y_2543_ = v___x_2552_;
v___y_2544_ = v___x_2553_;
v___y_2545_ = v___x_2483_;
goto v___jp_2540_;
}
}
else
{
lean_dec(v___x_2491_);
v___y_2524_ = v___x_2552_;
goto v___jp_2523_;
}
}
}
else
{
lean_dec(v___x_2491_);
lean_dec_ref(v___f_2490_);
lean_dec_ref(v_parentNames_2488_);
v_defects_2506_ = v_snd_2489_;
goto v___jp_2505_;
}
}
else
{
lean_dec(v___x_2491_);
lean_dec_ref(v___f_2490_);
lean_dec_ref(v_parentNames_2488_);
v_defects_2506_ = v_snd_2489_;
goto v___jp_2505_;
}
v___jp_2493_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___y_2494_);
lean_ctor_set(v___x_2497_, 1, v___y_2495_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___y_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
v___x_2500_ = lean_apply_2(v_toPure_2482_, lean_box(0), v___x_2499_);
return v___x_2500_;
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; size_t v_sz_2509_; size_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2507_ = lean_array_push(v_fst_2484_, v_snd_2502_);
v___x_2508_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2509_ = lean_array_size(v_fst_2485_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2508_, v___f_2504_, v_sz_2509_, v___x_2510_, v_fst_2485_);
v___x_2512_ = lean_array_get_size(v___x_2511_);
v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2483_);
v___x_2514_ = lean_nat_dec_lt(v___x_2483_, v___x_2512_);
lean_dec(v___x_2483_);
if (v___x_2514_ == 0)
{
lean_dec(v___x_2511_);
lean_dec_ref(v___f_2486_);
v___y_2494_ = v___x_2507_;
v___y_2495_ = v_defects_2506_;
v___y_2496_ = v___x_2513_;
goto v___jp_2493_;
}
else
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_le(v___x_2512_, v___x_2512_);
if (v___x_2515_ == 0)
{
if (v___x_2514_ == 0)
{
lean_dec(v___x_2511_);
lean_dec_ref(v___f_2486_);
v___y_2494_ = v___x_2507_;
v___y_2495_ = v_defects_2506_;
v___y_2496_ = v___x_2513_;
goto v___jp_2493_;
}
else
{
size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_usize_of_nat(v___x_2512_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2508_, v___f_2486_, v___x_2511_, v___x_2510_, v___x_2516_, v___x_2513_);
v___y_2494_ = v___x_2507_;
v___y_2495_ = v_defects_2506_;
v___y_2496_ = v___x_2517_;
goto v___jp_2493_;
}
}
else
{
size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_usize_of_nat(v___x_2512_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2508_, v___f_2486_, v___x_2511_, v___x_2510_, v___x_2518_, v___x_2513_);
v___y_2494_ = v___x_2507_;
v___y_2495_ = v_defects_2506_;
v___y_2496_ = v___x_2519_;
goto v___jp_2493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2571_, lean_object* v___x_2572_, lean_object* v_fst_2573_, lean_object* v_fst_2574_, lean_object* v___f_2575_, lean_object* v_relaxed_2576_, lean_object* v_parentNames_2577_, lean_object* v_snd_2578_, lean_object* v___f_2579_, lean_object* v___x_2580_, lean_object* v_____x_2581_){
_start:
{
uint8_t v_relaxed_boxed_2582_; lean_object* v_res_2583_; 
v_relaxed_boxed_2582_ = lean_unbox(v_relaxed_2576_);
v_res_2583_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2571_, v___x_2572_, v_fst_2573_, v_fst_2574_, v___f_2575_, v_relaxed_boxed_2582_, v_parentNames_2577_, v_snd_2578_, v___f_2579_, v___x_2580_, v_____x_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2584_, lean_object* v_toPure_2585_, lean_object* v___f_2586_, uint8_t v_relaxed_2587_, lean_object* v_parentNames_2588_, lean_object* v___f_2589_, lean_object* v___x_2590_, lean_object* v_inst_2591_, lean_object* v_toBind_2592_, lean_object* v___f_2593_, lean_object* v_b_2594_){
_start:
{
lean_object* v_snd_2595_; lean_object* v_fst_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2622_; 
v_snd_2595_ = lean_ctor_get(v_b_2594_, 1);
v_fst_2596_ = lean_ctor_get(v_b_2594_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_b_2594_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2598_ = v_b_2594_;
v_isShared_2599_ = v_isSharedCheck_2622_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snd_2595_);
lean_inc(v_fst_2596_);
lean_dec(v_b_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2622_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2621_; 
v_fst_2600_ = lean_ctor_get(v_snd_2595_, 0);
v_snd_2601_ = lean_ctor_get(v_snd_2595_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_snd_2595_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2603_ = v_snd_2595_;
v_isShared_2604_ = v_isSharedCheck_2621_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_inc(v_fst_2600_);
lean_dec(v_snd_2595_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2621_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = lean_array_get_size(v_fst_2596_);
v___x_2606_ = lean_nat_dec_eq(v___x_2605_, v___x_2584_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_del_object(v___x_2603_);
lean_del_object(v___x_2598_);
v___x_2607_ = lean_box(v_relaxed_2587_);
lean_inc(v_fst_2596_);
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_2608_, 0, v_toPure_2585_);
lean_closure_set(v___f_2608_, 1, v___x_2584_);
lean_closure_set(v___f_2608_, 2, v_fst_2600_);
lean_closure_set(v___f_2608_, 3, v_fst_2596_);
lean_closure_set(v___f_2608_, 4, v___f_2586_);
lean_closure_set(v___f_2608_, 5, v___x_2607_);
lean_closure_set(v___f_2608_, 6, v_parentNames_2588_);
lean_closure_set(v___f_2608_, 7, v_snd_2601_);
lean_closure_set(v___f_2608_, 8, v___f_2589_);
lean_closure_set(v___f_2608_, 9, v___x_2590_);
v___x_2609_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2591_, v_fst_2596_);
lean_inc(v_toBind_2592_);
v___x_2610_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2609_, v___f_2608_);
v___x_2611_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2610_, v___f_2593_);
return v___x_2611_;
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref(v_inst_2591_);
lean_dec(v___x_2590_);
lean_dec_ref(v___f_2589_);
lean_dec_ref(v_parentNames_2588_);
lean_dec_ref(v___f_2586_);
lean_dec(v___x_2584_);
if (v_isShared_2604_ == 0)
{
v___x_2613_ = v___x_2603_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_fst_2600_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_snd_2601_);
v___x_2613_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2613_);
v___x_2615_ = v___x_2598_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fst_2596_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
v___x_2617_ = lean_apply_2(v_toPure_2585_, lean_box(0), v___x_2616_);
v___x_2618_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2617_, v___f_2593_);
return v___x_2618_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2623_, lean_object* v_toPure_2624_, lean_object* v___f_2625_, lean_object* v_relaxed_2626_, lean_object* v_parentNames_2627_, lean_object* v___f_2628_, lean_object* v___x_2629_, lean_object* v_inst_2630_, lean_object* v_toBind_2631_, lean_object* v___f_2632_, lean_object* v_b_2633_){
_start:
{
uint8_t v_relaxed_boxed_2634_; lean_object* v_res_2635_; 
v_relaxed_boxed_2634_ = lean_unbox(v_relaxed_2626_);
v_res_2635_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2623_, v_toPure_2624_, v___f_2625_, v_relaxed_boxed_2634_, v_parentNames_2627_, v___f_2628_, v___x_2629_, v_inst_2630_, v_toBind_2631_, v___f_2632_, v_b_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v___x_2636_, lean_object* v_x_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_array_get_borrowed(v___x_2638_, v_x_2637_, v___x_2636_);
lean_inc(v___x_2639_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v___x_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v___x_2640_, v_x_2641_);
lean_dec_ref(v_x_2641_);
lean_dec(v___x_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v_toPure_2647_, lean_object* v___f_2648_, uint8_t v_relaxed_2649_, lean_object* v_parentNames_2650_, lean_object* v_inst_2651_, lean_object* v_toBind_2652_, lean_object* v___f_2653_, lean_object* v_structName_2654_, lean_object* v___f_2655_, lean_object* v___f_2656_, lean_object* v_parentResOrders_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___f_2659_; lean_object* v___y_2661_; lean_object* v_j_2672_; lean_object* v_as_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2658_ = lean_unsigned_to_nat(0u);
v___f_2659_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v_j_2672_ = lean_array_get_size(v_parentResOrders_2657_);
lean_inc_ref(v_parentNames_2650_);
v_as_2673_ = lean_array_push(v_parentResOrders_2657_, v_parentNames_2650_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2658_, v_as_2673_, v_j_2672_);
v___x_2675_ = lean_array_get_size(v___x_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1));
v___x_2677_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2678_ = lean_nat_dec_lt(v___x_2658_, v___x_2675_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v___x_2674_);
lean_dec_ref(v___f_2656_);
v___y_2661_ = v___x_2676_;
goto v___jp_2660_;
}
else
{
uint8_t v___x_2679_; 
v___x_2679_ = lean_nat_dec_le(v___x_2675_, v___x_2675_);
if (v___x_2679_ == 0)
{
if (v___x_2678_ == 0)
{
lean_dec_ref(v___x_2674_);
lean_dec_ref(v___f_2656_);
v___y_2661_ = v___x_2676_;
goto v___jp_2660_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2675_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2677_, v___f_2656_, v___x_2674_, v___x_2680_, v___x_2681_, v___x_2676_);
v___y_2661_ = v___x_2682_;
goto v___jp_2660_;
}
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2675_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2677_, v___f_2656_, v___x_2674_, v___x_2683_, v___x_2684_, v___x_2676_);
v___y_2661_ = v___x_2685_;
goto v___jp_2660_;
}
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; lean_object* v_resOrder_2666_; lean_object* v_defects_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_box(v_relaxed_2649_);
lean_inc(v_toBind_2652_);
lean_inc_ref(v_inst_2651_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 11, 10);
lean_closure_set(v___f_2664_, 0, v___x_2658_);
lean_closure_set(v___f_2664_, 1, v_toPure_2647_);
lean_closure_set(v___f_2664_, 2, v___f_2648_);
lean_closure_set(v___f_2664_, 3, v___x_2663_);
lean_closure_set(v___f_2664_, 4, v_parentNames_2650_);
lean_closure_set(v___f_2664_, 5, v___f_2659_);
lean_closure_set(v___f_2664_, 6, v___x_2662_);
lean_closure_set(v___f_2664_, 7, v_inst_2651_);
lean_closure_set(v___f_2664_, 8, v_toBind_2652_);
lean_closure_set(v___f_2664_, 9, v___f_2653_);
v___x_2665_ = lean_mk_empty_array_with_capacity(v___x_2662_);
v_resOrder_2666_ = lean_array_push(v___x_2665_, v_structName_2654_);
v_defects_2667_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_resOrder_2666_);
lean_ctor_set(v___x_2668_, 1, v_defects_2667_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___y_2661_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2651_, v___f_2664_, v___x_2669_);
v___x_2671_ = lean_apply_4(v_toBind_2652_, lean_box(0), lean_box(0), v___x_2670_, v___f_2655_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v_toPure_2686_, lean_object* v___f_2687_, lean_object* v_relaxed_2688_, lean_object* v_parentNames_2689_, lean_object* v_inst_2690_, lean_object* v_toBind_2691_, lean_object* v___f_2692_, lean_object* v_structName_2693_, lean_object* v___f_2694_, lean_object* v___f_2695_, lean_object* v_parentResOrders_2696_){
_start:
{
uint8_t v_relaxed_boxed_2697_; lean_object* v_res_2698_; 
v_relaxed_boxed_2697_ = lean_unbox(v_relaxed_2688_);
v_res_2698_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v_toPure_2686_, v___f_2687_, v_relaxed_boxed_2697_, v_parentNames_2689_, v_inst_2690_, v_toBind_2691_, v___f_2692_, v_structName_2693_, v___f_2694_, v___f_2695_, v_parentResOrders_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2700_ = lean_array_get_size(v_x_2699_);
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_nat_dec_eq(v___x_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
uint8_t v___x_2703_; 
v___x_2703_ = 1;
return v___x_2703_;
}
else
{
uint8_t v___x_2704_; 
v___x_2704_ = 0;
return v___x_2704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2705_);
lean_dec_ref(v_x_2705_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2708_, lean_object* v_x1_2709_, lean_object* v_x2_2710_){
_start:
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
lean_inc_ref(v_x2_2710_);
v___x_2711_ = lean_apply_1(v___f_2708_, v_x2_2710_);
v___x_2712_ = lean_unbox(v___x_2711_);
if (v___x_2712_ == 0)
{
lean_dec_ref(v_x2_2710_);
return v_x1_2709_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_array_push(v_x1_2709_, v_x2_2710_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2714_, lean_object* v_____do__lift_2715_){
_start:
{
if (lean_obj_tag(v_____do__lift_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_a_2716_ = lean_ctor_get(v_____do__lift_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_____do__lift_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_____do__lift_2715_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v_____do__lift_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 1);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_apply_2(v_toPure_2714_, lean_box(0), v___x_2721_);
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
v_a_2725_ = lean_ctor_get(v_____do__lift_2715_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_____do__lift_2715_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2727_ = v_____do__lift_2715_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v_____do__lift_2715_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set_tag(v___x_2727_, 0);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_apply_2(v_toPure_2714_, lean_box(0), v___x_2730_);
return v___x_2731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2734_, lean_object* v_____do__lift_2735_){
_start:
{
lean_object* v_resolutionOrder_2736_; lean_object* v___x_2737_; 
v_resolutionOrder_2736_ = lean_ctor_get(v_____do__lift_2735_, 0);
lean_inc_ref(v_resolutionOrder_2736_);
lean_dec_ref(v_____do__lift_2735_);
v___x_2737_ = lean_apply_2(v_toPure_2734_, lean_box(0), v_resolutionOrder_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_structName_2744_, lean_object* v_parentNames_2745_, uint8_t v_relaxed_2746_){
_start:
{
lean_object* v_toApplicative_2747_; lean_object* v_toBind_2748_; lean_object* v_toPure_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v_toApplicative_2747_ = lean_ctor_get(v_inst_2742_, 0);
v_toBind_2748_ = lean_ctor_get(v_inst_2742_, 1);
lean_inc_n(v_toBind_2748_, 3);
v_toPure_2749_ = lean_ctor_get(v_toApplicative_2747_, 1);
v___f_2750_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc_n(v_toPure_2749_, 4);
v___f_2751_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2751_, 0, v_toPure_2749_);
lean_inc_ref_n(v_inst_2742_, 2);
v___f_2752_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2752_, 0, v_inst_2742_);
lean_closure_set(v___f_2752_, 1, v_inst_2743_);
lean_closure_set(v___f_2752_, 2, v_toBind_2748_);
lean_closure_set(v___f_2752_, 3, v___f_2751_);
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2753_, 0, v_toPure_2749_);
v___f_2754_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2754_, 0, v_toPure_2749_);
v___x_2755_ = lean_box(v_relaxed_2746_);
lean_inc_ref(v_parentNames_2745_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 11, 10);
lean_closure_set(v___f_2756_, 0, v_toPure_2749_);
lean_closure_set(v___f_2756_, 1, v___f_2750_);
lean_closure_set(v___f_2756_, 2, v___x_2755_);
lean_closure_set(v___f_2756_, 3, v_parentNames_2745_);
lean_closure_set(v___f_2756_, 4, v_inst_2742_);
lean_closure_set(v___f_2756_, 5, v_toBind_2748_);
lean_closure_set(v___f_2756_, 6, v___f_2753_);
lean_closure_set(v___f_2756_, 7, v_structName_2744_);
lean_closure_set(v___f_2756_, 8, v___f_2754_);
lean_closure_set(v___f_2756_, 9, v___f_2750_);
v_sz_2757_ = lean_array_size(v_parentNames_2745_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2742_, v___f_2752_, v_sz_2757_, v___x_2758_, v_parentNames_2745_);
v___x_2760_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2759_, v___f_2756_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2761_, lean_object* v_toPure_2762_, lean_object* v___f_2763_, lean_object* v_inst_2764_, lean_object* v_inst_2765_, uint8_t v_relaxed_2766_, lean_object* v_toBind_2767_, lean_object* v___f_2768_, lean_object* v_env_2769_){
_start:
{
lean_object* v___x_2770_; 
lean_inc_ref(v_env_2769_);
v___x_2770_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2769_, v_structName_2761_);
if (lean_obj_tag(v___x_2770_) == 1)
{
lean_object* v_val_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec_ref(v_env_2769_);
lean_dec(v___f_2768_);
lean_dec(v_toBind_2767_);
lean_dec_ref(v_inst_2765_);
lean_dec_ref(v_inst_2764_);
lean_dec_ref(v___f_2763_);
lean_dec(v_structName_2761_);
v_val_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_val_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_apply_2(v_toPure_2762_, lean_box(0), v___x_2773_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; size_t v_sz_2777_; size_t v___x_2778_; lean_object* v_parentNames_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v___x_2770_);
lean_dec(v_toPure_2762_);
lean_inc(v_structName_2761_);
v___x_2775_ = l_Lean_getStructureParentInfo(v_env_2769_, v_structName_2761_);
v___x_2776_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2777_ = lean_array_size(v___x_2775_);
v___x_2778_ = ((size_t)0ULL);
v_parentNames_2779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2776_, v___f_2763_, v_sz_2777_, v___x_2778_, v___x_2775_);
v___x_2780_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2764_, v_inst_2765_, v_structName_2761_, v_parentNames_2779_, v_relaxed_2766_);
v___x_2781_ = lean_apply_4(v_toBind_2767_, lean_box(0), lean_box(0), v___x_2780_, v___f_2768_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2782_, lean_object* v_toPure_2783_, lean_object* v___f_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_relaxed_2787_, lean_object* v_toBind_2788_, lean_object* v___f_2789_, lean_object* v_env_2790_){
_start:
{
uint8_t v_relaxed_boxed_2791_; lean_object* v_res_2792_; 
v_relaxed_boxed_2791_ = lean_unbox(v_relaxed_2787_);
v_res_2792_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2782_, v_toPure_2783_, v___f_2784_, v_inst_2785_, v_inst_2786_, v_relaxed_boxed_2791_, v_toBind_2788_, v___f_2789_, v_env_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2793_, lean_object* v_inst_2794_, lean_object* v_structName_2795_, uint8_t v_relaxed_2796_){
_start:
{
lean_object* v_toApplicative_2797_; lean_object* v_toBind_2798_; lean_object* v_getEnv_2799_; lean_object* v_toPure_2800_; lean_object* v___f_2801_; lean_object* v___f_2802_; lean_object* v___x_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; 
v_toApplicative_2797_ = lean_ctor_get(v_inst_2793_, 0);
v_toBind_2798_ = lean_ctor_get(v_inst_2793_, 1);
lean_inc_n(v_toBind_2798_, 3);
v_getEnv_2799_ = lean_ctor_get(v_inst_2794_, 0);
lean_inc(v_getEnv_2799_);
v_toPure_2800_ = lean_ctor_get(v_toApplicative_2797_, 1);
lean_inc_n(v_toPure_2800_, 2);
v___f_2801_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2795_);
lean_inc_ref(v_inst_2794_);
v___f_2802_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2802_, 0, v_toPure_2800_);
lean_closure_set(v___f_2802_, 1, v_inst_2794_);
lean_closure_set(v___f_2802_, 2, v_structName_2795_);
lean_closure_set(v___f_2802_, 3, v_toBind_2798_);
v___x_2803_ = lean_box(v_relaxed_2796_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2804_, 0, v_structName_2795_);
lean_closure_set(v___f_2804_, 1, v_toPure_2800_);
lean_closure_set(v___f_2804_, 2, v___f_2801_);
lean_closure_set(v___f_2804_, 3, v_inst_2793_);
lean_closure_set(v___f_2804_, 4, v_inst_2794_);
lean_closure_set(v___f_2804_, 5, v___x_2803_);
lean_closure_set(v___f_2804_, 6, v_toBind_2798_);
lean_closure_set(v___f_2804_, 7, v___f_2802_);
v___x_2805_ = lean_apply_4(v_toBind_2798_, lean_box(0), lean_box(0), v_getEnv_2799_, v___f_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2806_, lean_object* v_inst_2807_, lean_object* v_toBind_2808_, lean_object* v___f_2809_, lean_object* v_parentName_2810_){
_start:
{
uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = 1;
v___x_2812_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2806_, v_inst_2807_, v_parentName_2810_, v___x_2811_);
v___x_2813_ = lean_apply_4(v_toBind_2808_, lean_box(0), lean_box(0), v___x_2812_, v___f_2809_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_structName_2816_, lean_object* v_relaxed_2817_){
_start:
{
uint8_t v_relaxed_boxed_2818_; lean_object* v_res_2819_; 
v_relaxed_boxed_2818_ = lean_unbox(v_relaxed_2817_);
v_res_2819_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2814_, v_inst_2815_, v_structName_2816_, v_relaxed_boxed_2818_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_structName_2822_, lean_object* v_parentNames_2823_, lean_object* v_relaxed_2824_){
_start:
{
uint8_t v_relaxed_boxed_2825_; lean_object* v_res_2826_; 
v_relaxed_boxed_2825_ = lean_unbox(v_relaxed_2824_);
v_res_2826_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2820_, v_inst_2821_, v_structName_2822_, v_parentNames_2823_, v_relaxed_boxed_2825_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_structName_2830_, uint8_t v_relaxed_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2828_, v_inst_2829_, v_structName_2830_, v_relaxed_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_structName_2836_, lean_object* v_relaxed_2837_){
_start:
{
uint8_t v_relaxed_boxed_2838_; lean_object* v_res_2839_; 
v_relaxed_boxed_2838_ = lean_unbox(v_relaxed_2837_);
v_res_2839_ = l_Lean_computeStructureResolutionOrder(v_m_2833_, v_inst_2834_, v_inst_2835_, v_structName_2836_, v_relaxed_boxed_2838_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_structName_2843_, lean_object* v_parentNames_2844_, uint8_t v_relaxed_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2841_, v_inst_2842_, v_structName_2843_, v_parentNames_2844_, v_relaxed_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_structName_2850_, lean_object* v_parentNames_2851_, lean_object* v_relaxed_2852_){
_start:
{
uint8_t v_relaxed_boxed_2853_; lean_object* v_res_2854_; 
v_relaxed_boxed_2853_ = lean_unbox(v_relaxed_2852_);
v_res_2854_ = l_Lean_mergeStructureResolutionOrders(v_m_2847_, v_inst_2848_, v_inst_2849_, v_structName_2850_, v_parentNames_2851_, v_relaxed_boxed_2853_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2855_){
_start:
{
lean_object* v_resolutionOrder_2856_; 
v_resolutionOrder_2856_ = lean_ctor_get(v_x_2855_, 0);
lean_inc_ref(v_resolutionOrder_2856_);
return v_resolutionOrder_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2857_);
lean_dec_ref(v_x_2857_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_structName_2862_){
_start:
{
lean_object* v_toApplicative_2863_; lean_object* v_toFunctor_2864_; lean_object* v_map_2865_; lean_object* v___f_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_toApplicative_2863_ = lean_ctor_get(v_inst_2860_, 0);
v_toFunctor_2864_ = lean_ctor_get(v_toApplicative_2863_, 0);
v_map_2865_ = lean_ctor_get(v_toFunctor_2864_, 0);
lean_inc(v_map_2865_);
v___f_2866_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2867_ = 1;
v___x_2868_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2860_, v_inst_2861_, v_structName_2862_, v___x_2867_);
v___x_2869_ = lean_apply_4(v_map_2865_, lean_box(0), lean_box(0), v___f_2866_, v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_structName_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2871_, v_inst_2872_, v_structName_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2875_, lean_object* v_structName_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Array_erase___redArg(v___x_2875_, v_x_2877_, v_structName_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_structName_2881_){
_start:
{
lean_object* v_toApplicative_2882_; lean_object* v_toFunctor_2883_; lean_object* v_map_2884_; lean_object* v___x_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2879_, 0);
v_toFunctor_2883_ = lean_ctor_get(v_toApplicative_2882_, 0);
v_map_2884_ = lean_ctor_get(v_toFunctor_2883_, 0);
lean_inc(v_map_2884_);
v___x_2885_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2881_);
v___f_2886_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2886_, 0, v___x_2885_);
lean_closure_set(v___f_2886_, 1, v_structName_2881_);
v___x_2887_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2879_, v_inst_2880_, v_structName_2881_);
v___x_2888_ = lean_apply_4(v_map_2884_, lean_box(0), lean_box(0), v___f_2886_, v___x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_structName_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_getAllParentStructures___redArg(v_inst_2890_, v_inst_2891_, v_structName_2892_);
return v___x_2893_;
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
res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Structure_0__Lean_structureExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Structure_0__Lean_structureExt);
lean_dec_ref(res);
l_Lean_instInhabitedStructureResolutionState_default = _init_l_Lean_instInhabitedStructureResolutionState_default();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState_default);
l_Lean_instInhabitedStructureResolutionState = _init_l_Lean_instInhabitedStructureResolutionState();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState);
res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
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
