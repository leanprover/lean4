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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; uint8_t v___y_197_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_eq(v_m_188_, v___x_193_);
v___x_195_ = lean_nat_sub(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
if (v___x_194_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_lt(v___x_195_, v_x_184_);
v___y_197_ = v___x_200_;
goto v___jp_196_;
}
else
{
v___y_197_ = v___x_194_;
goto v___jp_196_;
}
v___jp_196_:
{
if (v___y_197_ == 0)
{
v_x_185_ = v___x_195_;
goto _start;
}
else
{
lean_object* v___x_199_; 
lean_dec(v___x_195_);
lean_dec(v_x_184_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
}
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec(v_x_184_);
v___x_201_ = lean_nat_add(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
v___x_202_ = lean_nat_dec_le(v___x_201_, v_x_185_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec(v___x_201_);
lean_dec(v_x_185_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
v_x_184_ = v___x_201_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object* v_as_205_, lean_object* v_k_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_205_, v_k_206_, v_x_207_, v_x_208_);
lean_dec_ref(v_k_206_);
lean_dec_ref(v_as_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object* v_info_210_, lean_object* v_i_211_){
_start:
{
lean_object* v_fieldNames_212_; lean_object* v_fieldInfo_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_fieldNames_212_ = lean_ctor_get(v_info_210_, 1);
v_fieldInfo_213_ = lean_ctor_get(v_info_210_, 2);
v___x_214_ = lean_array_get_size(v_fieldNames_212_);
v___x_215_ = lean_nat_dec_lt(v_i_211_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v_fieldInfo_213_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_sub(v___x_218_, v___x_221_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_nat_dec_le(v___x_217_, v___x_222_);
if (v___x_224_ == 0)
{
lean_dec(v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_fieldName_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_fieldName_225_ = lean_array_fget_borrowed(v_fieldNames_212_, v_i_211_);
v___x_226_ = lean_box(0);
v___x_227_ = 0;
lean_inc(v_fieldName_225_);
v___x_228_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_228_, 0, v_fieldName_225_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_223_);
lean_ctor_set(v___x_228_, 3, v___x_223_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*4, v___x_227_);
v___x_229_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_213_, v___x_228_, v___x_217_, v___x_222_);
lean_dec_ref_known(v___x_228_, 4);
if (lean_obj_tag(v___x_229_) == 0)
{
return v___x_223_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_238_; 
v_val_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_238_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_val_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_projFn_234_; lean_object* v___x_236_; 
v_projFn_234_ = lean_ctor_get(v_val_230_, 1);
lean_inc(v_projFn_234_);
lean_dec(v_val_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v_projFn_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_projFn_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object* v_info_239_, lean_object* v_i_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_StructureInfo_getProjFn_x3f(v_info_239_, v_i_240_);
lean_dec(v_i_240_);
lean_dec_ref(v_info_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object* v_as_242_, lean_object* v_k_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_242_, v_k_243_, v_x_244_, v_x_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object* v_as_248_, lean_object* v_k_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(v_as_248_, v_k_249_, v_x_250_, v_x_251_, v_x_252_);
lean_dec_ref(v_k_249_);
lean_dec_ref(v_as_248_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__0(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_254_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureState_default(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_instInhabitedStructureState_default;
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v_x_261_);
lean_dec_ref(v_x_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t v_sz_263_, size_t v_i_264_, lean_object* v_bs_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_266_ == 0)
{
return v_bs_265_;
}
else
{
lean_object* v_v_267_; lean_object* v_snd_268_; lean_object* v___x_269_; lean_object* v_bs_x27_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v_v_267_ = lean_array_uget_borrowed(v_bs_265_, v_i_264_);
v_snd_268_ = lean_ctor_get(v_v_267_, 1);
lean_inc(v_snd_268_);
v___x_269_ = lean_unsigned_to_nat(0u);
v_bs_x27_270_ = lean_array_uset(v_bs_265_, v_i_264_, v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_264_, v___x_271_);
v___x_273_ = lean_array_uset(v_bs_x27_270_, v_i_264_, v_snd_268_);
v_i_264_ = v___x_272_;
v_bs_265_ = v___x_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_bs_277_){
_start:
{
size_t v_sz_boxed_278_; size_t v_i_boxed_279_; lean_object* v_res_280_; 
v_sz_boxed_278_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_279_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_boxed_278_, v_i_boxed_279_, v_bs_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_ps_281_, lean_object* v_k_282_, lean_object* v_v_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_k_282_);
lean_ctor_set(v___x_284_, 1, v_v_283_);
v___x_285_ = lean_array_push(v_ps_281_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_f_286_, lean_object* v_keys_287_, lean_object* v_vals_288_, lean_object* v_i_289_, lean_object* v_acc_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_keys_287_);
v___x_292_ = lean_nat_dec_lt(v_i_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec(v_i_289_);
lean_dec(v_f_286_);
return v_acc_290_;
}
else
{
lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_k_293_ = lean_array_fget_borrowed(v_keys_287_, v_i_289_);
v_v_294_ = lean_array_fget_borrowed(v_vals_288_, v_i_289_);
lean_inc(v_f_286_);
lean_inc(v_v_294_);
lean_inc(v_k_293_);
v___x_295_ = lean_apply_3(v_f_286_, v_acc_290_, v_k_293_, v_v_294_);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_289_, v___x_296_);
lean_dec(v_i_289_);
v_i_289_ = v___x_297_;
v_acc_290_ = v___x_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_f_299_, lean_object* v_keys_300_, lean_object* v_vals_301_, lean_object* v_i_302_, lean_object* v_acc_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_299_, v_keys_300_, v_vals_301_, v_i_302_, v_acc_303_);
lean_dec_ref(v_vals_301_);
lean_dec_ref(v_keys_300_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_305_, lean_object* v_as_306_, size_t v_i_307_, size_t v_stop_308_, lean_object* v_b_309_){
_start:
{
lean_object* v___y_311_; uint8_t v___x_315_; 
v___x_315_ = lean_usize_dec_eq(v_i_307_, v_stop_308_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_array_uget_borrowed(v_as_306_, v_i_307_);
switch(lean_obj_tag(v___x_316_))
{
case 0:
{
lean_object* v_key_317_; lean_object* v_val_318_; lean_object* v___x_319_; 
v_key_317_ = lean_ctor_get(v___x_316_, 0);
v_val_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_f_305_);
lean_inc(v_val_318_);
lean_inc(v_key_317_);
v___x_319_ = lean_apply_3(v_f_305_, v_b_309_, v_key_317_, v_val_318_);
v___y_311_ = v___x_319_;
goto v___jp_310_;
}
case 1:
{
lean_object* v_node_320_; lean_object* v___x_321_; 
v_node_320_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_f_305_);
v___x_321_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_305_, v_node_320_, v_b_309_);
v___y_311_ = v___x_321_;
goto v___jp_310_;
}
default: 
{
v___y_311_ = v_b_309_;
goto v___jp_310_;
}
}
}
else
{
lean_dec(v_f_305_);
return v_b_309_;
}
v___jp_310_:
{
size_t v___x_312_; size_t v___x_313_; 
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_i_307_, v___x_312_);
v_i_307_ = v___x_313_;
v_b_309_ = v___y_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_es_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_es_325_ = lean_ctor_get(v_x_323_, 0);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v_es_325_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec(v_f_322_);
return v_x_324_;
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_327_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_322_, v_es_325_, v___x_329_, v___x_330_, v_x_324_);
return v___x_331_;
}
}
else
{
lean_object* v_ks_332_; lean_object* v_vs_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_ks_332_ = lean_ctor_get(v_x_323_, 0);
v_vs_333_ = lean_ctor_get(v_x_323_, 1);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_322_, v_ks_332_, v_vs_333_, v___x_334_, v_x_324_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_336_, v_x_337_, v_x_338_);
lean_dec_ref(v_x_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_340_, lean_object* v_as_341_, lean_object* v_i_342_, lean_object* v_stop_343_, lean_object* v_b_344_){
_start:
{
size_t v_i_boxed_345_; size_t v_stop_boxed_346_; lean_object* v_res_347_; 
v_i_boxed_345_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_stop_boxed_346_ = lean_unbox_usize(v_stop_343_);
lean_dec(v_stop_343_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_340_, v_as_341_, v_i_boxed_345_, v_stop_boxed_346_, v_b_344_);
lean_dec_ref(v_as_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object* v_f_348_, lean_object* v_x1_349_, lean_object* v_x2_350_, lean_object* v_x3_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_3(v_f_348_, v_x1_349_, v_x2_350_, v_x3_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_353_, lean_object* v_f_354_, lean_object* v_init_355_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; 
v___f_356_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_356_, 0, v_f_354_);
v___x_357_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_356_, v_map_353_, v_init_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_358_, lean_object* v_f_359_, lean_object* v_init_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_358_, v_f_359_, v_init_360_);
lean_dec_ref(v_map_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_365_){
_start:
{
lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___f_366_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_367_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1));
v___x_368_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_365_, v___f_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_369_);
lean_dec_ref(v_m_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_371_, lean_object* v_pivot_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_k_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v_k_375_, v_hi_371_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_k_375_);
v___x_377_ = lean_array_fswap(v_as_373_, v_i_374_, v_hi_371_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_i_374_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_array_fget_borrowed(v_as_373_, v_k_375_);
v___x_380_ = l_Lean_StructureInfo_lt(v___x_379_, v_pivot_372_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_k_375_, v___x_381_);
lean_dec(v_k_375_);
v_k_375_ = v___x_382_;
goto _start;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_array_fswap(v_as_373_, v_i_374_, v_k_375_);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_i_374_, v___x_385_);
lean_dec(v_i_374_);
v___x_387_ = lean_nat_add(v_k_375_, v___x_385_);
lean_dec(v_k_375_);
v_as_373_ = v___x_384_;
v_i_374_ = v___x_386_;
v_k_375_ = v___x_387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_389_, lean_object* v_pivot_390_, lean_object* v_as_391_, lean_object* v_i_392_, lean_object* v_k_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_389_, v_pivot_390_, v_as_391_, v_i_392_, v_k_393_);
lean_dec_ref(v_pivot_390_);
lean_dec(v_hi_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_395_, lean_object* v_as_396_, lean_object* v_lo_397_, lean_object* v_hi_398_){
_start:
{
lean_object* v___y_400_; uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_lo_397_, v_hi_398_);
if (v___x_410_ == 0)
{
lean_dec(v_lo_397_);
return v_as_396_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_mid_413_; lean_object* v___y_415_; lean_object* v___y_421_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_411_ = lean_nat_add(v_lo_397_, v_hi_398_);
v___x_412_ = lean_unsigned_to_nat(1u);
v_mid_413_ = lean_nat_shiftr(v___x_411_, v___x_412_);
lean_dec(v___x_411_);
v___x_426_ = lean_array_fget_borrowed(v_as_396_, v_mid_413_);
v___x_427_ = lean_array_fget_borrowed(v_as_396_, v_lo_397_);
v___x_428_ = l_Lean_StructureInfo_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
v___y_421_ = v_as_396_;
goto v___jp_420_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_array_fswap(v_as_396_, v_lo_397_, v_mid_413_);
v___y_421_ = v___x_429_;
goto v___jp_420_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_array_fget_borrowed(v___y_415_, v_mid_413_);
v___x_417_ = lean_array_fget_borrowed(v___y_415_, v_hi_398_);
v___x_418_ = l_Lean_StructureInfo_lt(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_dec(v_mid_413_);
v___y_400_ = v___y_415_;
goto v___jp_399_;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = lean_array_fswap(v___y_415_, v_mid_413_, v_hi_398_);
lean_dec(v_mid_413_);
v___y_400_ = v___x_419_;
goto v___jp_399_;
}
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_array_fget_borrowed(v___y_421_, v_hi_398_);
v___x_423_ = lean_array_fget_borrowed(v___y_421_, v_lo_397_);
v___x_424_ = l_Lean_StructureInfo_lt(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
v___y_415_ = v___y_421_;
goto v___jp_414_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_array_fswap(v___y_421_, v_lo_397_, v_hi_398_);
v___y_415_ = v___x_425_;
goto v___jp_414_;
}
}
}
v___jp_399_:
{
lean_object* v_pivot_401_; lean_object* v___x_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; uint8_t v___x_405_; 
v_pivot_401_ = lean_array_fget(v___y_400_, v_hi_398_);
lean_inc_n(v_lo_397_, 2);
v___x_402_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_398_, v_pivot_401_, v___y_400_, v_lo_397_, v_lo_397_);
lean_dec(v_pivot_401_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v___x_402_);
v___x_405_ = lean_nat_dec_le(v_hi_398_, v_fst_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_395_, v_snd_404_, v_lo_397_, v_fst_403_);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_fst_403_, v___x_407_);
lean_dec(v_fst_403_);
v_as_396_ = v___x_406_;
v_lo_397_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v_fst_403_);
lean_dec(v_lo_397_);
return v_snd_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_430_, lean_object* v_as_431_, lean_object* v_lo_432_, lean_object* v_hi_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_430_, v_as_431_, v_lo_432_, v_hi_433_);
lean_dec(v_hi_433_);
lean_dec(v_n_430_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_435_, lean_object* v_x_436_, lean_object* v_s_437_){
_start:
{
lean_object* v_snd_438_; lean_object* v___x_439_; size_t v_sz_440_; size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___x_449_; 
v_snd_438_ = lean_ctor_get(v_s_437_, 1);
v___x_439_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_438_);
v_sz_440_ = lean_array_size(v___x_439_);
v___x_441_ = ((size_t)0ULL);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_440_, v___x_441_, v___x_439_);
v___x_443_ = lean_array_get_size(v___x_442_);
v___x_449_ = lean_nat_dec_eq(v___x_443_, v___x_435_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___y_453_; uint8_t v___x_455_; 
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_sub(v___x_443_, v___x_450_);
v___x_455_ = lean_nat_dec_le(v___x_435_, v___x_451_);
if (v___x_455_ == 0)
{
lean_dec(v___x_435_);
lean_inc(v___x_451_);
v___y_453_ = v___x_451_;
goto v___jp_452_;
}
else
{
v___y_453_ = v___x_435_;
goto v___jp_452_;
}
v___jp_452_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_le(v___y_453_, v___x_451_);
if (v___x_454_ == 0)
{
lean_dec(v___x_451_);
lean_inc(v___y_453_);
v___y_445_ = v___y_453_;
v___y_446_ = v___y_453_;
goto v___jp_444_;
}
else
{
v___y_445_ = v___y_453_;
v___y_446_ = v___x_451_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v___x_435_);
lean_inc_ref_n(v___x_442_, 2);
v___x_456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_456_, 0, v___x_442_);
lean_ctor_set(v___x_456_, 1, v___x_442_);
lean_ctor_set(v___x_456_, 2, v___x_442_);
return v___x_456_;
}
v___jp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_443_, v___x_442_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_inc_ref_n(v___x_447_, 2);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_ctor_set(v___x_448_, 2, v___x_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_457_, lean_object* v_x_458_, lean_object* v_s_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_457_, v_x_458_, v_s_459_);
lean_dec_ref(v_s_459_);
lean_dec_ref(v_x_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_snd_463_; lean_object* v___x_464_; size_t v_sz_465_; size_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_snd_463_ = lean_ctor_get(v_x_462_, 1);
v___x_464_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_463_);
v_sz_465_ = lean_array_size(v___x_464_);
v___x_466_ = ((size_t)0ULL);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_465_, v___x_466_, v___x_464_);
v___x_468_ = lean_array_get_size(v___x_467_);
v___x_469_ = lean_nat_dec_eq(v___x_468_, v___x_461_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___y_473_; uint8_t v___x_477_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_sub(v___x_468_, v___x_470_);
v___x_477_ = lean_nat_dec_le(v___x_461_, v___x_471_);
if (v___x_477_ == 0)
{
lean_dec(v___x_461_);
lean_inc(v___x_471_);
v___y_473_ = v___x_471_;
goto v___jp_472_;
}
else
{
v___y_473_ = v___x_461_;
goto v___jp_472_;
}
v___jp_472_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_le(v___y_473_, v___x_471_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_dec(v___x_471_);
lean_inc(v___y_473_);
v___x_475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_468_, v___x_467_, v___y_473_, v___y_473_);
lean_dec(v___y_473_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_468_, v___x_467_, v___y_473_, v___x_471_);
lean_dec(v___x_471_);
return v___x_476_;
}
}
}
else
{
lean_dec(v___x_461_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_478_, v_x_479_);
lean_dec_ref(v_x_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_ks_485_; lean_object* v_vs_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_510_; 
v_ks_485_ = lean_ctor_get(v_x_481_, 0);
v_vs_486_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_510_ == 0)
{
v___x_488_ = v_x_481_;
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_vs_486_);
lean_inc(v_ks_485_);
lean_dec(v_x_481_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_ks_485_);
v___x_491_ = lean_nat_dec_lt(v_x_482_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v_x_482_);
v___x_492_ = lean_array_push(v_ks_485_, v_x_483_);
v___x_493_ = lean_array_push(v_vs_486_, v_x_484_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_493_);
lean_ctor_set(v___x_488_, 0, v___x_492_);
v___x_495_ = v___x_488_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v_k_x27_497_; uint8_t v___x_498_; 
v_k_x27_497_ = lean_array_fget_borrowed(v_ks_485_, v_x_482_);
v___x_498_ = lean_name_eq(v_x_483_, v_k_x27_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_500_; 
if (v_isShared_489_ == 0)
{
v___x_500_ = v___x_488_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_ks_485_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_vs_486_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_x_482_, v___x_501_);
lean_dec(v_x_482_);
v_x_481_ = v___x_500_;
v_x_482_ = v___x_502_;
goto _start;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = lean_array_fset(v_ks_485_, v_x_482_, v_x_483_);
v___x_506_ = lean_array_fset(v_vs_486_, v_x_482_, v_x_484_);
lean_dec(v_x_482_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_506_);
lean_ctor_set(v___x_488_, 0, v___x_505_);
v___x_508_ = v___x_488_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_n_511_, lean_object* v_k_512_, lean_object* v_v_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_n_511_, v___x_514_, v_k_512_, v_v_513_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_517_, size_t v_x_518_, size_t v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_es_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v_j_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_es_522_ = lean_ctor_get(v_x_517_, 0);
v___x_523_ = ((size_t)31ULL);
v___x_524_ = lean_usize_land(v_x_518_, v___x_523_);
v_j_525_ = lean_usize_to_nat(v___x_524_);
v___x_526_ = lean_array_get_size(v_es_522_);
v___x_527_ = lean_nat_dec_lt(v_j_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v_j_525_);
lean_dec(v_x_521_);
lean_dec(v_x_520_);
return v_x_517_;
}
else
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_566_; 
lean_inc_ref(v_es_522_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_x_517_, 0);
lean_dec(v_unused_567_);
v___x_529_ = v_x_517_;
v_isShared_530_ = v_isSharedCheck_566_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_x_517_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_566_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_v_531_; lean_object* v___x_532_; lean_object* v_xs_x27_533_; lean_object* v___y_535_; 
v_v_531_ = lean_array_fget(v_es_522_, v_j_525_);
v___x_532_ = lean_box(0);
v_xs_x27_533_ = lean_array_fset(v_es_522_, v_j_525_, v___x_532_);
switch(lean_obj_tag(v_v_531_))
{
case 0:
{
lean_object* v_key_540_; lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_551_; 
v_key_540_ = lean_ctor_get(v_v_531_, 0);
v_val_541_ = lean_ctor_get(v_v_531_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_v_531_);
if (v_isSharedCheck_551_ == 0)
{
v___x_543_ = v_v_531_;
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_inc(v_key_540_);
lean_dec(v_v_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
uint8_t v___x_545_; 
v___x_545_ = lean_name_eq(v_x_520_, v_key_540_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_del_object(v___x_543_);
v___x_546_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_540_, v_val_541_, v_x_520_, v_x_521_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___y_535_ = v___x_547_;
goto v___jp_534_;
}
else
{
lean_object* v___x_549_; 
lean_dec(v_val_541_);
lean_dec(v_key_540_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_x_521_);
lean_ctor_set(v___x_543_, 0, v_x_520_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_x_520_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_x_521_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
v___y_535_ = v___x_549_;
goto v___jp_534_;
}
}
}
}
case 1:
{
lean_object* v_node_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_564_; 
v_node_552_ = lean_ctor_get(v_v_531_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_v_531_);
if (v_isSharedCheck_564_ == 0)
{
v___x_554_ = v_v_531_;
v_isShared_555_ = v_isSharedCheck_564_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_node_552_);
lean_dec(v_v_531_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_564_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_556_ = ((size_t)5ULL);
v___x_557_ = lean_usize_shift_right(v_x_518_, v___x_556_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_x_519_, v___x_558_);
v___x_560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_552_, v___x_557_, v___x_559_, v_x_520_, v_x_521_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_560_);
v___x_562_ = v___x_554_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_535_ = v___x_562_;
goto v___jp_534_;
}
}
}
default: 
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_x_520_);
lean_ctor_set(v___x_565_, 1, v_x_521_);
v___y_535_ = v___x_565_;
goto v___jp_534_;
}
}
v___jp_534_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_fset(v_xs_x27_533_, v_j_525_, v___y_535_);
lean_dec(v_j_525_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_536_);
v___x_538_ = v___x_529_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v_ks_568_; lean_object* v_vs_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_587_; 
v_ks_568_ = lean_ctor_get(v_x_517_, 0);
v_vs_569_ = lean_ctor_get(v_x_517_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_587_ == 0)
{
v___x_571_ = v_x_517_;
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_vs_569_);
lean_inc(v_ks_568_);
lean_dec(v_x_517_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_ks_568_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_vs_569_);
v___x_574_ = v_reuseFailAlloc_586_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v_newNode_575_; size_t v___x_576_; uint8_t v___x_577_; 
v_newNode_575_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_574_, v_x_520_, v_x_521_);
v___x_576_ = ((size_t)7ULL);
v___x_577_ = lean_usize_dec_le(v___x_576_, v_x_519_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_575_);
v___x_579_ = lean_unsigned_to_nat(4u);
v___x_580_ = lean_nat_dec_lt(v___x_578_, v___x_579_);
lean_dec(v___x_578_);
if (v___x_580_ == 0)
{
lean_object* v_ks_581_; lean_object* v_vs_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_ks_581_ = lean_ctor_get(v_newNode_575_, 0);
lean_inc_ref(v_ks_581_);
v_vs_582_ = lean_ctor_get(v_newNode_575_, 1);
lean_inc_ref(v_vs_582_);
lean_dec_ref(v_newNode_575_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_519_, v_ks_581_, v_vs_582_, v___x_583_, v___x_584_);
lean_dec_ref(v_vs_582_);
lean_dec_ref(v_ks_581_);
return v___x_585_;
}
else
{
return v_newNode_575_;
}
}
else
{
return v_newNode_575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_i_591_, lean_object* v_entries_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_keys_589_);
v___x_594_ = lean_nat_dec_lt(v_i_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_i_591_);
return v_entries_592_;
}
else
{
lean_object* v_k_595_; lean_object* v_v_596_; uint64_t v___y_598_; 
v_k_595_ = lean_array_fget_borrowed(v_keys_589_, v_i_591_);
v_v_596_ = lean_array_fget_borrowed(v_vals_590_, v_i_591_);
if (lean_obj_tag(v_k_595_) == 0)
{
uint64_t v___x_609_; 
v___x_609_ = 1723ULL;
v___y_598_ = v___x_609_;
goto v___jp_597_;
}
else
{
uint64_t v_hash_610_; 
v_hash_610_ = lean_ctor_get_uint64(v_k_595_, sizeof(void*)*2);
v___y_598_ = v_hash_610_;
goto v___jp_597_;
}
v___jp_597_:
{
size_t v_h_599_; size_t v___x_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v_h_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_h_599_ = lean_uint64_to_usize(v___y_598_);
v___x_600_ = ((size_t)5ULL);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_sub(v_depth_588_, v___x_602_);
v___x_604_ = lean_usize_mul(v___x_600_, v___x_603_);
v_h_605_ = lean_usize_shift_right(v_h_599_, v___x_604_);
v___x_606_ = lean_nat_add(v_i_591_, v___x_601_);
lean_dec(v_i_591_);
lean_inc(v_v_596_);
lean_inc(v_k_595_);
v___x_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_592_, v_h_605_, v_depth_588_, v_k_595_, v_v_596_);
v_i_591_ = v___x_606_;
v_entries_592_ = v___x_607_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_i_614_, lean_object* v_entries_615_){
_start:
{
size_t v_depth_boxed_616_; lean_object* v_res_617_; 
v_depth_boxed_616_ = lean_unbox_usize(v_depth_611_);
lean_dec(v_depth_611_);
v_res_617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_616_, v_keys_612_, v_vals_613_, v_i_614_, v_entries_615_);
lean_dec_ref(v_vals_613_);
lean_dec_ref(v_keys_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
size_t v_x_1794__boxed_623_; size_t v_x_1795__boxed_624_; lean_object* v_res_625_; 
v_x_1794__boxed_623_ = lean_unbox_usize(v_x_619_);
lean_dec(v_x_619_);
v_x_1795__boxed_624_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_res_625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_618_, v_x_1794__boxed_623_, v_x_1795__boxed_624_, v_x_621_, v_x_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
uint64_t v___y_630_; 
if (lean_obj_tag(v_x_627_) == 0)
{
uint64_t v___x_634_; 
v___x_634_ = 1723ULL;
v___y_630_ = v___x_634_;
goto v___jp_629_;
}
else
{
uint64_t v_hash_635_; 
v_hash_635_ = lean_ctor_get_uint64(v_x_627_, sizeof(void*)*2);
v___y_630_ = v_hash_635_;
goto v___jp_629_;
}
v___jp_629_:
{
size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_uint64_to_usize(v___y_630_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_626_, v___x_631_, v___x_632_, v_x_627_, v_x_628_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_636_, lean_object* v_x_637_, lean_object* v_e_638_){
_start:
{
lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_648_; 
v_snd_639_ = lean_ctor_get(v_x_637_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_x_637_, 0);
lean_dec(v_unused_649_);
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_structName_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v_structName_643_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_structName_643_);
v___x_644_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_639_, v_structName_643_, v_e_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_644_);
lean_ctor_set(v___x_641_, 0, v___x_636_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_656_, lean_object* v_x_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_656_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_661_, v_x_662_, v___y_663_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v_x_662_);
return v_res_665_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_698_; lean_object* v___f_699_; 
v___x_698_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_699_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_699_, 0, v___x_698_);
return v___f_699_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_700_; lean_object* v___f_701_; 
v___x_700_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_701_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_701_, 0, v___x_700_);
return v___f_701_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_box(2);
v___f_704_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_705_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_706_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_707_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_708_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_709_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_710_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___f_708_);
lean_ctor_set(v___x_710_, 2, v___f_707_);
lean_ctor_set(v___x_710_, 3, v___f_706_);
lean_ctor_set(v___x_710_, 4, v___f_705_);
lean_ctor_set(v___x_710_, 5, v___f_704_);
lean_ctor_set(v___x_710_, 6, v___x_703_);
lean_ctor_set(v___x_710_, 7, v___x_702_);
return v___x_710_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___f_711_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_712_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___f_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_716_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_719_, lean_object* v_m_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_722_, lean_object* v_m_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_722_, v_m_723_);
lean_dec_ref(v_m_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_725_, lean_object* v_as_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_w_729_, lean_object* v_hlo_730_, lean_object* v_hhi_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_725_, v_as_726_, v_lo_727_, v_hi_728_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_733_, lean_object* v_as_734_, lean_object* v_lo_735_, lean_object* v_hi_736_, lean_object* v_w_737_, lean_object* v_hlo_738_, lean_object* v_hhi_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_733_, v_as_734_, v_lo_735_, v_hi_736_, v_w_737_, v_hlo_738_, v_hhi_739_);
lean_dec(v_hi_736_);
lean_dec(v_n_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_742_, v_x_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_746_, lean_object* v_00_u03b2_747_, lean_object* v_map_748_, lean_object* v_f_749_, lean_object* v_init_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_748_, v_f_749_, v_init_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_752_, lean_object* v_00_u03b2_753_, lean_object* v_map_754_, lean_object* v_f_755_, lean_object* v_init_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_752_, v_00_u03b2_753_, v_map_754_, v_f_755_, v_init_756_);
lean_dec_ref(v_map_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_758_, lean_object* v_lo_759_, lean_object* v_hi_760_, lean_object* v_hhi_761_, lean_object* v_pivot_762_, lean_object* v_as_763_, lean_object* v_i_764_, lean_object* v_k_765_, lean_object* v_ilo_766_, lean_object* v_ik_767_, lean_object* v_w_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_760_, v_pivot_762_, v_as_763_, v_i_764_, v_k_765_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_770_, lean_object* v_lo_771_, lean_object* v_hi_772_, lean_object* v_hhi_773_, lean_object* v_pivot_774_, lean_object* v_as_775_, lean_object* v_i_776_, lean_object* v_k_777_, lean_object* v_ilo_778_, lean_object* v_ik_779_, lean_object* v_w_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_770_, v_lo_771_, v_hi_772_, v_hhi_773_, v_pivot_774_, v_as_775_, v_i_776_, v_k_777_, v_ilo_778_, v_ik_779_, v_w_780_);
lean_dec_ref(v_pivot_774_);
lean_dec(v_hi_772_);
lean_dec(v_lo_771_);
lean_dec(v_n_770_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, size_t v_x_784_, size_t v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_783_, v_x_784_, v_x_785_, v_x_786_, v_x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
size_t v_x_2182__boxed_795_; size_t v_x_2183__boxed_796_; lean_object* v_res_797_; 
v_x_2182__boxed_795_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_x_2183__boxed_796_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_res_797_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_789_, v_x_790_, v_x_2182__boxed_795_, v_x_2183__boxed_796_, v_x_793_, v_x_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_798_, lean_object* v_f_799_, lean_object* v_init_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_799_, v_map_798_, v_init_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_802_, lean_object* v_f_803_, lean_object* v_init_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_802_, v_f_803_, v_init_804_);
lean_dec_ref(v_map_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_806_, lean_object* v_00_u03b2_807_, lean_object* v_map_808_, lean_object* v_f_809_, lean_object* v_init_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_809_, v_map_808_, v_init_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_812_, lean_object* v_00_u03b2_813_, lean_object* v_map_814_, lean_object* v_f_815_, lean_object* v_init_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_812_, v_00_u03b2_813_, v_map_814_, v_f_815_, v_init_816_);
lean_dec_ref(v_map_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_818_, lean_object* v_n_819_, lean_object* v_k_820_, lean_object* v_v_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_819_, v_k_820_, v_v_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_823_, size_t v_depth_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_824_, v_keys_825_, v_vals_826_, v_i_828_, v_entries_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_831_, lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_heq_835_, lean_object* v_i_836_, lean_object* v_entries_837_){
_start:
{
size_t v_depth_boxed_838_; lean_object* v_res_839_; 
v_depth_boxed_838_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_831_, v_depth_boxed_838_, v_keys_833_, v_vals_834_, v_heq_835_, v_i_836_, v_entries_837_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_840_, lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_f_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_843_, v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_847_, lean_object* v_00_u03b1_848_, lean_object* v_00_u03b2_849_, lean_object* v_f_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_847_, v_00_u03b1_848_, v_00_u03b2_849_, v_f_850_, v_x_851_, v_x_852_);
lean_dec_ref(v_x_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_855_, v_x_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_00_u03c3_862_, lean_object* v_f_863_, lean_object* v_as_864_, size_t v_i_865_, size_t v_stop_866_, lean_object* v_b_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_863_, v_as_864_, v_i_865_, v_stop_866_, v_b_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_00_u03c3_871_, lean_object* v_f_872_, lean_object* v_as_873_, lean_object* v_i_874_, lean_object* v_stop_875_, lean_object* v_b_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; lean_object* v_res_879_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_875_);
lean_dec(v_stop_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_869_, v_00_u03b2_870_, v_00_u03c3_871_, v_f_872_, v_as_873_, v_i_boxed_877_, v_stop_boxed_878_, v_b_876_);
lean_dec_ref(v_as_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_880_, lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_f_883_, lean_object* v_keys_884_, lean_object* v_vals_885_, lean_object* v_heq_886_, lean_object* v_i_887_, lean_object* v_acc_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_883_, v_keys_884_, v_vals_885_, v_i_887_, v_acc_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_890_, lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_f_893_, lean_object* v_keys_894_, lean_object* v_vals_895_, lean_object* v_heq_896_, lean_object* v_i_897_, lean_object* v_acc_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_890_, v_00_u03b1_891_, v_00_u03b2_892_, v_f_893_, v_keys_894_, v_vals_895_, v_heq_896_, v_i_897_, v_acc_898_);
lean_dec_ref(v_vals_895_);
lean_dec_ref(v_keys_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_907_, size_t v_i_908_, lean_object* v_bs_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_908_, v_sz_907_);
if (v___x_910_ == 0)
{
return v_bs_909_;
}
else
{
lean_object* v_v_911_; lean_object* v_fieldName_912_; lean_object* v___x_913_; lean_object* v_bs_x27_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_v_911_ = lean_array_uget_borrowed(v_bs_909_, v_i_908_);
v_fieldName_912_ = lean_ctor_get(v_v_911_, 0);
lean_inc(v_fieldName_912_);
v___x_913_ = lean_unsigned_to_nat(0u);
v_bs_x27_914_ = lean_array_uset(v_bs_909_, v_i_908_, v___x_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_908_, v___x_915_);
v___x_917_ = lean_array_uset(v_bs_x27_914_, v_i_908_, v_fieldName_912_);
v_i_908_ = v___x_916_;
v_bs_909_ = v___x_917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_bs_921_){
_start:
{
size_t v_sz_boxed_922_; size_t v_i_boxed_923_; lean_object* v_res_924_; 
v_sz_boxed_922_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_923_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_922_, v_i_boxed_923_, v_bs_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object* v_hi_925_, lean_object* v_pivot_926_, lean_object* v_as_927_, lean_object* v_i_928_, lean_object* v_k_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_lt(v_k_929_, v_hi_925_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_k_929_);
v___x_931_ = lean_array_fswap(v_as_927_, v_i_928_, v_hi_925_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_i_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_fget_borrowed(v_as_927_, v_k_929_);
v___x_934_ = l_Lean_StructureFieldInfo_lt(v___x_933_, v_pivot_926_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_add(v_k_929_, v___x_935_);
lean_dec(v_k_929_);
v_k_929_ = v___x_936_;
goto _start;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_array_fswap(v_as_927_, v_i_928_, v_k_929_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_i_928_, v___x_939_);
lean_dec(v_i_928_);
v___x_941_ = lean_nat_add(v_k_929_, v___x_939_);
lean_dec(v_k_929_);
v_as_927_ = v___x_938_;
v_i_928_ = v___x_940_;
v_k_929_ = v___x_941_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object* v_hi_943_, lean_object* v_pivot_944_, lean_object* v_as_945_, lean_object* v_i_946_, lean_object* v_k_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_943_, v_pivot_944_, v_as_945_, v_i_946_, v_k_947_);
lean_dec_ref(v_pivot_944_);
lean_dec(v_hi_943_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_n_949_, lean_object* v_as_950_, lean_object* v_lo_951_, lean_object* v_hi_952_){
_start:
{
lean_object* v___y_954_; uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_lt(v_lo_951_, v_hi_952_);
if (v___x_964_ == 0)
{
lean_dec(v_lo_951_);
return v_as_950_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_mid_967_; lean_object* v___y_969_; lean_object* v___y_975_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_965_ = lean_nat_add(v_lo_951_, v_hi_952_);
v___x_966_ = lean_unsigned_to_nat(1u);
v_mid_967_ = lean_nat_shiftr(v___x_965_, v___x_966_);
lean_dec(v___x_965_);
v___x_980_ = lean_array_fget_borrowed(v_as_950_, v_mid_967_);
v___x_981_ = lean_array_fget_borrowed(v_as_950_, v_lo_951_);
v___x_982_ = l_Lean_StructureFieldInfo_lt(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
v___y_975_ = v_as_950_;
goto v___jp_974_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_array_fswap(v_as_950_, v_lo_951_, v_mid_967_);
v___y_975_ = v___x_983_;
goto v___jp_974_;
}
v___jp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_970_ = lean_array_fget_borrowed(v___y_969_, v_mid_967_);
v___x_971_ = lean_array_fget_borrowed(v___y_969_, v_hi_952_);
v___x_972_ = l_Lean_StructureFieldInfo_lt(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_dec(v_mid_967_);
v___y_954_ = v___y_969_;
goto v___jp_953_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_array_fswap(v___y_969_, v_mid_967_, v_hi_952_);
lean_dec(v_mid_967_);
v___y_954_ = v___x_973_;
goto v___jp_953_;
}
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_array_fget_borrowed(v___y_975_, v_hi_952_);
v___x_977_ = lean_array_fget_borrowed(v___y_975_, v_lo_951_);
v___x_978_ = l_Lean_StructureFieldInfo_lt(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
v___y_969_ = v___y_975_;
goto v___jp_968_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = lean_array_fswap(v___y_975_, v_lo_951_, v_hi_952_);
v___y_969_ = v___x_979_;
goto v___jp_968_;
}
}
}
v___jp_953_:
{
lean_object* v_pivot_955_; lean_object* v___x_956_; lean_object* v_fst_957_; lean_object* v_snd_958_; uint8_t v___x_959_; 
v_pivot_955_ = lean_array_fget(v___y_954_, v_hi_952_);
lean_inc_n(v_lo_951_, 2);
v___x_956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_952_, v_pivot_955_, v___y_954_, v_lo_951_, v_lo_951_);
lean_dec(v_pivot_955_);
v_fst_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_fst_957_);
v_snd_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_snd_958_);
lean_dec_ref(v___x_956_);
v___x_959_ = lean_nat_dec_le(v_hi_952_, v_fst_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_949_, v_snd_958_, v_lo_951_, v_fst_957_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_fst_957_, v___x_961_);
lean_dec(v_fst_957_);
v_as_950_ = v___x_960_;
v_lo_951_ = v___x_962_;
goto _start;
}
else
{
lean_dec(v_fst_957_);
lean_dec(v_lo_951_);
return v_snd_958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_n_984_, lean_object* v_as_985_, lean_object* v_lo_986_, lean_object* v_hi_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_984_, v_as_985_, v_lo_986_, v_hi_987_);
lean_dec(v_hi_987_);
lean_dec(v_n_984_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_991_, lean_object* v_e_992_){
_start:
{
lean_object* v_structName_993_; lean_object* v_fields_994_; lean_object* v___x_995_; size_t v_sz_996_; size_t v___x_997_; lean_object* v___x_998_; lean_object* v___y_1000_; lean_object* v___x_1007_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_structName_993_ = lean_ctor_get(v_e_992_, 0);
lean_inc(v_structName_993_);
v_fields_994_ = lean_ctor_get(v_e_992_, 1);
lean_inc_ref_n(v_fields_994_, 2);
lean_dec_ref(v_e_992_);
v___x_995_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_996_ = lean_array_size(v_fields_994_);
v___x_997_ = ((size_t)0ULL);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_996_, v___x_997_, v_fields_994_);
v___x_1007_ = lean_array_get_size(v_fields_994_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_nat_dec_eq(v___x_1007_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___y_1017_; uint8_t v___x_1019_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_sub(v___x_1007_, v___x_1014_);
v___x_1019_ = lean_nat_dec_le(v___x_1012_, v___x_1015_);
if (v___x_1019_ == 0)
{
lean_inc(v___x_1015_);
v___y_1017_ = v___x_1015_;
goto v___jp_1016_;
}
else
{
v___y_1017_ = v___x_1012_;
goto v___jp_1016_;
}
v___jp_1016_:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_le(v___y_1017_, v___x_1015_);
if (v___x_1018_ == 0)
{
lean_dec(v___x_1015_);
lean_inc(v___y_1017_);
v___y_1009_ = v___y_1017_;
v___y_1010_ = v___y_1017_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v___y_1017_;
v___y_1010_ = v___x_1015_;
goto v___jp_1008_;
}
}
}
else
{
v___y_1000_ = v_fields_994_;
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v_toEnvExtension_1001_; lean_object* v_asyncMode_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_toEnvExtension_1001_ = lean_ctor_get(v___x_995_, 0);
v_asyncMode_1002_ = lean_ctor_get(v_toEnvExtension_1001_, 2);
v___x_1003_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_1004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1004_, 0, v_structName_993_);
lean_ctor_set(v___x_1004_, 1, v___x_998_);
lean_ctor_set(v___x_1004_, 2, v___y_1000_);
lean_ctor_set(v___x_1004_, 3, v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_995_, v_env_991_, v___x_1004_, v_asyncMode_1002_, v___x_1005_);
return v___x_1006_;
}
v___jp_1008_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_1007_, v_fields_994_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
v___y_1000_ = v___x_1011_;
goto v___jp_999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_1020_, lean_object* v_as_1021_, lean_object* v_lo_1022_, lean_object* v_hi_1023_, lean_object* v_w_1024_, lean_object* v_hlo_1025_, lean_object* v_hhi_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_1020_, v_as_1021_, v_lo_1022_, v_hi_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_1028_, lean_object* v_as_1029_, lean_object* v_lo_1030_, lean_object* v_hi_1031_, lean_object* v_w_1032_, lean_object* v_hlo_1033_, lean_object* v_hhi_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_1028_, v_as_1029_, v_lo_1030_, v_hi_1031_, v_w_1032_, v_hlo_1033_, v_hhi_1034_);
lean_dec(v_hi_1031_);
lean_dec(v_n_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object* v_n_1036_, lean_object* v_lo_1037_, lean_object* v_hi_1038_, lean_object* v_hhi_1039_, lean_object* v_pivot_1040_, lean_object* v_as_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_, lean_object* v_ilo_1044_, lean_object* v_ik_1045_, lean_object* v_w_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_1038_, v_pivot_1040_, v_as_1041_, v_i_1042_, v_k_1043_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object* v_n_1048_, lean_object* v_lo_1049_, lean_object* v_hi_1050_, lean_object* v_hhi_1051_, lean_object* v_pivot_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_, lean_object* v_ilo_1056_, lean_object* v_ik_1057_, lean_object* v_w_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_1048_, v_lo_1049_, v_hi_1050_, v_hhi_1051_, v_pivot_1052_, v_as_1053_, v_i_1054_, v_k_1055_, v_ilo_1056_, v_ik_1057_, v_w_1058_);
lean_dec_ref(v_pivot_1052_);
lean_dec(v_hi_1050_);
lean_dec(v_lo_1049_);
lean_dec(v_n_1048_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_1060_, lean_object* v_parentInfo_1061_, lean_object* v___x_1062_, lean_object* v_asyncMode_1063_, lean_object* v___x_1064_, lean_object* v_env_1065_){
_start:
{
lean_object* v_structName_1066_; lean_object* v_fieldNames_1067_; lean_object* v_fieldInfo_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_structName_1066_ = lean_ctor_get(v_val_1060_, 0);
v_fieldNames_1067_ = lean_ctor_get(v_val_1060_, 1);
v_fieldInfo_1068_ = lean_ctor_get(v_val_1060_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_val_1060_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_val_1060_, 3);
lean_dec(v_unused_1077_);
v___x_1070_ = v_val_1060_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_fieldInfo_1068_);
lean_inc(v_fieldNames_1067_);
lean_inc(v_structName_1066_);
lean_dec(v_val_1060_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 3, v_parentInfo_1061_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_structName_1066_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_fieldNames_1067_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_fieldInfo_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_parentInfo_1061_);
v___x_1073_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1062_, v_env_1065_, v___x_1073_, v_asyncMode_1063_, v___x_1064_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_1078_, lean_object* v_parentInfo_1079_, lean_object* v___x_1080_, lean_object* v_asyncMode_1081_, lean_object* v___x_1082_, lean_object* v_env_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_setStructureParents___redArg___lam__0(v_val_1078_, v_parentInfo_1079_, v___x_1080_, v_asyncMode_1081_, v___x_1082_, v_env_1083_);
lean_dec(v_asyncMode_1081_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v_structName_1094_, lean_object* v_parentInfo_1095_, lean_object* v_modifyEnv_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_____do__lift_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v_toEnvExtension_1101_; lean_object* v_asyncMode_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_snd_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1121_; 
v___x_1100_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1101_ = lean_ctor_get(v___x_1100_, 0);
v_asyncMode_1102_ = lean_ctor_get(v_toEnvExtension_1101_, 2);
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1091_, v___x_1100_, v_____do__lift_1099_, v_asyncMode_1102_, v___x_1103_);
v_snd_1105_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v___x_1104_, 0);
lean_dec(v_unused_1122_);
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1121_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_snd_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1121_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; 
lean_inc(v_structName_1094_);
v___x_1109_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1092_, v___x_1093_, v_snd_1105_, v_structName_1094_);
lean_dec(v_snd_1105_);
if (lean_obj_tag(v___x_1109_) == 1)
{
lean_object* v_val_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
lean_del_object(v___x_1107_);
lean_dec_ref(v_inst_1098_);
lean_dec_ref(v_inst_1097_);
lean_dec(v_structName_1094_);
v_val_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1109_, 1);
lean_inc(v_asyncMode_1102_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1111_, 0, v_val_1110_);
lean_closure_set(v___f_1111_, 1, v_parentInfo_1095_);
lean_closure_set(v___f_1111_, 2, v___x_1100_);
lean_closure_set(v___f_1111_, 3, v_asyncMode_1102_);
lean_closure_set(v___f_1111_, 4, v___x_1103_);
v___x_1112_ = lean_apply_1(v_modifyEnv_1096_, v___f_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_dec(v___x_1109_);
lean_dec(v_modifyEnv_1096_);
lean_dec_ref(v_parentInfo_1095_);
v___x_1113_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_1114_ = l_Lean_MessageData_ofName(v_structName_1094_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 7);
lean_ctor_set(v___x_1107_, 1, v___x_1114_);
lean_ctor_set(v___x_1107_, 0, v___x_1113_);
v___x_1116_ = v___x_1107_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_throwError___redArg(v_inst_1097_, v_inst_1098_, v___x_1118_);
return v___x_1119_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = l_Lean_instInhabitedStructureState_default;
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v___x_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_structName_1131_, lean_object* v_parentInfo_1132_){
_start:
{
lean_object* v_toBind_1133_; lean_object* v_getEnv_1134_; lean_object* v_modifyEnv_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v_toBind_1133_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc(v_toBind_1133_);
v_getEnv_1134_ = lean_ctor_get(v_inst_1129_, 0);
lean_inc(v_getEnv_1134_);
v_modifyEnv_1135_ = lean_ctor_get(v_inst_1129_, 1);
lean_inc(v_modifyEnv_1135_);
lean_dec_ref(v_inst_1129_);
v___x_1136_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1137_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1138_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1139_, 0, v___x_1138_);
lean_closure_set(v___f_1139_, 1, v___x_1136_);
lean_closure_set(v___f_1139_, 2, v___x_1137_);
lean_closure_set(v___f_1139_, 3, v_structName_1131_);
lean_closure_set(v___f_1139_, 4, v_parentInfo_1132_);
lean_closure_set(v___f_1139_, 5, v_modifyEnv_1135_);
lean_closure_set(v___f_1139_, 6, v_inst_1128_);
lean_closure_set(v___f_1139_, 7, v_inst_1130_);
v___x_1140_ = lean_apply_4(v_toBind_1133_, lean_box(0), lean_box(0), v_getEnv_1134_, v___f_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_structName_1145_, lean_object* v_parentInfo_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_setStructureParents___redArg(v_inst_1142_, v_inst_1143_, v_inst_1144_, v_structName_1145_, v_parentInfo_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1148_, lean_object* v_k_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_m_1154_; lean_object* v_a_1155_; uint8_t v___x_1156_; 
v___x_1152_ = lean_nat_add(v_x_1150_, v_x_1151_);
v___x_1153_ = lean_unsigned_to_nat(1u);
v_m_1154_ = lean_nat_shiftr(v___x_1152_, v___x_1153_);
lean_dec(v___x_1152_);
v_a_1155_ = lean_array_fget_borrowed(v_as_1148_, v_m_1154_);
v___x_1156_ = l_Lean_StructureInfo_lt(v_a_1155_, v_k_1149_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; 
lean_dec(v_x_1151_);
v___x_1157_ = l_Lean_StructureInfo_lt(v_k_1149_, v_a_1155_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_dec(v_m_1154_);
lean_dec(v_x_1150_);
lean_inc(v_a_1155_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_a_1155_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; uint8_t v___y_1163_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_nat_dec_eq(v_m_1154_, v___x_1159_);
v___x_1161_ = lean_nat_sub(v_m_1154_, v___x_1153_);
lean_dec(v_m_1154_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_lt(v___x_1161_, v_x_1150_);
v___y_1163_ = v___x_1166_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v___x_1160_;
goto v___jp_1162_;
}
v___jp_1162_:
{
if (v___y_1163_ == 0)
{
v_x_1151_ = v___x_1161_;
goto _start;
}
else
{
lean_object* v___x_1165_; 
lean_dec(v___x_1161_);
lean_dec(v_x_1150_);
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
}
}
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
lean_dec(v_x_1150_);
v___x_1167_ = lean_nat_add(v_m_1154_, v___x_1153_);
lean_dec(v_m_1154_);
v___x_1168_ = lean_nat_dec_le(v___x_1167_, v_x_1151_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec(v___x_1167_);
lean_dec(v_x_1151_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
v_x_1150_ = v___x_1167_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1171_, lean_object* v_k_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1171_, v_k_1172_, v_x_1173_, v_x_1174_);
lean_dec_ref(v_k_1172_);
lean_dec_ref(v_as_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1176_, lean_object* v_vals_1177_, lean_object* v_i_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_keys_1176_);
v___x_1181_ = lean_nat_dec_lt(v_i_1178_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_i_1178_);
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_k_x27_1183_; uint8_t v___x_1184_; 
v_k_x27_1183_ = lean_array_fget_borrowed(v_keys_1176_, v_i_1178_);
v___x_1184_ = lean_name_eq(v_k_1179_, v_k_x27_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_i_1178_, v___x_1185_);
lean_dec(v_i_1178_);
v_i_1178_ = v___x_1186_;
goto _start;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_array_fget_borrowed(v_vals_1177_, v_i_1178_);
lean_dec(v_i_1178_);
lean_inc(v___x_1188_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1190_, lean_object* v_vals_1191_, lean_object* v_i_1192_, lean_object* v_k_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1190_, v_vals_1191_, v_i_1192_, v_k_1193_);
lean_dec(v_k_1193_);
lean_dec_ref(v_vals_1191_);
lean_dec_ref(v_keys_1190_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1195_, size_t v_x_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1195_) == 0)
{
lean_object* v_es_1198_; lean_object* v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v_j_1202_; lean_object* v___x_1203_; 
v_es_1198_ = lean_ctor_get(v_x_1195_, 0);
v___x_1199_ = lean_box(2);
v___x_1200_ = ((size_t)31ULL);
v___x_1201_ = lean_usize_land(v_x_1196_, v___x_1200_);
v_j_1202_ = lean_usize_to_nat(v___x_1201_);
v___x_1203_ = lean_array_get_borrowed(v___x_1199_, v_es_1198_, v_j_1202_);
lean_dec(v_j_1202_);
switch(lean_obj_tag(v___x_1203_))
{
case 0:
{
lean_object* v_key_1204_; lean_object* v_val_1205_; uint8_t v___x_1206_; 
v_key_1204_ = lean_ctor_get(v___x_1203_, 0);
v_val_1205_ = lean_ctor_get(v___x_1203_, 1);
v___x_1206_ = lean_name_eq(v_x_1197_, v_key_1204_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; 
lean_inc(v_val_1205_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_val_1205_);
return v___x_1208_;
}
}
case 1:
{
lean_object* v_node_1209_; size_t v___x_1210_; size_t v___x_1211_; 
v_node_1209_ = lean_ctor_get(v___x_1203_, 0);
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_usize_shift_right(v_x_1196_, v___x_1210_);
v_x_1195_ = v_node_1209_;
v_x_1196_ = v___x_1211_;
goto _start;
}
default: 
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
}
}
else
{
lean_object* v_ks_1214_; lean_object* v_vs_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_ks_1214_ = lean_ctor_get(v_x_1195_, 0);
v_vs_1215_ = lean_ctor_get(v_x_1195_, 1);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1214_, v_vs_1215_, v___x_1216_, v_x_1197_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
size_t v_x_410__boxed_1221_; lean_object* v_res_1222_; 
v_x_410__boxed_1221_ = lean_unbox_usize(v_x_1219_);
lean_dec(v_x_1219_);
v_res_1222_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1218_, v_x_410__boxed_1221_, v_x_1220_);
lean_dec(v_x_1220_);
lean_dec_ref(v_x_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
uint64_t v___y_1226_; 
if (lean_obj_tag(v_x_1224_) == 0)
{
uint64_t v___x_1229_; 
v___x_1229_ = 1723ULL;
v___y_1226_ = v___x_1229_;
goto v___jp_1225_;
}
else
{
uint64_t v_hash_1230_; 
v_hash_1230_ = lean_ctor_get_uint64(v_x_1224_, sizeof(void*)*2);
v___y_1226_ = v_hash_1230_;
goto v___jp_1225_;
}
v___jp_1225_:
{
size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_uint64_to_usize(v___y_1226_);
v___x_1228_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1223_, v___x_1227_, v_x_1224_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1231_, v_x_1232_);
lean_dec(v_x_1232_);
lean_dec_ref(v_x_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1234_, lean_object* v_structName_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1237_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1234_, v_structName_1235_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v___x_1238_; lean_object* v_toEnvExtension_1239_; lean_object* v_asyncMode_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_snd_1243_; lean_object* v___x_1244_; 
v___x_1238_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1239_ = lean_ctor_get(v___x_1238_, 0);
v_asyncMode_1240_ = lean_ctor_get(v_toEnvExtension_1239_, 2);
v___x_1241_ = lean_box(0);
v___x_1242_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1236_, v___x_1238_, v_env_1234_, v_asyncMode_1240_, v___x_1241_);
v_snd_1243_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_snd_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1243_, v_structName_1235_);
lean_dec(v_structName_1235_);
lean_dec(v_snd_1243_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_val_1245_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1246_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1247_ = 0;
v___x_1248_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1236_, v___x_1246_, v_env_1234_, v_val_1245_, v___x_1247_);
lean_dec(v_val_1245_);
lean_dec_ref(v_env_1234_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_array_get_size(v___x_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1248_);
lean_dec(v_structName_1235_);
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_sub(v___x_1250_, v___x_1253_);
v___x_1255_ = lean_nat_dec_le(v___x_1249_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec(v___x_1254_);
lean_dec_ref(v___x_1248_);
lean_dec(v_structName_1235_);
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1258_, 0, v_structName_1235_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
lean_ctor_set(v___x_1258_, 3, v___x_1257_);
v___x_1259_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1248_, v___x_1258_, v___x_1249_, v___x_1254_);
lean_dec_ref_known(v___x_1258_, 4);
lean_dec_ref(v___x_1248_);
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1264_, v_x_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1268_, lean_object* v_k_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1268_, v_k_1269_, v_x_1270_, v_x_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1274_, lean_object* v_k_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1274_, v_k_1275_, v_x_1276_, v_x_1277_, v_x_1278_);
lean_dec_ref(v_k_1275_);
lean_dec_ref(v_as_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, size_t v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1281_, v_x_1282_, v_x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
size_t v_x_541__boxed_1289_; lean_object* v_res_1290_; 
v_x_541__boxed_1289_ = lean_unbox_usize(v_x_1287_);
lean_dec(v_x_1287_);
v_res_1290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1285_, v_x_1286_, v_x_541__boxed_1289_, v_x_1288_);
lean_dec(v_x_1288_);
lean_dec_ref(v_x_1286_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1291_, lean_object* v_keys_1292_, lean_object* v_vals_1293_, lean_object* v_heq_1294_, lean_object* v_i_1295_, lean_object* v_k_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1292_, v_vals_1293_, v_i_1295_, v_k_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1298_, lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_heq_1301_, lean_object* v_i_1302_, lean_object* v_k_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1298_, v_keys_1299_, v_vals_1300_, v_heq_1301_, v_i_1302_, v_k_1303_);
lean_dec(v_k_1303_);
lean_dec_ref(v_vals_1300_);
lean_dec_ref(v_keys_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1307_ = lean_panic_fn_borrowed(v___x_1306_, v_msg_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1311_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1312_ = lean_unsigned_to_nat(4u);
v___x_1313_ = lean_unsigned_to_nat(139u);
v___x_1314_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1315_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1316_ = l_mkPanicMessageWithDecl(v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_, v___x_1311_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1317_, lean_object* v_structName_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_getStructureInfo_x3f(v_env_1317_, v_structName_1318_);
if (lean_obj_tag(v___x_1319_) == 1)
{
lean_object* v_val_1320_; 
v_val_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1319_, 1);
return v_val_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1322_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1325_ = lean_panic_fn_borrowed(v___x_1324_, v_msg_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1327_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1328_ = lean_unsigned_to_nat(9u);
v___x_1329_ = lean_unsigned_to_nat(154u);
v___x_1330_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1331_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1332_ = l_mkPanicMessageWithDecl(v___x_1331_, v___x_1330_, v___x_1329_, v___x_1328_, v___x_1327_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1334_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1335_ = lean_unsigned_to_nat(11u);
v___x_1336_ = lean_unsigned_to_nat(153u);
v___x_1337_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1338_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1339_ = l_mkPanicMessageWithDecl(v___x_1338_, v___x_1337_, v___x_1336_, v___x_1335_, v___x_1334_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1340_, lean_object* v_constName_1341_){
_start:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = 0;
lean_inc_ref(v_env_1340_);
v___x_1349_ = l_Lean_Environment_find_x3f(v_env_1340_, v_constName_1341_, v___x_1348_);
if (lean_obj_tag(v___x_1349_) == 1)
{
lean_object* v_val_1350_; 
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v___x_1349_, 1);
if (lean_obj_tag(v_val_1350_) == 5)
{
lean_object* v_val_1351_; lean_object* v_ctors_1352_; 
v_val_1351_ = lean_ctor_get(v_val_1350_, 0);
lean_inc_ref(v_val_1351_);
lean_dec_ref_known(v_val_1350_, 1);
v_ctors_1352_ = lean_ctor_get(v_val_1351_, 4);
lean_inc(v_ctors_1352_);
lean_dec_ref(v_val_1351_);
if (lean_obj_tag(v_ctors_1352_) == 1)
{
lean_object* v_tail_1353_; 
v_tail_1353_ = lean_ctor_get(v_ctors_1352_, 1);
if (lean_obj_tag(v_tail_1353_) == 0)
{
lean_object* v_head_1354_; lean_object* v___x_1355_; 
v_head_1354_ = lean_ctor_get(v_ctors_1352_, 0);
lean_inc(v_head_1354_);
lean_dec_ref_known(v_ctors_1352_, 2);
v___x_1355_ = l_Lean_Environment_find_x3f(v_env_1340_, v_head_1354_, v___x_1348_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
if (lean_obj_tag(v_val_1356_) == 6)
{
lean_object* v_val_1357_; 
v_val_1357_ = lean_ctor_get(v_val_1356_, 0);
lean_inc_ref(v_val_1357_);
lean_dec_ref_known(v_val_1356_, 1);
return v_val_1357_;
}
else
{
lean_dec(v_val_1356_);
goto v___jp_1345_;
}
}
else
{
lean_dec(v___x_1355_);
goto v___jp_1345_;
}
}
else
{
lean_dec_ref_known(v_ctors_1352_, 2);
lean_dec_ref(v_env_1340_);
goto v___jp_1342_;
}
}
else
{
lean_dec(v_ctors_1352_);
lean_dec_ref(v_env_1340_);
goto v___jp_1342_;
}
}
else
{
lean_dec(v_val_1350_);
lean_dec_ref(v_env_1340_);
goto v___jp_1342_;
}
}
else
{
lean_dec(v___x_1349_);
lean_dec_ref(v_env_1340_);
goto v___jp_1342_;
}
v___jp_1342_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1344_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1343_);
return v___x_1344_;
}
v___jp_1345_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1347_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1346_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1358_, lean_object* v_structName_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v_fieldNames_1361_; 
v___x_1360_ = l_Lean_getStructureInfo(v_env_1358_, v_structName_1359_);
v_fieldNames_1361_ = lean_ctor_get(v___x_1360_, 1);
lean_inc_ref(v_fieldNames_1361_);
lean_dec_ref(v___x_1360_);
return v_fieldNames_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1362_, lean_object* v_structName_1363_, lean_object* v_fieldName_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_getStructureInfo_x3f(v_env_1362_, v_structName_1363_);
if (lean_obj_tag(v___x_1365_) == 1)
{
lean_object* v_val_1366_; lean_object* v_fieldInfo_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_val_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v_fieldInfo_1367_ = lean_ctor_get(v_val_1366_, 2);
lean_inc_ref(v_fieldInfo_1367_);
lean_dec(v_val_1366_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_fieldInfo_1367_);
v___x_1370_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_fieldInfo_1367_);
lean_dec(v_fieldName_1364_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_sub(v___x_1369_, v___x_1372_);
v___x_1374_ = lean_nat_dec_le(v___x_1368_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v___x_1373_);
lean_dec_ref(v_fieldInfo_1367_);
lean_dec(v_fieldName_1364_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_box(0);
v___x_1378_ = 0;
v___x_1379_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1379_, 0, v_fieldName_1364_);
lean_ctor_set(v___x_1379_, 1, v___x_1376_);
lean_ctor_set(v___x_1379_, 2, v___x_1377_);
lean_ctor_set(v___x_1379_, 3, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*4, v___x_1378_);
v___x_1380_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1367_, v___x_1379_, v___x_1368_, v___x_1373_);
lean_dec_ref_known(v___x_1379_, 4);
lean_dec_ref(v_fieldInfo_1367_);
return v___x_1380_;
}
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v___x_1365_);
lean_dec(v_fieldName_1364_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1382_, lean_object* v_structName_1383_, lean_object* v_fieldName_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_getFieldInfo_x3f(v_env_1382_, v_structName_1383_, v_fieldName_1384_);
if (lean_obj_tag(v___x_1385_) == 1)
{
lean_object* v_val_1386_; lean_object* v_subobject_x3f_1387_; 
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v_subobject_x3f_1387_ = lean_ctor_get(v_val_1386_, 2);
lean_inc(v_subobject_x3f_1387_);
lean_dec(v_val_1386_);
return v_subobject_x3f_1387_;
}
else
{
lean_object* v___x_1388_; 
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1389_, lean_object* v_structName_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v_parentInfo_1392_; 
v___x_1391_ = l_Lean_getStructureInfo(v_env_1389_, v_structName_1390_);
v_parentInfo_1392_ = lean_ctor_get(v___x_1391_, 3);
lean_inc_ref(v_parentInfo_1392_);
lean_dec_ref(v___x_1391_);
return v_parentInfo_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1393_, lean_object* v_structName_1394_, lean_object* v_as_1395_, size_t v_i_1396_, size_t v_stop_1397_, lean_object* v_b_1398_){
_start:
{
lean_object* v___y_1400_; uint8_t v___x_1404_; 
v___x_1404_ = lean_usize_dec_eq(v_i_1396_, v_stop_1397_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_array_uget_borrowed(v_as_1395_, v_i_1396_);
lean_inc(v___x_1405_);
lean_inc(v_structName_1394_);
lean_inc_ref(v_env_1393_);
v___x_1406_ = l_Lean_isSubobjectField_x3f(v_env_1393_, v_structName_1394_, v___x_1405_);
if (lean_obj_tag(v___x_1406_) == 0)
{
v___y_1400_ = v_b_1398_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1407_; lean_object* v___x_1408_; 
v_val_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = lean_array_push(v_b_1398_, v_val_1407_);
v___y_1400_ = v___x_1408_;
goto v___jp_1399_;
}
}
else
{
lean_dec(v_structName_1394_);
lean_dec_ref(v_env_1393_);
return v_b_1398_;
}
v___jp_1399_:
{
size_t v___x_1401_; size_t v___x_1402_; 
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_i_1396_, v___x_1401_);
v_i_1396_ = v___x_1402_;
v_b_1398_ = v___y_1400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1409_, lean_object* v_structName_1410_, lean_object* v_as_1411_, lean_object* v_i_1412_, lean_object* v_stop_1413_, lean_object* v_b_1414_){
_start:
{
size_t v_i_boxed_1415_; size_t v_stop_boxed_1416_; lean_object* v_res_1417_; 
v_i_boxed_1415_ = lean_unbox_usize(v_i_1412_);
lean_dec(v_i_1412_);
v_stop_boxed_1416_ = lean_unbox_usize(v_stop_1413_);
lean_dec(v_stop_1413_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1409_, v_structName_1410_, v_as_1411_, v_i_boxed_1415_, v_stop_boxed_1416_, v_b_1414_);
lean_dec_ref(v_as_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1418_, lean_object* v_structName_1419_, lean_object* v_as_1420_, lean_object* v_start_1421_, lean_object* v_stop_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1424_ = lean_nat_dec_lt(v_start_1421_, v_stop_1422_);
if (v___x_1424_ == 0)
{
lean_dec(v_structName_1419_);
lean_dec_ref(v_env_1418_);
return v___x_1423_;
}
else
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = lean_array_get_size(v_as_1420_);
v___x_1426_ = lean_nat_dec_le(v_stop_1422_, v___x_1425_);
if (v___x_1426_ == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_lt(v_start_1421_, v___x_1425_);
if (v___x_1427_ == 0)
{
lean_dec(v_structName_1419_);
lean_dec_ref(v_env_1418_);
return v___x_1423_;
}
else
{
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_usize_of_nat(v_start_1421_);
v___x_1429_ = lean_usize_of_nat(v___x_1425_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1418_, v_structName_1419_, v_as_1420_, v___x_1428_, v___x_1429_, v___x_1423_);
return v___x_1430_;
}
}
else
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_usize_of_nat(v_start_1421_);
v___x_1432_ = lean_usize_of_nat(v_stop_1422_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1418_, v_structName_1419_, v_as_1420_, v___x_1431_, v___x_1432_, v___x_1423_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1434_, lean_object* v_structName_1435_, lean_object* v_as_1436_, lean_object* v_start_1437_, lean_object* v_stop_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1434_, v_structName_1435_, v_as_1436_, v_start_1437_, v_stop_1438_);
lean_dec(v_stop_1438_);
lean_dec(v_start_1437_);
lean_dec_ref(v_as_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1440_, lean_object* v_structName_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_inc(v_structName_1441_);
lean_inc_ref(v_env_1440_);
v___x_1442_ = l_Lean_getStructureFields(v_env_1440_, v_structName_1441_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_array_get_size(v___x_1442_);
v___x_1445_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1440_, v_structName_1441_, v___x_1442_, v___x_1443_, v___x_1444_);
lean_dec_ref(v___x_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1446_, lean_object* v_as_1447_, size_t v_i_1448_, size_t v_stop_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_eq(v_i_1448_, v_stop_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_array_uget_borrowed(v_as_1447_, v_i_1448_);
v___x_1452_ = lean_name_eq(v_a_1446_, v___x_1451_);
if (v___x_1452_ == 0)
{
size_t v___x_1453_; size_t v___x_1454_; 
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1448_, v___x_1453_);
v_i_1448_ = v___x_1454_;
goto _start;
}
else
{
return v___x_1452_;
}
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1457_, lean_object* v_as_1458_, lean_object* v_i_1459_, lean_object* v_stop_1460_){
_start:
{
size_t v_i_boxed_1461_; size_t v_stop_boxed_1462_; uint8_t v_res_1463_; lean_object* v_r_1464_; 
v_i_boxed_1461_ = lean_unbox_usize(v_i_1459_);
lean_dec(v_i_1459_);
v_stop_boxed_1462_ = lean_unbox_usize(v_stop_1460_);
lean_dec(v_stop_1460_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1457_, v_as_1458_, v_i_boxed_1461_, v_stop_boxed_1462_);
lean_dec_ref(v_as_1458_);
lean_dec(v_a_1457_);
v_r_1464_ = lean_box(v_res_1463_);
return v_r_1464_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_array_get_size(v_as_1465_);
v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
return v___x_1469_;
}
else
{
if (v___x_1469_ == 0)
{
return v___x_1469_;
}
else
{
size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = ((size_t)0ULL);
v___x_1471_ = lean_usize_of_nat(v___x_1468_);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1466_, v_as_1465_, v___x_1470_, v___x_1471_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1473_, lean_object* v_a_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_as_1473_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1480_, lean_object* v_structName_1481_, lean_object* v_fieldName_1482_){
_start:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
lean_inc(v_structName_1481_);
lean_inc_ref(v_env_1480_);
v___x_1483_ = l_Lean_getStructureFields(v_env_1480_, v_structName_1481_);
v___x_1484_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1483_, v_fieldName_1482_);
lean_dec_ref(v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; size_t v_sz_1488_; size_t v___x_1489_; lean_object* v___x_1490_; lean_object* v_fst_1491_; 
lean_inc_ref(v_env_1480_);
v___x_1485_ = l_Lean_getStructureSubobjects(v_env_1480_, v_structName_1481_);
v___x_1486_ = lean_box(0);
v___x_1487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1488_ = lean_array_size(v___x_1485_);
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1480_, v_fieldName_1482_, v___x_1485_, v_sz_1488_, v___x_1489_, v___x_1487_);
lean_dec_ref(v___x_1485_);
v_fst_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_fst_1491_);
lean_dec_ref(v___x_1490_);
if (lean_obj_tag(v_fst_1491_) == 0)
{
return v___x_1486_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v_fst_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_fst_1491_, 1);
return v_val_1492_;
}
}
else
{
lean_object* v___x_1493_; 
lean_dec_ref(v_env_1480_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_structName_1481_);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1494_, lean_object* v_fieldName_1495_, lean_object* v_as_1496_, size_t v_sz_1497_, size_t v_i_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1498_, v_sz_1497_);
if (v___x_1500_ == 0)
{
lean_dec_ref(v_env_1494_);
lean_inc_ref(v_b_1499_);
return v_b_1499_;
}
else
{
lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_box(0);
v_a_1502_ = lean_array_uget_borrowed(v_as_1496_, v_i_1498_);
lean_inc(v_a_1502_);
lean_inc_ref(v_env_1494_);
v___x_1503_ = l_Lean_findField_x3f(v_env_1494_, v_a_1502_, v_fieldName_1495_);
if (lean_obj_tag(v___x_1503_) == 1)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_env_1494_);
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1501_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; 
lean_dec(v___x_1503_);
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1498_, v___x_1507_);
v_i_1498_ = v___x_1508_;
v_b_1499_ = v___x_1506_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1510_, lean_object* v_fieldName_1511_, lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_){
_start:
{
size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1510_, v_fieldName_1511_, v_as_1512_, v_sz_boxed_1516_, v_i_boxed_1517_, v_b_1515_);
lean_dec_ref(v_b_1515_);
lean_dec_ref(v_as_1512_);
lean_dec(v_fieldName_1511_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1519_, lean_object* v_structName_1520_, lean_object* v_fieldName_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_findField_x3f(v_env_1519_, v_structName_1520_, v_fieldName_1521_);
lean_dec(v_fieldName_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1526_, lean_object* v_as_1527_, size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_b_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1531_ == 0)
{
lean_inc_ref(v_b_1530_);
return v_b_1530_;
}
else
{
lean_object* v_a_1532_; lean_object* v_projFn_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_a_1532_ = lean_array_uget_borrowed(v_as_1527_, v_i_1529_);
v_projFn_1533_ = lean_ctor_get(v_a_1532_, 1);
v___x_1534_ = lean_box(0);
v___x_1535_ = l_Lean_Name_isSuffixOf(v_projName_1526_, v_projFn_1533_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; 
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1537_ = ((size_t)1ULL);
v___x_1538_ = lean_usize_add(v_i_1529_, v___x_1537_);
v_i_1529_ = v___x_1538_;
v_b_1530_ = v___x_1536_;
goto _start;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc(v_a_1532_);
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_a_1532_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1534_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1543_, lean_object* v_as_1544_, lean_object* v_sz_1545_, lean_object* v_i_1546_, lean_object* v_b_1547_){
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1545_);
lean_dec(v_sz_1545_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1543_, v_as_1544_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1547_);
lean_dec_ref(v_b_1547_);
lean_dec_ref(v_as_1544_);
lean_dec(v_projName_1543_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1551_, lean_object* v_projName_1552_, lean_object* v_structName_1553_, lean_object* v_a_1554_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_NameSet_contains(v_a_1554_, v_structName_1553_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1580_; size_t v_sz_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v_fst_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1601_; 
lean_inc(v_structName_1553_);
lean_inc_ref(v_env_1551_);
v___x_1556_ = l_Lean_getStructureParentInfo(v_env_1551_, v_structName_1553_);
v___x_1580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1581_ = lean_array_size(v___x_1556_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1552_, v___x_1556_, v_sz_1581_, v___x_1582_, v___x_1580_);
v_fst_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1583_, 1);
lean_dec(v_unused_1602_);
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1601_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_fst_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1601_;
goto v_resetjp_1585_;
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; lean_object* v_fst_1564_; lean_object* v_fst_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1578_; 
v___x_1558_ = l_Lean_NameSet_insert(v_a_1554_, v_structName_1553_);
v___x_1559_ = lean_box(0);
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1561_ = lean_array_size(v___x_1556_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1551_, v_projName_1552_, v___x_1556_, v_sz_1561_, v___x_1562_, v___x_1560_, v___x_1558_);
lean_dec_ref(v___x_1556_);
v_fst_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_fst_1564_);
v_fst_1565_ = lean_ctor_get(v_fst_1564_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_fst_1564_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_fst_1564_, 1);
lean_dec(v_unused_1579_);
v___x_1567_ = v_fst_1564_;
v_isShared_1568_ = v_isSharedCheck_1578_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_fst_1565_);
lean_dec(v_fst_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1578_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_fst_1565_) == 0)
{
lean_object* v_snd_1569_; lean_object* v___x_1571_; 
v_snd_1569_ = lean_ctor_get(v___x_1563_, 1);
lean_inc(v_snd_1569_);
lean_dec_ref(v___x_1563_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1569_);
lean_ctor_set(v___x_1567_, 0, v___x_1559_);
v___x_1571_ = v___x_1567_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_snd_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
lean_object* v_snd_1573_; lean_object* v_val_1574_; lean_object* v___x_1576_; 
v_snd_1573_ = lean_ctor_get(v___x_1563_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1563_);
v_val_1574_ = lean_ctor_get(v_fst_1565_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_fst_1565_, 1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1573_);
lean_ctor_set(v___x_1567_, 0, v_val_1574_);
v___x_1576_ = v___x_1567_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_val_1574_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_snd_1573_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
v_resetjp_1585_:
{
if (lean_obj_tag(v_fst_1584_) == 0)
{
lean_del_object(v___x_1586_);
goto v___jp_1557_;
}
else
{
lean_object* v_val_1588_; 
v_val_1588_ = lean_ctor_get(v_fst_1584_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v_fst_1584_, 1);
if (lean_obj_tag(v_val_1588_) == 1)
{
lean_object* v_val_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v___x_1556_);
lean_dec(v_structName_1553_);
lean_dec_ref(v_env_1551_);
v_val_1589_ = lean_ctor_get(v_val_1588_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_val_1588_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1591_ = v_val_1588_;
v_isShared_1592_ = v_isSharedCheck_1600_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_val_1589_);
lean_dec(v_val_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1600_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_structName_1593_; lean_object* v___x_1595_; 
v_structName_1593_ = lean_ctor_get(v_val_1589_, 0);
lean_inc(v_structName_1593_);
lean_dec(v_val_1589_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_structName_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_structName_1593_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v_a_1554_);
lean_ctor_set(v___x_1586_, 0, v___x_1595_);
v___x_1597_ = v___x_1586_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1554_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec(v_val_1588_);
lean_del_object(v___x_1586_);
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_structName_1553_);
lean_dec_ref(v_env_1551_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1554_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1605_, lean_object* v_projName_1606_, lean_object* v_as_1607_, size_t v_sz_1608_, size_t v_i_1609_, lean_object* v_b_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_lt(v_i_1609_, v_sz_1608_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v_env_1605_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_b_1610_);
lean_ctor_set(v___x_1613_, 1, v___y_1611_);
return v___x_1613_;
}
else
{
lean_object* v_a_1614_; lean_object* v_structName_1615_; lean_object* v___x_1616_; lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_b_1610_);
v_a_1614_ = lean_array_uget_borrowed(v_as_1607_, v_i_1609_);
v_structName_1615_ = lean_ctor_get(v_a_1614_, 0);
lean_inc(v_structName_1615_);
lean_inc_ref(v_env_1605_);
v___x_1616_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1605_, v_projName_1606_, v_structName_1615_, v___y_1611_);
v_fst_1617_ = lean_ctor_get(v___x_1616_, 0);
v_snd_1618_ = lean_ctor_get(v___x_1616_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1620_ = v___x_1616_;
v_isShared_1621_ = v_isSharedCheck_1632_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_inc(v_fst_1617_);
lean_dec(v___x_1616_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1632_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_box(0);
if (lean_obj_tag(v_fst_1617_) == 1)
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec_ref(v_env_1605_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_fst_1617_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1622_);
lean_ctor_set(v___x_1620_, 0, v___x_1623_);
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1622_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_snd_1618_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; 
lean_del_object(v___x_1620_);
lean_dec(v_fst_1617_);
v___x_1628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1609_, v___x_1629_);
v_i_1609_ = v___x_1630_;
v_b_1610_ = v___x_1628_;
v___y_1611_ = v_snd_1618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1633_, lean_object* v_projName_1634_, lean_object* v_as_1635_, lean_object* v_sz_1636_, lean_object* v_i_1637_, lean_object* v_b_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1636_);
lean_dec(v_sz_1636_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1633_, v_projName_1634_, v_as_1635_, v_sz_boxed_1640_, v_i_boxed_1641_, v_b_1638_, v___y_1639_);
lean_dec_ref(v_as_1635_);
lean_dec(v_projName_1634_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1643_, lean_object* v_projName_1644_, lean_object* v_structName_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1643_, v_projName_1644_, v_structName_1645_, v_a_1646_);
lean_dec(v_projName_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1648_, lean_object* v_structName_1649_, lean_object* v_projName_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_fst_1653_; 
v___x_1651_ = l_Lean_NameSet_empty;
v___x_1652_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1648_, v_projName_1650_, v_structName_1649_, v___x_1651_);
v_fst_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_fst_1653_);
lean_dec_ref(v___x_1652_);
return v_fst_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1654_, lean_object* v_structName_1655_, lean_object* v_projName_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_findParentProjStruct_x3f(v_env_1654_, v_structName_1655_, v_projName_1656_);
lean_dec(v_projName_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1663_ = l_Lean_Name_append(v_structCtorName_1661_, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1664_, lean_object* v_structName_1665_, uint8_t v_includeSubobjectFields_1666_, lean_object* v_as_1667_, size_t v_i_1668_, size_t v_stop_1669_, lean_object* v_b_1670_){
_start:
{
lean_object* v___y_1672_; uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_eq(v_i_1668_, v_stop_1669_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_array_uget_borrowed(v_as_1667_, v_i_1668_);
lean_inc(v___x_1677_);
lean_inc(v_structName_1665_);
lean_inc_ref(v_env_1664_);
v___x_1678_ = l_Lean_isSubobjectField_x3f(v_env_1664_, v_structName_1665_, v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_inc(v___x_1677_);
v___x_1679_ = lean_array_push(v_b_1670_, v___x_1677_);
v___y_1672_ = v___x_1679_;
goto v___jp_1671_;
}
else
{
if (v_includeSubobjectFields_1666_ == 0)
{
lean_object* v_val_1680_; lean_object* v___x_1681_; 
v_val_1680_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___x_1678_, 1);
lean_inc_ref(v_env_1664_);
v___x_1681_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1664_, v_val_1680_, v_b_1670_, v_includeSubobjectFields_1666_);
v___y_1672_ = v___x_1681_;
goto v___jp_1671_;
}
else
{
lean_object* v_val_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_val_1682_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1678_, 1);
lean_inc(v___x_1677_);
v___x_1683_ = lean_array_push(v_b_1670_, v___x_1677_);
lean_inc_ref(v_env_1664_);
v___x_1684_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1664_, v_val_1682_, v___x_1683_, v_includeSubobjectFields_1666_);
v___y_1672_ = v___x_1684_;
goto v___jp_1671_;
}
}
}
else
{
lean_dec(v_structName_1665_);
lean_dec_ref(v_env_1664_);
return v_b_1670_;
}
v___jp_1671_:
{
size_t v___x_1673_; size_t v___x_1674_; 
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_i_1668_, v___x_1673_);
v_i_1668_ = v___x_1674_;
v_b_1670_ = v___y_1672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1685_, lean_object* v_structName_1686_, lean_object* v_fullNames_1687_, uint8_t v_includeSubobjectFields_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
lean_inc(v_structName_1686_);
lean_inc_ref(v_env_1685_);
v___x_1689_ = l_Lean_getStructureFields(v_env_1685_, v_structName_1686_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_array_get_size(v___x_1689_);
v___x_1692_ = lean_nat_dec_lt(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v___x_1689_);
lean_dec(v_structName_1686_);
lean_dec_ref(v_env_1685_);
return v_fullNames_1687_;
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_nat_dec_le(v___x_1691_, v___x_1691_);
if (v___x_1693_ == 0)
{
if (v___x_1692_ == 0)
{
lean_dec_ref(v___x_1689_);
lean_dec(v_structName_1686_);
lean_dec_ref(v_env_1685_);
return v_fullNames_1687_;
}
else
{
size_t v___x_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = ((size_t)0ULL);
v___x_1695_ = lean_usize_of_nat(v___x_1691_);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1685_, v_structName_1686_, v_includeSubobjectFields_1688_, v___x_1689_, v___x_1694_, v___x_1695_, v_fullNames_1687_);
lean_dec_ref(v___x_1689_);
return v___x_1696_;
}
}
else
{
size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = lean_usize_of_nat(v___x_1691_);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1685_, v_structName_1686_, v_includeSubobjectFields_1688_, v___x_1689_, v___x_1697_, v___x_1698_, v_fullNames_1687_);
lean_dec_ref(v___x_1689_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1700_, lean_object* v_structName_1701_, lean_object* v_fullNames_1702_, lean_object* v_includeSubobjectFields_1703_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1704_; lean_object* v_res_1705_; 
v_includeSubobjectFields_boxed_1704_ = lean_unbox(v_includeSubobjectFields_1703_);
v_res_1705_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1700_, v_structName_1701_, v_fullNames_1702_, v_includeSubobjectFields_boxed_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1706_, lean_object* v_structName_1707_, lean_object* v_includeSubobjectFields_1708_, lean_object* v_as_1709_, lean_object* v_i_1710_, lean_object* v_stop_1711_, lean_object* v_b_1712_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1713_; size_t v_i_boxed_1714_; size_t v_stop_boxed_1715_; lean_object* v_res_1716_; 
v_includeSubobjectFields_boxed_1713_ = lean_unbox(v_includeSubobjectFields_1708_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_stop_boxed_1715_ = lean_unbox_usize(v_stop_1711_);
lean_dec(v_stop_1711_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1706_, v_structName_1707_, v_includeSubobjectFields_boxed_1713_, v_as_1709_, v_i_boxed_1714_, v_stop_boxed_1715_, v_b_1712_);
lean_dec_ref(v_as_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1717_, lean_object* v_structName_1718_, uint8_t v_includeSubobjectFields_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1721_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1717_, v_structName_1718_, v___x_1720_, v_includeSubobjectFields_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1722_, lean_object* v_structName_1723_, lean_object* v_includeSubobjectFields_1724_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1725_; lean_object* v_res_1726_; 
v_includeSubobjectFields_boxed_1725_ = lean_unbox(v_includeSubobjectFields_1724_);
v_res_1726_ = l_Lean_getStructureFieldsFlattened(v_env_1722_, v_structName_1723_, v_includeSubobjectFields_boxed_1725_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1727_, lean_object* v_constName_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_getStructureInfo_x3f(v_env_1727_, v_constName_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
uint8_t v___x_1730_; 
v___x_1730_ = 0;
return v___x_1730_;
}
else
{
uint8_t v___x_1731_; 
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = 1;
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1732_, lean_object* v_constName_1733_){
_start:
{
uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_res_1734_ = l_Lean_isStructure(v_env_1732_, v_constName_1733_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1736_, lean_object* v_structName_1737_, lean_object* v_fieldName_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_getFieldInfo_x3f(v_env_1736_, v_structName_1737_, v_fieldName_1738_);
if (lean_obj_tag(v___x_1739_) == 1)
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_val_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_projFn_1744_; lean_object* v___x_1746_; 
v_projFn_1744_ = lean_ctor_get(v_val_1740_, 1);
lean_inc(v_projFn_1744_);
lean_dec(v_val_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_projFn_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_projFn_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
lean_object* v___x_1749_; 
lean_dec(v___x_1739_);
v___x_1749_ = lean_box(0);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1750_, lean_object* v_structName_1751_, lean_object* v_fieldName_1752_){
_start:
{
lean_object* v___x_1753_; 
lean_inc_ref(v_env_1750_);
v___x_1753_ = l_Lean_getProjFnForField_x3f(v_env_1750_, v_structName_1751_, v_fieldName_1752_);
if (lean_obj_tag(v___x_1753_) == 1)
{
lean_object* v_val_1754_; lean_object* v___x_1755_; 
v_val_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_n(v_val_1754_, 2);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1750_, v_val_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; 
lean_dec(v_val_1754_);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_val_1757_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v___x_1755_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v___x_1755_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_val_1754_);
lean_ctor_set(v___x_1761_, 1, v_val_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___x_1753_);
lean_dec_ref(v_env_1750_);
v___x_1766_ = lean_box(0);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1772_ = l_Lean_Name_append(v_projFn_1770_, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1778_ = l_Lean_Name_append(v_projFn_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1779_, lean_object* v_env_1780_, lean_object* v_structName_1781_, lean_object* v_fieldName_1782_){
_start:
{
lean_object* v___x_1783_; 
lean_inc(v_fieldName_1782_);
lean_inc(v_structName_1781_);
lean_inc_ref(v_env_1780_);
v___x_1783_ = l_Lean_getProjFnForField_x3f(v_env_1780_, v_structName_1781_, v_fieldName_1782_);
if (lean_obj_tag(v___x_1783_) == 1)
{
lean_object* v_val_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_fieldName_1782_);
lean_dec(v_structName_1781_);
v_val_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_val_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_defFn_1788_; uint8_t v___x_1789_; uint8_t v___x_1790_; 
v_defFn_1788_ = lean_apply_1(v_mkName_1779_, v_val_1784_);
v___x_1789_ = 1;
lean_inc(v_defFn_1788_);
v___x_1790_ = l_Lean_Environment_contains(v_env_1780_, v_defFn_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec(v_defFn_1788_);
lean_del_object(v___x_1786_);
v___x_1791_ = lean_box(0);
return v___x_1791_;
}
else
{
lean_object* v___x_1793_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_defFn_1788_);
v___x_1793_ = v___x_1786_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_defFn_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v_defFn_1797_; uint8_t v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v___x_1783_);
v___x_1796_ = l_Lean_Name_append(v_structName_1781_, v_fieldName_1782_);
v_defFn_1797_ = lean_apply_1(v_mkName_1779_, v___x_1796_);
v___x_1798_ = 1;
lean_inc(v_defFn_1797_);
v___x_1799_ = l_Lean_Environment_contains(v_env_1780_, v_defFn_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec(v_defFn_1797_);
v___x_1800_ = lean_box(0);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_defFn_1797_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1803_, lean_object* v_structName_1804_, lean_object* v_fieldName_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1807_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1806_, v_env_1803_, v_structName_1804_, v_fieldName_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1809_, lean_object* v_structName_1810_, lean_object* v_fieldName_1811_){
_start:
{
lean_object* v___x_1812_; 
lean_inc(v_fieldName_1811_);
lean_inc(v_structName_1810_);
lean_inc_ref(v_env_1809_);
v___x_1812_ = l_Lean_getDefaultFnForField_x3f(v_env_1809_, v_structName_1810_, v_fieldName_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1814_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1813_, v_env_1809_, v_structName_1810_, v_fieldName_1811_);
return v___x_1814_;
}
else
{
lean_dec(v_fieldName_1811_);
lean_dec(v_structName_1810_);
lean_dec_ref(v_env_1809_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1820_ = l_Lean_Name_append(v_projFn_1818_, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1822_, lean_object* v_structName_1823_, lean_object* v_fieldName_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1826_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1825_, v_env_1822_, v_structName_1823_, v_fieldName_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1827_, lean_object* v_env_1828_, lean_object* v_baseStructName_1829_, lean_object* v_as_1830_, lean_object* v_i_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_snd_1834_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_as_1830_);
v___x_1839_ = lean_nat_dec_lt(v_i_1831_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_i_1831_);
lean_dec_ref(v_env_1828_);
lean_dec(v_path_1827_);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___y_1832_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v_subobject_x3f_1843_; 
v___x_1842_ = lean_array_fget_borrowed(v_as_1830_, v_i_1831_);
v_subobject_x3f_1843_ = lean_ctor_get(v___x_1842_, 2);
if (lean_obj_tag(v_subobject_x3f_1843_) == 1)
{
lean_object* v_projFn_1844_; lean_object* v_val_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_fst_1848_; 
v_projFn_1844_ = lean_ctor_get(v___x_1842_, 1);
v_val_1845_ = lean_ctor_get(v_subobject_x3f_1843_, 0);
lean_inc(v_path_1827_);
lean_inc(v_projFn_1844_);
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_projFn_1844_);
lean_ctor_set(v___x_1846_, 1, v_path_1827_);
lean_inc(v_val_1845_);
lean_inc_ref(v_env_1828_);
v___x_1847_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1828_, v_baseStructName_1829_, v_val_1845_, v___x_1846_, v___y_1832_);
v_fst_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_fst_1848_);
if (lean_obj_tag(v_fst_1848_) == 0)
{
lean_object* v_snd_1849_; 
v_snd_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_snd_1849_);
lean_dec_ref(v___x_1847_);
v_snd_1834_ = v_snd_1849_;
goto v___jp_1833_;
}
else
{
lean_dec_ref_known(v_fst_1848_, 1);
lean_dec(v_i_1831_);
lean_dec_ref(v_env_1828_);
lean_dec(v_path_1827_);
return v___x_1847_;
}
}
else
{
v_snd_1834_ = v___y_1832_;
goto v___jp_1833_;
}
}
v___jp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_add(v_i_1831_, v___x_1835_);
lean_dec(v_i_1831_);
v_i_1831_ = v___x_1836_;
v___y_1832_ = v_snd_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1850_, lean_object* v_baseStructName_1851_, lean_object* v_structName_1852_, lean_object* v_path_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_name_eq(v_baseStructName_1851_, v_structName_1852_);
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_NameSet_contains(v_a_1854_, v_structName_1852_);
if (v___x_1869_ == 0)
{
goto v___jp_1855_;
}
else
{
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_path_1853_);
lean_dec(v_structName_1852_);
lean_dec_ref(v_env_1850_);
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v_a_1854_);
return v___x_1871_;
}
else
{
goto v___jp_1855_;
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_structName_1852_);
lean_dec_ref(v_env_1850_);
v___x_1872_ = l_List_reverse___redArg(v_path_1853_);
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_a_1854_);
return v___x_1874_;
}
v___jp_1855_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_inc(v_structName_1852_);
v___x_1856_ = l_Lean_NameSet_insert(v_a_1854_, v_structName_1852_);
lean_inc_ref(v_env_1850_);
v___x_1857_ = l_Lean_getStructureInfo_x3f(v_env_1850_, v_structName_1852_);
if (lean_obj_tag(v___x_1857_) == 1)
{
lean_object* v_val_1858_; lean_object* v_fieldInfo_1859_; lean_object* v_parentInfo_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_fst_1863_; 
v_val_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_val_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v_fieldInfo_1859_ = lean_ctor_get(v_val_1858_, 2);
lean_inc_ref(v_fieldInfo_1859_);
v_parentInfo_1860_ = lean_ctor_get(v_val_1858_, 3);
lean_inc_ref(v_parentInfo_1860_);
lean_dec(v_val_1858_);
v___x_1861_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1850_);
lean_inc(v_path_1853_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1853_, v_env_1850_, v_baseStructName_1851_, v_fieldInfo_1859_, v___x_1861_, v___x_1856_);
lean_dec_ref(v_fieldInfo_1859_);
v_fst_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_fst_1863_);
if (lean_obj_tag(v_fst_1863_) == 0)
{
lean_object* v_snd_1864_; lean_object* v___x_1865_; 
v_snd_1864_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_snd_1864_);
lean_dec_ref(v___x_1862_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1853_, v_env_1850_, v_baseStructName_1851_, v_parentInfo_1860_, v___x_1861_, v_snd_1864_);
lean_dec_ref(v_parentInfo_1860_);
return v___x_1865_;
}
else
{
lean_dec_ref_known(v_fst_1863_, 1);
lean_dec_ref(v_parentInfo_1860_);
lean_dec(v_path_1853_);
lean_dec_ref(v_env_1850_);
return v___x_1862_;
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v___x_1857_);
lean_dec(v_path_1853_);
lean_dec_ref(v_env_1850_);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v___x_1856_);
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1875_, lean_object* v_env_1876_, lean_object* v_baseStructName_1877_, lean_object* v_as_1878_, lean_object* v_i_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_array_get_size(v_as_1878_);
v___x_1882_ = lean_nat_dec_lt(v_i_1879_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_i_1879_);
lean_dec_ref(v_env_1876_);
lean_dec(v_path_1875_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___y_1880_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v_structName_1886_; lean_object* v_projFn_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v_fst_1890_; 
v___x_1885_ = lean_array_fget_borrowed(v_as_1878_, v_i_1879_);
v_structName_1886_ = lean_ctor_get(v___x_1885_, 0);
v_projFn_1887_ = lean_ctor_get(v___x_1885_, 1);
lean_inc(v_path_1875_);
lean_inc(v_projFn_1887_);
v___x_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_projFn_1887_);
lean_ctor_set(v___x_1888_, 1, v_path_1875_);
lean_inc(v_structName_1886_);
lean_inc_ref(v_env_1876_);
v___x_1889_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1876_, v_baseStructName_1877_, v_structName_1886_, v___x_1888_, v___y_1880_);
v_fst_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_fst_1890_);
if (lean_obj_tag(v_fst_1890_) == 0)
{
lean_object* v_snd_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_snd_1891_ = lean_ctor_get(v___x_1889_, 1);
lean_inc(v_snd_1891_);
lean_dec_ref(v___x_1889_);
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = lean_nat_add(v_i_1879_, v___x_1892_);
lean_dec(v_i_1879_);
v_i_1879_ = v___x_1893_;
v___y_1880_ = v_snd_1891_;
goto _start;
}
else
{
lean_dec_ref_known(v_fst_1890_, 1);
lean_dec(v_i_1879_);
lean_dec_ref(v_env_1876_);
lean_dec(v_path_1875_);
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1895_, lean_object* v_env_1896_, lean_object* v_baseStructName_1897_, lean_object* v_as_1898_, lean_object* v_i_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1895_, v_env_1896_, v_baseStructName_1897_, v_as_1898_, v_i_1899_, v___y_1900_);
lean_dec_ref(v_as_1898_);
lean_dec(v_baseStructName_1897_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1902_, lean_object* v_env_1903_, lean_object* v_baseStructName_1904_, lean_object* v_as_1905_, lean_object* v_i_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1902_, v_env_1903_, v_baseStructName_1904_, v_as_1905_, v_i_1906_, v___y_1907_);
lean_dec_ref(v_as_1905_);
lean_dec(v_baseStructName_1904_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1909_, lean_object* v_baseStructName_1910_, lean_object* v_structName_1911_, lean_object* v_path_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1909_, v_baseStructName_1910_, v_structName_1911_, v_path_1912_, v_a_1913_);
lean_dec(v_baseStructName_1910_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1915_, lean_object* v_baseStructName_1916_, lean_object* v_structName_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_fst_1921_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = l_Lean_NameSet_empty;
v___x_1920_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1915_, v_baseStructName_1916_, v_structName_1917_, v___x_1918_, v___x_1919_);
v_fst_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_fst_1921_);
lean_dec_ref(v___x_1920_);
return v_fst_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1922_, lean_object* v_baseStructName_1923_, lean_object* v_structName_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_getPathToBaseStructure_x3f(v_env_1922_, v_baseStructName_1923_, v_structName_1924_);
lean_dec(v_baseStructName_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1926_, lean_object* v_constName_1927_){
_start:
{
uint8_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = 0;
v___x_1929_ = l_Lean_Environment_find_x3f(v_env_1926_, v_constName_1927_, v___x_1928_);
if (lean_obj_tag(v___x_1929_) == 1)
{
lean_object* v_val_1930_; 
v_val_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v___x_1929_, 1);
if (lean_obj_tag(v_val_1930_) == 5)
{
lean_object* v_val_1931_; lean_object* v_numIndices_1932_; lean_object* v_ctors_1933_; uint8_t v_isRec_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v_val_1931_ = lean_ctor_get(v_val_1930_, 0);
lean_inc_ref(v_val_1931_);
lean_dec_ref_known(v_val_1930_, 1);
v_numIndices_1932_ = lean_ctor_get(v_val_1931_, 2);
lean_inc(v_numIndices_1932_);
v_ctors_1933_ = lean_ctor_get(v_val_1931_, 4);
lean_inc(v_ctors_1933_);
v_isRec_1934_ = lean_ctor_get_uint8(v_val_1931_, sizeof(void*)*6);
lean_dec_ref(v_val_1931_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_nat_dec_eq(v_numIndices_1932_, v___x_1935_);
lean_dec(v_numIndices_1932_);
if (v___x_1936_ == 0)
{
lean_dec(v_ctors_1933_);
return v___x_1936_;
}
else
{
if (lean_obj_tag(v_ctors_1933_) == 1)
{
lean_object* v_tail_1937_; 
v_tail_1937_ = lean_ctor_get(v_ctors_1933_, 1);
lean_inc(v_tail_1937_);
lean_dec_ref_known(v_ctors_1933_, 2);
if (lean_obj_tag(v_tail_1937_) == 0)
{
if (v_isRec_1934_ == 0)
{
return v___x_1936_;
}
else
{
return v___x_1928_;
}
}
else
{
lean_dec(v_tail_1937_);
return v___x_1928_;
}
}
else
{
lean_dec(v_ctors_1933_);
return v___x_1928_;
}
}
}
else
{
lean_dec(v_val_1930_);
return v___x_1928_;
}
}
else
{
lean_dec(v___x_1929_);
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1938_, lean_object* v_constName_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lean_isNonRecStructure(v_env_1938_, v_constName_1939_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1942_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_panic_fn_borrowed(v___x_1943_, v_msg_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1946_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1947_ = lean_unsigned_to_nat(11u);
v___x_1948_ = lean_unsigned_to_nat(374u);
v___x_1949_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1950_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1951_ = l_mkPanicMessageWithDecl(v___x_1950_, v___x_1949_, v___x_1948_, v___x_1947_, v___x_1946_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1952_, lean_object* v_constName_1953_){
_start:
{
uint8_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = 0;
lean_inc_ref(v_env_1952_);
v___x_1958_ = l_Lean_Environment_find_x3f(v_env_1952_, v_constName_1953_, v___x_1957_);
if (lean_obj_tag(v___x_1958_) == 1)
{
lean_object* v_val_1959_; 
v_val_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_val_1959_);
lean_dec_ref_known(v___x_1958_, 1);
if (lean_obj_tag(v_val_1959_) == 5)
{
lean_object* v_val_1960_; lean_object* v_numIndices_1961_; lean_object* v_ctors_1962_; uint8_t v_isRec_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_val_1960_ = lean_ctor_get(v_val_1959_, 0);
lean_inc_ref(v_val_1960_);
lean_dec_ref_known(v_val_1959_, 1);
v_numIndices_1961_ = lean_ctor_get(v_val_1960_, 2);
lean_inc(v_numIndices_1961_);
v_ctors_1962_ = lean_ctor_get(v_val_1960_, 4);
lean_inc(v_ctors_1962_);
v_isRec_1963_ = lean_ctor_get_uint8(v_val_1960_, sizeof(void*)*6);
lean_dec_ref(v_val_1960_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_nat_dec_eq(v_numIndices_1961_, v___x_1964_);
lean_dec(v_numIndices_1961_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_ctors_1962_);
lean_dec_ref(v_env_1952_);
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
else
{
if (lean_obj_tag(v_ctors_1962_) == 1)
{
lean_object* v_tail_1967_; 
v_tail_1967_ = lean_ctor_get(v_ctors_1962_, 1);
if (lean_obj_tag(v_tail_1967_) == 0)
{
if (v_isRec_1963_ == 0)
{
lean_object* v_head_1968_; lean_object* v___x_1969_; 
v_head_1968_ = lean_ctor_get(v_ctors_1962_, 0);
lean_inc(v_head_1968_);
lean_dec_ref_known(v_ctors_1962_, 2);
v___x_1969_ = l_Lean_Environment_find_x3f(v_env_1952_, v_head_1968_, v_isRec_1963_);
if (lean_obj_tag(v___x_1969_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_val_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
if (lean_obj_tag(v_val_1970_) == 6)
{
lean_object* v_val_1974_; lean_object* v___x_1976_; 
v_val_1974_ = lean_ctor_get(v_val_1970_, 0);
lean_inc_ref(v_val_1974_);
lean_dec_ref_known(v_val_1970_, 1);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_val_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_val_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_del_object(v___x_1972_);
lean_dec(v_val_1970_);
goto v___jp_1954_;
}
}
}
else
{
lean_dec(v___x_1969_);
goto v___jp_1954_;
}
}
else
{
lean_object* v___x_1979_; 
lean_dec_ref_known(v_ctors_1962_, 2);
lean_dec_ref(v_env_1952_);
v___x_1979_ = lean_box(0);
return v___x_1979_;
}
}
else
{
lean_object* v___x_1980_; 
lean_dec_ref_known(v_ctors_1962_, 2);
lean_dec_ref(v_env_1952_);
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v_ctors_1962_);
lean_dec_ref(v_env_1952_);
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_val_1959_);
lean_dec_ref(v_env_1952_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; 
lean_dec(v___x_1958_);
lean_dec_ref(v_env_1952_);
v___x_1983_ = lean_box(0);
return v___x_1983_;
}
v___jp_1954_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1956_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1955_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1984_, lean_object* v_constName_1985_){
_start:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = 0;
lean_inc_ref(v_env_1984_);
v___x_1987_ = l_Lean_Environment_find_x3f(v_env_1984_, v_constName_1985_, v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 1)
{
lean_object* v_val_1988_; 
v_val_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_val_1988_) == 5)
{
lean_object* v_val_1989_; lean_object* v_numIndices_1990_; lean_object* v_ctors_1991_; uint8_t v_isRec_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_val_1989_ = lean_ctor_get(v_val_1988_, 0);
lean_inc_ref(v_val_1989_);
lean_dec_ref_known(v_val_1988_, 1);
v_numIndices_1990_ = lean_ctor_get(v_val_1989_, 2);
lean_inc(v_numIndices_1990_);
v_ctors_1991_ = lean_ctor_get(v_val_1989_, 4);
lean_inc(v_ctors_1991_);
v_isRec_1992_ = lean_ctor_get_uint8(v_val_1989_, sizeof(void*)*6);
lean_dec_ref(v_val_1989_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_nat_dec_eq(v_numIndices_1990_, v___x_1993_);
lean_dec(v_numIndices_1990_);
if (v___x_1994_ == 0)
{
lean_dec(v_ctors_1991_);
lean_dec_ref(v_env_1984_);
return v___x_1993_;
}
else
{
if (lean_obj_tag(v_ctors_1991_) == 1)
{
lean_object* v_tail_1995_; 
v_tail_1995_ = lean_ctor_get(v_ctors_1991_, 1);
if (lean_obj_tag(v_tail_1995_) == 0)
{
if (v_isRec_1992_ == 0)
{
lean_object* v_head_1996_; lean_object* v___x_1997_; 
v_head_1996_ = lean_ctor_get(v_ctors_1991_, 0);
lean_inc(v_head_1996_);
lean_dec_ref_known(v_ctors_1991_, 2);
v___x_1997_ = l_Lean_Environment_find_x3f(v_env_1984_, v_head_1996_, v_isRec_1992_);
if (lean_obj_tag(v___x_1997_) == 1)
{
lean_object* v_val_1998_; 
v_val_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1997_, 1);
if (lean_obj_tag(v_val_1998_) == 6)
{
lean_object* v_val_1999_; lean_object* v_numFields_2000_; 
v_val_1999_ = lean_ctor_get(v_val_1998_, 0);
lean_inc_ref(v_val_1999_);
lean_dec_ref_known(v_val_1998_, 1);
v_numFields_2000_ = lean_ctor_get(v_val_1999_, 4);
lean_inc(v_numFields_2000_);
lean_dec_ref(v_val_1999_);
return v_numFields_2000_;
}
else
{
lean_dec(v_val_1998_);
return v___x_1993_;
}
}
else
{
lean_dec(v___x_1997_);
return v___x_1993_;
}
}
else
{
lean_dec_ref_known(v_ctors_1991_, 2);
lean_dec_ref(v_env_1984_);
return v___x_1993_;
}
}
else
{
lean_dec_ref_known(v_ctors_1991_, 2);
lean_dec_ref(v_env_1984_);
return v___x_1993_;
}
}
else
{
lean_dec(v_ctors_1991_);
lean_dec_ref(v_env_1984_);
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_val_1988_);
lean_dec_ref(v_env_1984_);
v___x_2001_ = lean_unsigned_to_nat(0u);
return v___x_2001_;
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v___x_1987_);
lean_dec_ref(v_env_1984_);
v___x_2002_ = lean_unsigned_to_nat(0u);
return v___x_2002_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_2011_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___f_2015_; 
v___x_2014_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2015_, 0, v___x_2014_);
return v___f_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___f_2017_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_box(1);
v___x_2020_ = l_Lean_registerEnvExtension___redArg(v___f_2017_, v___x_2018_, v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2023_, lean_object* v_structName_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v_asyncMode_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2025_ = l_Lean_structureResolutionExt;
v_asyncMode_2026_ = lean_ctor_get(v___x_2025_, 2);
v___x_2027_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2028_ = lean_box(0);
v___x_2029_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2027_, v___x_2025_, v_env_2023_, v_asyncMode_2026_, v___x_2028_);
v___x_2030_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2029_, v_structName_2024_);
lean_dec(v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2031_, lean_object* v_structName_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2031_, v_structName_2032_);
lean_dec(v_structName_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2034_, lean_object* v___x_2035_, lean_object* v_structName_2036_, lean_object* v_resolutionOrder_2037_, lean_object* v_s_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2034_, v___x_2035_, v_s_2038_, v_structName_2036_, v_resolutionOrder_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2040_, lean_object* v_env_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v_asyncMode_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = l_Lean_structureResolutionExt;
v_asyncMode_2043_ = lean_ctor_get(v___x_2042_, 2);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2042_, v_env_2041_, v___f_2040_, v_asyncMode_2043_, v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2046_, lean_object* v_structName_2047_, lean_object* v_resolutionOrder_2048_){
_start:
{
lean_object* v_modifyEnv_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; 
v_modifyEnv_2049_ = lean_ctor_get(v_inst_2046_, 1);
lean_inc(v_modifyEnv_2049_);
lean_dec_ref(v_inst_2046_);
v___x_2050_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2051_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2052_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2052_, 0, v___x_2050_);
lean_closure_set(v___f_2052_, 1, v___x_2051_);
lean_closure_set(v___f_2052_, 2, v_structName_2047_);
lean_closure_set(v___f_2052_, 3, v_resolutionOrder_2048_);
v___f_2053_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2053_, 0, v___f_2052_);
v___x_2054_ = lean_apply_1(v_modifyEnv_2049_, v___f_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2055_, lean_object* v_inst_2056_, lean_object* v_structName_2057_, lean_object* v_resolutionOrder_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2056_, v_structName_2057_, v_resolutionOrder_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2077_, lean_object* v_resOrders_2078_, lean_object* v___x_2079_, lean_object* v_toPure_2080_, lean_object* v_____s_2081_){
_start:
{
lean_object* v_fst_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2097_; 
v_fst_2082_ = lean_ctor_get(v_____s_2081_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_____s_2081_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_____s_2081_, 1);
lean_dec(v_unused_2098_);
v___x_2084_ = v_____s_2081_;
v_isShared_2085_ = v_isSharedCheck_2097_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_fst_2082_);
lean_dec(v_____s_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2097_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
if (lean_obj_tag(v_fst_2082_) == 0)
{
uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2086_ = 0;
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_array_get_borrowed(v___x_2077_, v_resOrders_2078_, v___x_2087_);
v___x_2089_ = lean_array_get_borrowed(v___x_2079_, v___x_2088_, v___x_2087_);
v___x_2090_ = lean_box(v___x_2086_);
lean_inc(v___x_2089_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___x_2089_);
lean_ctor_set(v___x_2084_, 0, v___x_2090_);
v___x_2092_ = v___x_2084_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2089_);
v___x_2092_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_apply_2(v_toPure_2080_, lean_box(0), v___x_2092_);
return v___x_2093_;
}
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_2084_);
v_val_2095_ = lean_ctor_get(v_fst_2082_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_fst_2082_, 1);
v___x_2096_ = lean_apply_2(v_toPure_2080_, lean_box(0), v_val_2095_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2099_, lean_object* v_resOrders_2100_, lean_object* v___x_2101_, lean_object* v_toPure_2102_, lean_object* v_____s_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2099_, v_resOrders_2100_, v___x_2101_, v_toPure_2102_, v_____s_2103_);
lean_dec(v___x_2101_);
lean_dec_ref(v_resOrders_2100_);
lean_dec_ref(v___x_2099_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2105_, lean_object* v_____do__lift_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_apply_2(v_toPure_2105_, lean_box(0), v_____do__lift_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2108_, lean_object* v_toPure_2109_, lean_object* v___x_2110_, lean_object* v_____s_2111_){
_start:
{
lean_object* v_fst_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2130_; 
v_fst_2112_ = lean_ctor_get(v_____s_2111_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_____s_2111_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_____s_2111_, 1);
lean_dec(v_unused_2131_);
v___x_2114_ = v_____s_2111_;
v_isShared_2115_ = v_isSharedCheck_2130_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_fst_2112_);
lean_dec(v_____s_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2130_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
if (lean_obj_tag(v_fst_2112_) == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_del_object(v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2108_);
v___x_2117_ = lean_apply_2(v_toPure_2109_, lean_box(0), v___x_2116_);
return v___x_2117_;
}
else
{
lean_object* v___x_2119_; 
lean_dec_ref(v___x_2108_);
lean_inc_ref(v_fst_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2110_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2110_);
v___x_2119_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
v_isSharedCheck_2127_ = !lean_is_exclusive(v_fst_2112_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_fst_2112_, 0);
lean_dec(v_unused_2128_);
v___x_2121_ = v_fst_2112_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v_fst_2112_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2119_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_apply_2(v_toPure_2109_, lean_box(0), v___x_2124_);
return v___x_2125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2132_, lean_object* v_next_2133_, lean_object* v_G_2134_, lean_object* v_____do__lift_2135_){
_start:
{
if (lean_obj_tag(v_____do__lift_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
lean_dec(v_G_2134_);
v_a_2136_ = lean_ctor_get(v_____do__lift_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v_____do__lift_2135_, 1);
v___x_2137_ = lean_apply_2(v_toPure_2132_, lean_box(0), v_a_2136_);
return v___x_2137_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec(v_toPure_2132_);
v_a_2138_ = lean_ctor_get(v_____do__lift_2135_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v_____do__lift_2135_, 1);
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = lean_nat_add(v_next_2133_, v___x_2139_);
v___x_2141_ = lean_apply_4(v_G_2134_, v___x_2140_, v_a_2138_, lean_box(0), lean_box(0));
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2142_, lean_object* v_next_2143_, lean_object* v_G_2144_, lean_object* v_____do__lift_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2142_, v_next_2143_, v_G_2144_, v_____do__lift_2145_);
lean_dec(v_next_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2147_, uint8_t v___x_2148_, lean_object* v_v_2149_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_name_eq(v_v_2149_, v___x_2147_);
if (v___x_2150_ == 0)
{
return v___x_2150_;
}
else
{
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2151_, lean_object* v___x_2152_, lean_object* v_v_2153_){
_start:
{
uint8_t v___x_1551__boxed_2154_; uint8_t v_res_2155_; lean_object* v_r_2156_; 
v___x_1551__boxed_2154_ = lean_unbox(v___x_2152_);
v_res_2155_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2151_, v___x_1551__boxed_2154_, v_v_2153_);
lean_dec(v_v_2153_);
lean_dec(v___x_2151_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2176_, lean_object* v___f_2177_, lean_object* v_resOrder_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_array_2183_; lean_object* v_start_2184_; lean_object* v_stop_2185_; uint8_t v___x_2186_; lean_object* v___y_2188_; 
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_array_get_size(v_resOrder_2178_);
v___x_2181_ = l_Array_toSubarray___redArg(v_resOrder_2178_, v___x_2179_, v___x_2180_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2183_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_ref(v_array_2183_);
v_start_2184_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_start_2184_);
v_stop_2185_ = lean_ctor_get(v___x_2181_, 2);
lean_inc(v_stop_2185_);
lean_dec_ref(v___x_2181_);
v___x_2186_ = lean_nat_dec_lt(v_start_2184_, v_stop_2185_);
if (v___x_2186_ == 0)
{
lean_dec(v_stop_2185_);
lean_dec(v_start_2184_);
lean_dec_ref(v_array_2183_);
lean_dec_ref(v___f_2177_);
return v___x_2176_;
}
else
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_array_get_size(v_array_2183_);
v___x_2196_ = lean_nat_dec_le(v_stop_2185_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_dec(v_stop_2185_);
v___y_2188_ = v___x_2195_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v_stop_2185_;
goto v___jp_2187_;
}
}
v___jp_2187_:
{
uint8_t v___x_2189_; 
v___x_2189_ = lean_nat_dec_lt(v_start_2184_, v___y_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v___y_2188_);
lean_dec(v_start_2184_);
lean_dec_ref(v_array_2183_);
lean_dec_ref(v___f_2177_);
return v___x_2186_;
}
else
{
size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2190_ = lean_usize_of_nat(v_start_2184_);
lean_dec(v_start_2184_);
v___x_2191_ = lean_usize_of_nat(v___y_2188_);
lean_dec(v___y_2188_);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2182_, v___f_2177_, v_array_2183_, v___x_2190_, v___x_2191_);
v___x_2193_ = lean_unbox(v___x_2192_);
lean_dec(v___x_2192_);
if (v___x_2193_ == 0)
{
return v___x_2189_;
}
else
{
uint8_t v___x_2194_; 
v___x_2194_ = 0;
return v___x_2194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2197_, lean_object* v___f_2198_, lean_object* v_resOrder_2199_){
_start:
{
uint8_t v___x_1596__boxed_2200_; uint8_t v_res_2201_; lean_object* v_r_2202_; 
v___x_1596__boxed_2200_ = lean_unbox(v___x_2197_);
v_res_2201_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1596__boxed_2200_, v___f_2198_, v_resOrder_2199_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2203_, uint8_t v___y_2204_, lean_object* v_v_2205_){
_start:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_apply_1(v___f_2203_, v_v_2205_);
v___x_2207_ = lean_unbox(v___x_2206_);
if (v___x_2207_ == 0)
{
return v___y_2204_;
}
else
{
uint8_t v___x_2208_; 
v___x_2208_ = 0;
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2209_, lean_object* v___y_2210_, lean_object* v_v_2211_){
_start:
{
uint8_t v___y_1652__boxed_2212_; uint8_t v_res_2213_; lean_object* v_r_2214_; 
v___y_1652__boxed_2212_ = lean_unbox(v___y_2210_);
v_res_2213_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2209_, v___y_1652__boxed_2212_, v_v_2211_);
v_r_2214_ = lean_box(v_res_2213_);
return v_r_2214_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2215_, uint8_t v___x_2216_, lean_object* v_v_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_apply_1(v___f_2215_, v_v_2217_);
v___x_2219_ = lean_unbox(v___x_2218_);
if (v___x_2219_ == 0)
{
return v___x_2216_;
}
else
{
uint8_t v___x_2220_; 
v___x_2220_ = 0;
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2221_, lean_object* v___x_2222_, lean_object* v_v_2223_){
_start:
{
uint8_t v___x_1664__boxed_2224_; uint8_t v_res_2225_; lean_object* v_r_2226_; 
v___x_1664__boxed_2224_ = lean_unbox(v___x_2222_);
v_res_2225_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2221_, v___x_1664__boxed_2224_, v_v_2223_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2227_, lean_object* v_toPure_2228_, lean_object* v___x_2229_, lean_object* v_resOrders_2230_, lean_object* v___x_2231_, lean_object* v___x_2232_, lean_object* v_toBind_2233_, lean_object* v___f_2234_, lean_object* v___x_2235_, lean_object* v_next_2236_, lean_object* v___x_2237_, lean_object* v_next_2238_, lean_object* v_acc_2239_, lean_object* v_h_2240_, lean_object* v_G_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_nat_dec_lt(v_next_2238_, v___x_2227_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_G_2241_);
lean_dec(v_next_2238_);
lean_dec_ref(v___x_2235_);
lean_dec(v___f_2234_);
lean_dec(v_toBind_2233_);
lean_dec(v___x_2232_);
lean_dec_ref(v_resOrders_2230_);
lean_dec(v___x_2227_);
v___x_2243_ = lean_apply_2(v_toPure_2228_, lean_box(0), v_acc_2239_);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_array_2248_; lean_object* v_start_2249_; lean_object* v_stop_2250_; lean_object* v___f_2251_; lean_object* v___y_2253_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; uint8_t v___y_2283_; uint8_t v___x_2295_; 
lean_dec_ref(v_acc_2239_);
v___x_2244_ = lean_array_get_borrowed(v___x_2229_, v_resOrders_2230_, v_next_2238_);
v___x_2245_ = lean_array_get(v___x_2231_, v___x_2244_, v___x_2232_);
lean_inc_n(v_next_2238_, 2);
lean_inc(v___x_2232_);
lean_inc_ref(v_resOrders_2230_);
v___x_2246_ = l_Array_toSubarray___redArg(v_resOrders_2230_, v___x_2232_, v_next_2238_);
v___x_2247_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2248_ = lean_ctor_get(v___x_2246_, 0);
lean_inc_ref(v_array_2248_);
v_start_2249_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_start_2249_);
v_stop_2250_ = lean_ctor_get(v___x_2246_, 2);
lean_inc(v_stop_2250_);
lean_dec_ref(v___x_2246_);
lean_inc(v_toPure_2228_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2251_, 0, v_toPure_2228_);
lean_closure_set(v___f_2251_, 1, v_next_2238_);
lean_closure_set(v___f_2251_, 2, v_G_2241_);
v___x_2278_ = lean_box(v___x_2242_);
lean_inc(v___x_2245_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_2279_, 0, v___x_2245_);
lean_closure_set(v___f_2279_, 1, v___x_2278_);
v___x_2280_ = lean_box(v___x_2242_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2281_, 0, v___x_2280_);
lean_closure_set(v___f_2281_, 1, v___f_2279_);
v___x_2295_ = lean_nat_dec_lt(v_start_2249_, v_stop_2250_);
if (v___x_2295_ == 0)
{
lean_dec(v_stop_2250_);
lean_dec(v_start_2249_);
lean_dec_ref(v_array_2248_);
v___y_2283_ = v___x_2242_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___y_2299_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2296_ = lean_box(v___x_2242_);
lean_inc_ref(v___f_2281_);
v___f_2297_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2297_, 0, v___f_2281_);
lean_closure_set(v___f_2297_, 1, v___x_2296_);
v___x_2305_ = lean_array_get_size(v_array_2248_);
v___x_2306_ = lean_nat_dec_le(v_stop_2250_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec(v_stop_2250_);
v___y_2299_ = v___x_2305_;
goto v___jp_2298_;
}
else
{
v___y_2299_ = v_stop_2250_;
goto v___jp_2298_;
}
v___jp_2298_:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_nat_dec_lt(v_start_2249_, v___y_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v___y_2299_);
lean_dec_ref(v___f_2297_);
lean_dec(v_start_2249_);
lean_dec_ref(v_array_2248_);
v___y_2283_ = v___x_2295_;
goto v___jp_2282_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2301_ = lean_usize_of_nat(v_start_2249_);
lean_dec(v_start_2249_);
v___x_2302_ = lean_usize_of_nat(v___y_2299_);
lean_dec(v___y_2299_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2247_, v___f_2297_, v_array_2248_, v___x_2301_, v___x_2302_);
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
lean_dec(v___x_2245_);
lean_dec(v_next_2238_);
lean_dec(v___x_2232_);
lean_dec_ref(v_resOrders_2230_);
lean_dec(v___x_2227_);
goto v___jp_2256_;
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_inc(v_toBind_2233_);
v___x_2254_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v___y_2253_, v___f_2234_);
v___x_2255_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v___x_2254_, v___f_2251_);
return v___x_2255_;
}
v___jp_2256_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2235_);
v___x_2258_ = lean_apply_2(v_toPure_2228_, lean_box(0), v___x_2257_);
v___y_2253_ = v___x_2258_;
goto v___jp_2252_;
}
v___jp_2259_:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2260_ = lean_nat_dec_eq(v_next_2236_, v___x_2232_);
lean_dec(v___x_2232_);
v___x_2261_ = lean_box(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2245_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2237_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = lean_apply_2(v_toPure_2228_, lean_box(0), v___x_2265_);
v___y_2253_ = v___x_2266_;
goto v___jp_2252_;
}
v___jp_2267_:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_nat_dec_lt(v___y_2271_, v___y_2272_);
if (v___x_2273_ == 0)
{
lean_dec(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v___x_2235_);
goto v___jp_2259_;
}
else
{
size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2274_ = lean_usize_of_nat(v___y_2271_);
lean_dec(v___y_2271_);
v___x_2275_ = lean_usize_of_nat(v___y_2272_);
lean_dec(v___y_2272_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2269_, v___y_2268_, v___y_2270_, v___x_2274_, v___x_2275_);
v___x_2277_ = lean_unbox(v___x_2276_);
lean_dec(v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v___x_2235_);
goto v___jp_2259_;
}
else
{
lean_dec(v___x_2245_);
lean_dec(v___x_2232_);
goto v___jp_2256_;
}
}
}
v___jp_2282_:
{
if (v___y_2283_ == 0)
{
lean_dec_ref(v___f_2281_);
lean_dec(v___x_2245_);
lean_dec(v_next_2238_);
lean_dec(v___x_2232_);
lean_dec_ref(v_resOrders_2230_);
lean_dec(v___x_2227_);
goto v___jp_2256_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_array_2287_; lean_object* v_start_2288_; lean_object* v_stop_2289_; uint8_t v___x_2290_; 
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_next_2238_, v___x_2284_);
lean_dec(v_next_2238_);
v___x_2286_ = l_Array_toSubarray___redArg(v_resOrders_2230_, v___x_2285_, v___x_2227_);
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
lean_dec_ref(v___x_2235_);
goto v___jp_2259_;
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
v___y_2268_ = v___f_2292_;
v___y_2269_ = v___x_2247_;
v___y_2270_ = v_array_2287_;
v___y_2271_ = v_start_2288_;
v___y_2272_ = v___x_2293_;
goto v___jp_2267_;
}
else
{
v___y_2268_ = v___f_2292_;
v___y_2269_ = v___x_2247_;
v___y_2270_ = v_array_2287_;
v___y_2271_ = v_start_2288_;
v___y_2272_ = v_stop_2289_;
goto v___jp_2267_;
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_toPure_2407_, lean_object* v_____s_2408_){
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2420_, lean_object* v_____do__lift_2421_){
_start:
{
if (lean_obj_tag(v_____do__lift_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_a_2422_ = lean_ctor_get(v_____do__lift_2421_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_____do__lift_2421_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2424_ = v_____do__lift_2421_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v_____do__lift_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set_tag(v___x_2424_, 1);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_apply_2(v_toPure_2420_, lean_box(0), v___x_2427_);
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2439_; 
v_a_2431_ = lean_ctor_get(v_____do__lift_2421_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_____do__lift_2421_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2433_ = v_____do__lift_2421_;
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v_____do__lift_2421_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 0);
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_apply_2(v_toPure_2420_, lean_box(0), v___x_2436_);
return v___x_2437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2440_, lean_object* v___f_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2443_ = lean_array_get_size(v_x_2442_);
v___x_2444_ = lean_mk_empty_array_with_capacity(v___x_2440_);
v___x_2445_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2446_ = lean_nat_dec_lt(v___x_2440_, v___x_2443_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v_x_2442_);
lean_dec_ref(v___f_2441_);
return v___x_2444_;
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_nat_dec_le(v___x_2443_, v___x_2443_);
if (v___x_2447_ == 0)
{
if (v___x_2446_ == 0)
{
lean_dec_ref(v_x_2442_);
lean_dec_ref(v___f_2441_);
return v___x_2444_;
}
else
{
size_t v___x_2448_; size_t v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = lean_usize_of_nat(v___x_2443_);
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2445_, v___f_2441_, v_x_2442_, v___x_2448_, v___x_2449_, v___x_2444_);
return v___x_2450_;
}
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2443_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2445_, v___f_2441_, v_x_2442_, v___x_2451_, v___x_2452_, v___x_2444_);
return v___x_2453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v___x_2454_, lean_object* v___f_2455_, lean_object* v_x_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v___x_2454_, v___f_2455_, v_x_2456_);
lean_dec(v___x_2454_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v_snd_2458_, lean_object* v_x1_2459_, lean_object* v_x2_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_name_eq(v_x2_2460_, v_snd_2458_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_array_push(v_x1_2459_, v_x2_2460_);
return v___x_2462_;
}
else
{
lean_dec(v_x2_2460_);
return v_x1_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v_snd_2463_, lean_object* v_x1_2464_, lean_object* v_x2_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v_snd_2463_, v_x1_2464_, v_x2_2465_);
lean_dec(v_snd_2463_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2467_, lean_object* v___f_2468_, lean_object* v_x1_2469_, lean_object* v_x2_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_array_2474_; lean_object* v_start_2475_; lean_object* v_stop_2476_; lean_object* v___y_2478_; uint8_t v___x_2485_; 
v___x_2471_ = lean_array_get_size(v_x2_2470_);
lean_inc_ref(v_x2_2470_);
v___x_2472_ = l_Array_toSubarray___redArg(v_x2_2470_, v___x_2467_, v___x_2471_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2474_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_array_2474_);
v_start_2475_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_start_2475_);
v_stop_2476_ = lean_ctor_get(v___x_2472_, 2);
lean_inc(v_stop_2476_);
lean_dec_ref(v___x_2472_);
v___x_2485_ = lean_nat_dec_lt(v_start_2475_, v_stop_2476_);
if (v___x_2485_ == 0)
{
lean_dec(v_stop_2476_);
lean_dec(v_start_2475_);
lean_dec_ref(v_array_2474_);
lean_dec_ref(v_x2_2470_);
lean_dec_ref(v___f_2468_);
return v_x1_2469_;
}
else
{
lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = lean_array_get_size(v_array_2474_);
v___x_2487_ = lean_nat_dec_le(v_stop_2476_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_dec(v_stop_2476_);
v___y_2478_ = v___x_2486_;
goto v___jp_2477_;
}
else
{
v___y_2478_ = v_stop_2476_;
goto v___jp_2477_;
}
}
v___jp_2477_:
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_nat_dec_lt(v_start_2475_, v___y_2478_);
if (v___x_2479_ == 0)
{
lean_dec(v___y_2478_);
lean_dec(v_start_2475_);
lean_dec_ref(v_array_2474_);
lean_dec_ref(v_x2_2470_);
lean_dec_ref(v___f_2468_);
return v_x1_2469_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2480_ = lean_usize_of_nat(v_start_2475_);
lean_dec(v_start_2475_);
v___x_2481_ = lean_usize_of_nat(v___y_2478_);
lean_dec(v___y_2478_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2473_, v___f_2468_, v_array_2474_, v___x_2480_, v___x_2481_);
v___x_2483_ = lean_unbox(v___x_2482_);
lean_dec(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v_x2_2470_);
return v_x1_2469_;
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_array_push(v_x1_2469_, v_x2_2470_);
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2488_, lean_object* v_x_2489_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_name_eq(v_x_2489_, v_snd_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec(v_snd_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2496_, lean_object* v___x_2497_, lean_object* v_fst_2498_, lean_object* v_fst_2499_, lean_object* v___f_2500_, uint8_t v_relaxed_2501_, lean_object* v___x_2502_, lean_object* v_parentNames_2503_, lean_object* v___f_2504_, lean_object* v_snd_2505_, lean_object* v___f_2506_, lean_object* v___x_2507_, lean_object* v_____x_2508_){
_start:
{
lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v_fst_2517_; lean_object* v_snd_2518_; lean_object* v___f_2519_; lean_object* v___f_2520_; lean_object* v_defects_2522_; lean_object* v___y_2537_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2561_; uint8_t v___x_2571_; 
v_fst_2517_ = lean_ctor_get(v_____x_2508_, 0);
lean_inc(v_fst_2517_);
v_snd_2518_ = lean_ctor_get(v_____x_2508_, 1);
lean_inc_n(v_snd_2518_, 2);
lean_dec_ref(v_____x_2508_);
v___f_2519_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2519_, 0, v_snd_2518_);
lean_inc(v___x_2497_);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 3, 2);
lean_closure_set(v___f_2520_, 0, v___x_2497_);
lean_closure_set(v___f_2520_, 1, v___f_2519_);
v___x_2571_ = lean_unbox(v_fst_2517_);
lean_dec(v_fst_2517_);
if (v___x_2571_ == 0)
{
if (v_relaxed_2501_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2572_ = lean_array_get_size(v_fst_2499_);
v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2497_);
v___x_2574_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2575_ = lean_nat_dec_lt(v___x_2497_, v___x_2572_);
if (v___x_2575_ == 0)
{
v___y_2561_ = v___x_2573_;
goto v___jp_2560_;
}
else
{
lean_object* v___f_2576_; lean_object* v___f_2577_; uint8_t v___x_2578_; 
lean_inc(v_snd_2518_);
v___f_2576_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2576_, 0, v_snd_2518_);
lean_inc(v___x_2507_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2577_, 0, v___x_2507_);
lean_closure_set(v___f_2577_, 1, v___f_2576_);
v___x_2578_ = lean_nat_dec_le(v___x_2572_, v___x_2572_);
if (v___x_2578_ == 0)
{
if (v___x_2575_ == 0)
{
lean_dec_ref(v___f_2577_);
v___y_2561_ = v___x_2573_;
goto v___jp_2560_;
}
else
{
size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2572_);
lean_inc(v_fst_2499_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2574_, v___f_2577_, v_fst_2499_, v___x_2579_, v___x_2580_, v___x_2573_);
v___y_2561_ = v___x_2581_;
goto v___jp_2560_;
}
}
else
{
size_t v___x_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = lean_usize_of_nat(v___x_2572_);
lean_inc(v_fst_2499_);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2574_, v___f_2577_, v_fst_2499_, v___x_2582_, v___x_2583_, v___x_2573_);
v___y_2561_ = v___x_2584_;
goto v___jp_2560_;
}
}
}
else
{
lean_dec(v___x_2507_);
lean_dec_ref(v___f_2506_);
lean_dec_ref(v___f_2504_);
lean_dec_ref(v_parentNames_2503_);
lean_dec_ref(v___x_2502_);
v_defects_2522_ = v_snd_2505_;
goto v___jp_2521_;
}
}
else
{
lean_dec(v___x_2507_);
lean_dec_ref(v___f_2506_);
lean_dec_ref(v___f_2504_);
lean_dec_ref(v_parentNames_2503_);
lean_dec_ref(v___x_2502_);
v_defects_2522_ = v_snd_2505_;
goto v___jp_2521_;
}
v___jp_2509_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2510_);
lean_ctor_set(v___x_2513_, 1, v___y_2511_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
v___x_2516_ = lean_apply_2(v_toPure_2496_, lean_box(0), v___x_2515_);
return v___x_2516_;
}
v___jp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; size_t v_sz_2525_; size_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2523_ = lean_array_push(v_fst_2498_, v_snd_2518_);
v___x_2524_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2525_ = lean_array_size(v_fst_2499_);
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2524_, v___f_2520_, v_sz_2525_, v___x_2526_, v_fst_2499_);
v___x_2528_ = lean_array_get_size(v___x_2527_);
v___x_2529_ = lean_mk_empty_array_with_capacity(v___x_2497_);
v___x_2530_ = lean_nat_dec_lt(v___x_2497_, v___x_2528_);
lean_dec(v___x_2497_);
if (v___x_2530_ == 0)
{
lean_dec(v___x_2527_);
lean_dec_ref(v___f_2500_);
v___y_2510_ = v___x_2523_;
v___y_2511_ = v_defects_2522_;
v___y_2512_ = v___x_2529_;
goto v___jp_2509_;
}
else
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_nat_dec_le(v___x_2528_, v___x_2528_);
if (v___x_2531_ == 0)
{
if (v___x_2530_ == 0)
{
lean_dec(v___x_2527_);
lean_dec_ref(v___f_2500_);
v___y_2510_ = v___x_2523_;
v___y_2511_ = v_defects_2522_;
v___y_2512_ = v___x_2529_;
goto v___jp_2509_;
}
else
{
size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_usize_of_nat(v___x_2528_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2524_, v___f_2500_, v___x_2527_, v___x_2526_, v___x_2532_, v___x_2529_);
v___y_2510_ = v___x_2523_;
v___y_2511_ = v_defects_2522_;
v___y_2512_ = v___x_2533_;
goto v___jp_2509_;
}
}
else
{
size_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_usize_of_nat(v___x_2528_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2524_, v___f_2500_, v___x_2527_, v___x_2526_, v___x_2534_, v___x_2529_);
v___y_2510_ = v___x_2523_;
v___y_2511_ = v_defects_2522_;
v___y_2512_ = v___x_2535_;
goto v___jp_2509_;
}
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; size_t v_sz_2541_; size_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_inc_ref(v___x_2502_);
v___x_2538_ = l_Array_eraseReps___redArg(v___x_2502_, v___y_2537_);
lean_inc_n(v_snd_2518_, 2);
v___x_2539_ = l_Array_contains___redArg(v___x_2502_, v_parentNames_2503_, v_snd_2518_);
v___x_2540_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2541_ = lean_array_size(v___x_2538_);
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2540_, v___f_2504_, v_sz_2541_, v___x_2542_, v___x_2538_);
v___x_2544_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2544_, 0, v_snd_2518_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_ctor_set_uint8(v___x_2544_, sizeof(void*)*2, v___x_2539_);
v___x_2545_ = lean_array_push(v_snd_2505_, v___x_2544_);
v_defects_2522_ = v___x_2545_;
goto v___jp_2521_;
}
v___jp_2546_:
{
lean_object* v___x_2552_; 
lean_inc_ref(v___y_2550_);
v___x_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2550_, v___y_2549_, v___y_2547_, v___y_2548_, v___y_2551_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2551_);
lean_dec(v___y_2549_);
v___y_2537_ = v___x_2552_;
goto v___jp_2536_;
}
v___jp_2553_:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_nat_dec_le(v___y_2558_, v___y_2554_);
if (v___x_2559_ == 0)
{
lean_dec(v___y_2554_);
lean_inc(v___y_2558_);
v___y_2547_ = v___y_2555_;
v___y_2548_ = v___y_2558_;
v___y_2549_ = v___y_2556_;
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2558_;
goto v___jp_2546_;
}
else
{
v___y_2547_ = v___y_2555_;
v___y_2548_ = v___y_2558_;
v___y_2549_ = v___y_2556_;
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2554_;
goto v___jp_2546_;
}
}
v___jp_2560_:
{
lean_object* v___x_2562_; size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2563_ = lean_array_size(v___y_2561_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2562_, v___f_2506_, v_sz_2563_, v___x_2564_, v___y_2561_);
v___x_2566_ = lean_array_get_size(v___x_2565_);
v___x_2567_ = lean_nat_dec_eq(v___x_2566_, v___x_2497_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2569_ = lean_nat_sub(v___x_2566_, v___x_2507_);
lean_dec(v___x_2507_);
v___x_2570_ = lean_nat_dec_le(v___x_2497_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_inc(v___x_2569_);
v___y_2554_ = v___x_2569_;
v___y_2555_ = v___x_2565_;
v___y_2556_ = v___x_2566_;
v___y_2557_ = v___x_2568_;
v___y_2558_ = v___x_2569_;
goto v___jp_2553_;
}
else
{
lean_inc(v___x_2497_);
v___y_2554_ = v___x_2569_;
v___y_2555_ = v___x_2565_;
v___y_2556_ = v___x_2566_;
v___y_2557_ = v___x_2568_;
v___y_2558_ = v___x_2497_;
goto v___jp_2553_;
}
}
else
{
lean_dec(v___x_2507_);
v___y_2537_ = v___x_2565_;
goto v___jp_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2585_, lean_object* v___x_2586_, lean_object* v_fst_2587_, lean_object* v_fst_2588_, lean_object* v___f_2589_, lean_object* v_relaxed_2590_, lean_object* v___x_2591_, lean_object* v_parentNames_2592_, lean_object* v___f_2593_, lean_object* v_snd_2594_, lean_object* v___f_2595_, lean_object* v___x_2596_, lean_object* v_____x_2597_){
_start:
{
uint8_t v_relaxed_boxed_2598_; lean_object* v_res_2599_; 
v_relaxed_boxed_2598_ = lean_unbox(v_relaxed_2590_);
v_res_2599_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2585_, v___x_2586_, v_fst_2587_, v_fst_2588_, v___f_2589_, v_relaxed_boxed_2598_, v___x_2591_, v_parentNames_2592_, v___f_2593_, v_snd_2594_, v___f_2595_, v___x_2596_, v_____x_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2600_, lean_object* v_toPure_2601_, lean_object* v___f_2602_, uint8_t v_relaxed_2603_, lean_object* v___x_2604_, lean_object* v_parentNames_2605_, lean_object* v___f_2606_, lean_object* v___f_2607_, lean_object* v___x_2608_, lean_object* v_inst_2609_, lean_object* v_toBind_2610_, lean_object* v___f_2611_, lean_object* v_b_2612_){
_start:
{
lean_object* v_snd_2613_; lean_object* v_fst_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2640_; 
v_snd_2613_ = lean_ctor_get(v_b_2612_, 1);
v_fst_2614_ = lean_ctor_get(v_b_2612_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_b_2612_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2616_ = v_b_2612_;
v_isShared_2617_ = v_isSharedCheck_2640_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2613_);
lean_inc(v_fst_2614_);
lean_dec(v_b_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2640_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2639_; 
v_fst_2618_ = lean_ctor_get(v_snd_2613_, 0);
v_snd_2619_ = lean_ctor_get(v_snd_2613_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_snd_2613_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2621_ = v_snd_2613_;
v_isShared_2622_ = v_isSharedCheck_2639_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_snd_2619_);
lean_inc(v_fst_2618_);
lean_dec(v_snd_2613_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2639_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_array_get_size(v_fst_2614_);
v___x_2624_ = lean_nat_dec_eq(v___x_2623_, v___x_2600_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_del_object(v___x_2621_);
lean_del_object(v___x_2616_);
v___x_2625_ = lean_box(v_relaxed_2603_);
lean_inc(v_fst_2614_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 13, 12);
lean_closure_set(v___f_2626_, 0, v_toPure_2601_);
lean_closure_set(v___f_2626_, 1, v___x_2600_);
lean_closure_set(v___f_2626_, 2, v_fst_2618_);
lean_closure_set(v___f_2626_, 3, v_fst_2614_);
lean_closure_set(v___f_2626_, 4, v___f_2602_);
lean_closure_set(v___f_2626_, 5, v___x_2625_);
lean_closure_set(v___f_2626_, 6, v___x_2604_);
lean_closure_set(v___f_2626_, 7, v_parentNames_2605_);
lean_closure_set(v___f_2626_, 8, v___f_2606_);
lean_closure_set(v___f_2626_, 9, v_snd_2619_);
lean_closure_set(v___f_2626_, 10, v___f_2607_);
lean_closure_set(v___f_2626_, 11, v___x_2608_);
v___x_2627_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2609_, v_fst_2614_);
lean_inc(v_toBind_2610_);
v___x_2628_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2627_, v___f_2626_);
v___x_2629_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2628_, v___f_2611_);
return v___x_2629_;
}
else
{
lean_object* v___x_2631_; 
lean_dec_ref(v_inst_2609_);
lean_dec(v___x_2608_);
lean_dec_ref(v___f_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v_parentNames_2605_);
lean_dec_ref(v___x_2604_);
lean_dec_ref(v___f_2602_);
lean_dec(v___x_2600_);
if (v_isShared_2622_ == 0)
{
v___x_2631_ = v___x_2621_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_fst_2618_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_snd_2619_);
v___x_2631_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___x_2631_);
v___x_2633_ = v___x_2616_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = lean_apply_2(v_toPure_2601_, lean_box(0), v___x_2634_);
v___x_2636_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2635_, v___f_2611_);
return v___x_2636_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2641_, lean_object* v_toPure_2642_, lean_object* v___f_2643_, lean_object* v_relaxed_2644_, lean_object* v___x_2645_, lean_object* v_parentNames_2646_, lean_object* v___f_2647_, lean_object* v___f_2648_, lean_object* v___x_2649_, lean_object* v_inst_2650_, lean_object* v_toBind_2651_, lean_object* v___f_2652_, lean_object* v_b_2653_){
_start:
{
uint8_t v_relaxed_boxed_2654_; lean_object* v_res_2655_; 
v_relaxed_boxed_2654_ = lean_unbox(v_relaxed_2644_);
v_res_2655_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2641_, v_toPure_2642_, v___f_2643_, v_relaxed_boxed_2654_, v___x_2645_, v_parentNames_2646_, v___f_2647_, v___f_2648_, v___x_2649_, v_inst_2650_, v_toBind_2651_, v___f_2652_, v_b_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2656_, lean_object* v___x_2657_, lean_object* v_x_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_array_get_borrowed(v___x_2656_, v_x_2658_, v___x_2657_);
lean_inc(v___x_2659_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2660_, lean_object* v___x_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2660_, v___x_2661_, v_x_2662_);
lean_dec_ref(v_x_2662_);
lean_dec(v___x_2661_);
lean_dec(v___x_2660_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v___x_2666_, lean_object* v_toPure_2667_, lean_object* v___f_2668_, uint8_t v_relaxed_2669_, lean_object* v___x_2670_, lean_object* v_parentNames_2671_, lean_object* v___f_2672_, lean_object* v_inst_2673_, lean_object* v_toBind_2674_, lean_object* v___f_2675_, lean_object* v_structName_2676_, lean_object* v___f_2677_, lean_object* v___f_2678_, lean_object* v_parentResOrders_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v___f_2681_; lean_object* v___y_2683_; lean_object* v_j_2694_; lean_object* v_as_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2680_ = lean_unsigned_to_nat(0u);
v___f_2681_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2681_, 0, v___x_2666_);
lean_closure_set(v___f_2681_, 1, v___x_2680_);
v_j_2694_ = lean_array_get_size(v_parentResOrders_2679_);
lean_inc_ref(v_parentNames_2671_);
v_as_2695_ = lean_array_push(v_parentResOrders_2679_, v_parentNames_2671_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2680_, v_as_2695_, v_j_2694_);
v___x_2697_ = lean_array_get_size(v___x_2696_);
v___x_2698_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v___x_2699_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2700_ = lean_nat_dec_lt(v___x_2680_, v___x_2697_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2678_);
v___y_2683_ = v___x_2698_;
goto v___jp_2682_;
}
else
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_nat_dec_le(v___x_2697_, v___x_2697_);
if (v___x_2701_ == 0)
{
if (v___x_2700_ == 0)
{
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2678_);
v___y_2683_ = v___x_2698_;
goto v___jp_2682_;
}
else
{
size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = lean_usize_of_nat(v___x_2697_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2699_, v___f_2678_, v___x_2696_, v___x_2702_, v___x_2703_, v___x_2698_);
v___y_2683_ = v___x_2704_;
goto v___jp_2682_;
}
}
else
{
size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = lean_usize_of_nat(v___x_2697_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2699_, v___f_2678_, v___x_2696_, v___x_2705_, v___x_2706_, v___x_2698_);
v___y_2683_ = v___x_2707_;
goto v___jp_2682_;
}
}
v___jp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; lean_object* v_resOrder_2688_; lean_object* v_defects_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_box(v_relaxed_2669_);
lean_inc(v_toBind_2674_);
lean_inc_ref(v_inst_2673_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_2686_, 0, v___x_2680_);
lean_closure_set(v___f_2686_, 1, v_toPure_2667_);
lean_closure_set(v___f_2686_, 2, v___f_2668_);
lean_closure_set(v___f_2686_, 3, v___x_2685_);
lean_closure_set(v___f_2686_, 4, v___x_2670_);
lean_closure_set(v___f_2686_, 5, v_parentNames_2671_);
lean_closure_set(v___f_2686_, 6, v___f_2672_);
lean_closure_set(v___f_2686_, 7, v___f_2681_);
lean_closure_set(v___f_2686_, 8, v___x_2684_);
lean_closure_set(v___f_2686_, 9, v_inst_2673_);
lean_closure_set(v___f_2686_, 10, v_toBind_2674_);
lean_closure_set(v___f_2686_, 11, v___f_2675_);
v___x_2687_ = lean_mk_empty_array_with_capacity(v___x_2684_);
v_resOrder_2688_ = lean_array_push(v___x_2687_, v_structName_2676_);
v_defects_2689_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_resOrder_2688_);
lean_ctor_set(v___x_2690_, 1, v_defects_2689_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2683_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2673_, v___f_2686_, v___x_2691_);
v___x_2693_ = lean_apply_4(v_toBind_2674_, lean_box(0), lean_box(0), v___x_2692_, v___f_2677_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v___x_2708_, lean_object* v_toPure_2709_, lean_object* v___f_2710_, lean_object* v_relaxed_2711_, lean_object* v___x_2712_, lean_object* v_parentNames_2713_, lean_object* v___f_2714_, lean_object* v_inst_2715_, lean_object* v_toBind_2716_, lean_object* v___f_2717_, lean_object* v_structName_2718_, lean_object* v___f_2719_, lean_object* v___f_2720_, lean_object* v_parentResOrders_2721_){
_start:
{
uint8_t v_relaxed_boxed_2722_; lean_object* v_res_2723_; 
v_relaxed_boxed_2722_ = lean_unbox(v_relaxed_2711_);
v_res_2723_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v___x_2708_, v_toPure_2709_, v___f_2710_, v_relaxed_boxed_2722_, v___x_2712_, v_parentNames_2713_, v___f_2714_, v_inst_2715_, v_toBind_2716_, v___f_2717_, v_structName_2718_, v___f_2719_, v___f_2720_, v_parentResOrders_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2725_ = lean_array_get_size(v_x_2724_);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = lean_nat_dec_eq(v___x_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
uint8_t v___x_2728_; 
v___x_2728_ = 1;
return v___x_2728_;
}
else
{
uint8_t v___x_2729_; 
v___x_2729_ = 0;
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2730_){
_start:
{
uint8_t v_res_2731_; lean_object* v_r_2732_; 
v_res_2731_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2730_);
lean_dec_ref(v_x_2730_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2733_, lean_object* v_x1_2734_, lean_object* v_x2_2735_){
_start:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
lean_inc_ref(v_x2_2735_);
v___x_2736_ = lean_apply_1(v___f_2733_, v_x2_2735_);
v___x_2737_ = lean_unbox(v___x_2736_);
if (v___x_2737_ == 0)
{
lean_dec_ref(v_x2_2735_);
return v_x1_2734_;
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_array_push(v_x1_2734_, v_x2_2735_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_toPure_2739_, lean_object* v_____do__lift_2740_){
_start:
{
lean_object* v_resolutionOrder_2741_; lean_object* v___x_2742_; 
v_resolutionOrder_2741_ = lean_ctor_get(v_____do__lift_2740_, 0);
lean_inc_ref(v_resolutionOrder_2741_);
lean_dec_ref(v_____do__lift_2740_);
v___x_2742_ = lean_apply_2(v_toPure_2739_, lean_box(0), v_resolutionOrder_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v___x_2743_, lean_object* v_parentNames_2744_, lean_object* v_x_2745_){
_start:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_inc(v_x_2745_);
v___x_2746_ = l_Array_contains___redArg(v___x_2743_, v_parentNames_2744_, v_x_2745_);
v___x_2747_ = lean_box(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v_x_2745_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_structName_2755_, lean_object* v_parentNames_2756_, uint8_t v_relaxed_2757_){
_start:
{
lean_object* v_toApplicative_2758_; lean_object* v_toBind_2759_; lean_object* v_toPure_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_toApplicative_2758_ = lean_ctor_get(v_inst_2753_, 0);
v_toBind_2759_ = lean_ctor_get(v_inst_2753_, 1);
lean_inc_n(v_toBind_2759_, 3);
v_toPure_2760_ = lean_ctor_get(v_toApplicative_2758_, 1);
v___f_2761_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
v___x_2762_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref_n(v_parentNames_2756_, 2);
v___f_2763_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 3, 2);
lean_closure_set(v___f_2763_, 0, v___x_2762_);
lean_closure_set(v___f_2763_, 1, v_parentNames_2756_);
v___x_2764_ = lean_box(0);
lean_inc_n(v_toPure_2760_, 4);
v___f_2765_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2765_, 0, v_toPure_2760_);
lean_inc_ref_n(v_inst_2753_, 2);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2766_, 0, v_inst_2753_);
lean_closure_set(v___f_2766_, 1, v_inst_2754_);
lean_closure_set(v___f_2766_, 2, v_toBind_2759_);
lean_closure_set(v___f_2766_, 3, v___f_2765_);
v___f_2767_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2767_, 0, v_toPure_2760_);
v___f_2768_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6), 2, 1);
lean_closure_set(v___f_2768_, 0, v_toPure_2760_);
v___x_2769_ = lean_box(v_relaxed_2757_);
v___f_2770_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 14, 13);
lean_closure_set(v___f_2770_, 0, v___x_2764_);
lean_closure_set(v___f_2770_, 1, v_toPure_2760_);
lean_closure_set(v___f_2770_, 2, v___f_2761_);
lean_closure_set(v___f_2770_, 3, v___x_2769_);
lean_closure_set(v___f_2770_, 4, v___x_2762_);
lean_closure_set(v___f_2770_, 5, v_parentNames_2756_);
lean_closure_set(v___f_2770_, 6, v___f_2763_);
lean_closure_set(v___f_2770_, 7, v_inst_2753_);
lean_closure_set(v___f_2770_, 8, v_toBind_2759_);
lean_closure_set(v___f_2770_, 9, v___f_2767_);
lean_closure_set(v___f_2770_, 10, v_structName_2755_);
lean_closure_set(v___f_2770_, 11, v___f_2768_);
lean_closure_set(v___f_2770_, 12, v___f_2761_);
v_sz_2771_ = lean_array_size(v_parentNames_2756_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2753_, v___f_2766_, v_sz_2771_, v___x_2772_, v_parentNames_2756_);
v___x_2774_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v___x_2773_, v___f_2770_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2775_, lean_object* v_toPure_2776_, lean_object* v___f_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, uint8_t v_relaxed_2780_, lean_object* v_toBind_2781_, lean_object* v___f_2782_, lean_object* v_env_2783_){
_start:
{
lean_object* v___x_2784_; 
lean_inc_ref(v_env_2783_);
v___x_2784_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2783_, v_structName_2775_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v_val_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec_ref(v_env_2783_);
lean_dec(v___f_2782_);
lean_dec(v_toBind_2781_);
lean_dec_ref(v_inst_2779_);
lean_dec_ref(v_inst_2778_);
lean_dec_ref(v___f_2777_);
lean_dec(v_structName_2775_);
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_val_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = lean_apply_2(v_toPure_2776_, lean_box(0), v___x_2787_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; size_t v_sz_2791_; size_t v___x_2792_; lean_object* v_parentNames_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec(v___x_2784_);
lean_dec(v_toPure_2776_);
lean_inc(v_structName_2775_);
v___x_2789_ = l_Lean_getStructureParentInfo(v_env_2783_, v_structName_2775_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2791_ = lean_array_size(v___x_2789_);
v___x_2792_ = ((size_t)0ULL);
v_parentNames_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2790_, v___f_2777_, v_sz_2791_, v___x_2792_, v___x_2789_);
v___x_2794_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2778_, v_inst_2779_, v_structName_2775_, v_parentNames_2793_, v_relaxed_2780_);
v___x_2795_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v___x_2794_, v___f_2782_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2796_, lean_object* v_toPure_2797_, lean_object* v___f_2798_, lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_relaxed_2801_, lean_object* v_toBind_2802_, lean_object* v___f_2803_, lean_object* v_env_2804_){
_start:
{
uint8_t v_relaxed_boxed_2805_; lean_object* v_res_2806_; 
v_relaxed_boxed_2805_ = lean_unbox(v_relaxed_2801_);
v_res_2806_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2796_, v_toPure_2797_, v___f_2798_, v_inst_2799_, v_inst_2800_, v_relaxed_boxed_2805_, v_toBind_2802_, v___f_2803_, v_env_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2807_, lean_object* v_inst_2808_, lean_object* v_structName_2809_, uint8_t v_relaxed_2810_){
_start:
{
lean_object* v_toApplicative_2811_; lean_object* v_toBind_2812_; lean_object* v_getEnv_2813_; lean_object* v_toPure_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; 
v_toApplicative_2811_ = lean_ctor_get(v_inst_2807_, 0);
v_toBind_2812_ = lean_ctor_get(v_inst_2807_, 1);
lean_inc_n(v_toBind_2812_, 3);
v_getEnv_2813_ = lean_ctor_get(v_inst_2808_, 0);
lean_inc(v_getEnv_2813_);
v_toPure_2814_ = lean_ctor_get(v_toApplicative_2811_, 1);
lean_inc_n(v_toPure_2814_, 2);
v___f_2815_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2809_);
lean_inc_ref(v_inst_2808_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2816_, 0, v_toPure_2814_);
lean_closure_set(v___f_2816_, 1, v_inst_2808_);
lean_closure_set(v___f_2816_, 2, v_structName_2809_);
lean_closure_set(v___f_2816_, 3, v_toBind_2812_);
v___x_2817_ = lean_box(v_relaxed_2810_);
v___f_2818_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2818_, 0, v_structName_2809_);
lean_closure_set(v___f_2818_, 1, v_toPure_2814_);
lean_closure_set(v___f_2818_, 2, v___f_2815_);
lean_closure_set(v___f_2818_, 3, v_inst_2807_);
lean_closure_set(v___f_2818_, 4, v_inst_2808_);
lean_closure_set(v___f_2818_, 5, v___x_2817_);
lean_closure_set(v___f_2818_, 6, v_toBind_2812_);
lean_closure_set(v___f_2818_, 7, v___f_2816_);
v___x_2819_ = lean_apply_4(v_toBind_2812_, lean_box(0), lean_box(0), v_getEnv_2813_, v___f_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_toBind_2822_, lean_object* v___f_2823_, lean_object* v_parentName_2824_){
_start:
{
uint8_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = 1;
v___x_2826_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2820_, v_inst_2821_, v_parentName_2824_, v___x_2825_);
v___x_2827_ = lean_apply_4(v_toBind_2822_, lean_box(0), lean_box(0), v___x_2826_, v___f_2823_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_structName_2830_, lean_object* v_relaxed_2831_){
_start:
{
uint8_t v_relaxed_boxed_2832_; lean_object* v_res_2833_; 
v_relaxed_boxed_2832_ = lean_unbox(v_relaxed_2831_);
v_res_2833_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2828_, v_inst_2829_, v_structName_2830_, v_relaxed_boxed_2832_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_structName_2836_, lean_object* v_parentNames_2837_, lean_object* v_relaxed_2838_){
_start:
{
uint8_t v_relaxed_boxed_2839_; lean_object* v_res_2840_; 
v_relaxed_boxed_2839_ = lean_unbox(v_relaxed_2838_);
v_res_2840_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2834_, v_inst_2835_, v_structName_2836_, v_parentNames_2837_, v_relaxed_boxed_2839_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_structName_2844_, uint8_t v_relaxed_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2842_, v_inst_2843_, v_structName_2844_, v_relaxed_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_structName_2850_, lean_object* v_relaxed_2851_){
_start:
{
uint8_t v_relaxed_boxed_2852_; lean_object* v_res_2853_; 
v_relaxed_boxed_2852_ = lean_unbox(v_relaxed_2851_);
v_res_2853_ = l_Lean_computeStructureResolutionOrder(v_m_2847_, v_inst_2848_, v_inst_2849_, v_structName_2850_, v_relaxed_boxed_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_structName_2857_, lean_object* v_parentNames_2858_, uint8_t v_relaxed_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2855_, v_inst_2856_, v_structName_2857_, v_parentNames_2858_, v_relaxed_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_structName_2864_, lean_object* v_parentNames_2865_, lean_object* v_relaxed_2866_){
_start:
{
uint8_t v_relaxed_boxed_2867_; lean_object* v_res_2868_; 
v_relaxed_boxed_2867_ = lean_unbox(v_relaxed_2866_);
v_res_2868_ = l_Lean_mergeStructureResolutionOrders(v_m_2861_, v_inst_2862_, v_inst_2863_, v_structName_2864_, v_parentNames_2865_, v_relaxed_boxed_2867_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2869_){
_start:
{
lean_object* v_resolutionOrder_2870_; 
v_resolutionOrder_2870_ = lean_ctor_get(v_x_2869_, 0);
lean_inc_ref(v_resolutionOrder_2870_);
return v_resolutionOrder_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2871_);
lean_dec_ref(v_x_2871_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_structName_2876_){
_start:
{
lean_object* v_toApplicative_2877_; lean_object* v_toFunctor_2878_; lean_object* v_map_2879_; lean_object* v___f_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_toApplicative_2877_ = lean_ctor_get(v_inst_2874_, 0);
v_toFunctor_2878_ = lean_ctor_get(v_toApplicative_2877_, 0);
v_map_2879_ = lean_ctor_get(v_toFunctor_2878_, 0);
lean_inc(v_map_2879_);
v___f_2880_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2881_ = 1;
v___x_2882_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2874_, v_inst_2875_, v_structName_2876_, v___x_2881_);
v___x_2883_ = lean_apply_4(v_map_2879_, lean_box(0), lean_box(0), v___f_2880_, v___x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_structName_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2885_, v_inst_2886_, v_structName_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2889_, lean_object* v_structName_2890_, lean_object* v_x_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Array_erase___redArg(v___x_2889_, v_x_2891_, v_structName_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_structName_2895_){
_start:
{
lean_object* v_toApplicative_2896_; lean_object* v_toFunctor_2897_; lean_object* v_map_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_toApplicative_2896_ = lean_ctor_get(v_inst_2893_, 0);
v_toFunctor_2897_ = lean_ctor_get(v_toApplicative_2896_, 0);
v_map_2898_ = lean_ctor_get(v_toFunctor_2897_, 0);
lean_inc(v_map_2898_);
v___x_2899_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2895_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2900_, 0, v___x_2899_);
lean_closure_set(v___f_2900_, 1, v_structName_2895_);
v___x_2901_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2893_, v_inst_2894_, v_structName_2895_);
v___x_2902_ = lean_apply_4(v_map_2898_, lean_box(0), lean_box(0), v___f_2900_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_structName_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_getAllParentStructures___redArg(v_inst_2904_, v_inst_2905_, v_structName_2906_);
return v___x_2907_;
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
