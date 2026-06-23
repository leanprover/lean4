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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0;
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; uint64_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1723u);
v___x_520_ = lean_uint64_of_nat(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_522_, size_t v_x_523_, size_t v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_es_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v_j_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_es_527_ = lean_ctor_get(v_x_522_, 0);
v___x_528_ = ((size_t)31ULL);
v___x_529_ = lean_usize_land(v_x_523_, v___x_528_);
v_j_530_ = lean_usize_to_nat(v___x_529_);
v___x_531_ = lean_array_get_size(v_es_527_);
v___x_532_ = lean_nat_dec_lt(v_j_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec(v_j_530_);
lean_dec(v_x_526_);
lean_dec(v_x_525_);
return v_x_522_;
}
else
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_571_; 
lean_inc_ref(v_es_527_);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_x_522_, 0);
lean_dec(v_unused_572_);
v___x_534_ = v_x_522_;
v_isShared_535_ = v_isSharedCheck_571_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_x_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_571_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_v_536_; lean_object* v___x_537_; lean_object* v_xs_x27_538_; lean_object* v___y_540_; 
v_v_536_ = lean_array_fget(v_es_527_, v_j_530_);
v___x_537_ = lean_box(0);
v_xs_x27_538_ = lean_array_fset(v_es_527_, v_j_530_, v___x_537_);
switch(lean_obj_tag(v_v_536_))
{
case 0:
{
lean_object* v_key_545_; lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_556_; 
v_key_545_ = lean_ctor_get(v_v_536_, 0);
v_val_546_ = lean_ctor_get(v_v_536_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_v_536_);
if (v_isSharedCheck_556_ == 0)
{
v___x_548_ = v_v_536_;
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_inc(v_key_545_);
lean_dec(v_v_536_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v___x_550_; 
v___x_550_ = lean_name_eq(v_x_525_, v_key_545_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_del_object(v___x_548_);
v___x_551_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_545_, v_val_546_, v_x_525_, v_x_526_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v___y_540_ = v___x_552_;
goto v___jp_539_;
}
else
{
lean_object* v___x_554_; 
lean_dec(v_val_546_);
lean_dec(v_key_545_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_x_526_);
lean_ctor_set(v___x_548_, 0, v_x_525_);
v___x_554_ = v___x_548_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_x_525_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_x_526_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v___y_540_ = v___x_554_;
goto v___jp_539_;
}
}
}
}
case 1:
{
lean_object* v_node_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_569_; 
v_node_557_ = lean_ctor_get(v_v_536_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_v_536_);
if (v_isSharedCheck_569_ == 0)
{
v___x_559_ = v_v_536_;
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_node_557_);
lean_dec(v_v_536_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_shift_right(v_x_523_, v___x_561_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_x_524_, v___x_563_);
v___x_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_557_, v___x_562_, v___x_564_, v_x_525_, v_x_526_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_565_);
v___x_567_ = v___x_559_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_540_ = v___x_567_;
goto v___jp_539_;
}
}
}
default: 
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_x_525_);
lean_ctor_set(v___x_570_, 1, v_x_526_);
v___y_540_ = v___x_570_;
goto v___jp_539_;
}
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_fset(v_xs_x27_538_, v_j_530_, v___y_540_);
lean_dec(v_j_530_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_541_);
v___x_543_ = v___x_534_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
else
{
lean_object* v_ks_573_; lean_object* v_vs_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_594_; 
v_ks_573_ = lean_ctor_get(v_x_522_, 0);
v_vs_574_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_594_ == 0)
{
v___x_576_ = v_x_522_;
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_vs_574_);
lean_inc(v_ks_573_);
lean_dec(v_x_522_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_ks_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_vs_574_);
v___x_579_ = v_reuseFailAlloc_593_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v_newNode_580_; uint8_t v___y_582_; size_t v___x_588_; uint8_t v___x_589_; 
v_newNode_580_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_579_, v_x_525_, v_x_526_);
v___x_588_ = ((size_t)7ULL);
v___x_589_ = lean_usize_dec_le(v___x_588_, v_x_524_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_580_);
v___x_591_ = lean_unsigned_to_nat(4u);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
v___y_582_ = v___x_592_;
goto v___jp_581_;
}
else
{
v___y_582_ = v___x_589_;
goto v___jp_581_;
}
v___jp_581_:
{
if (v___y_582_ == 0)
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_ks_583_ = lean_ctor_get(v_newNode_580_, 0);
lean_inc_ref(v_ks_583_);
v_vs_584_ = lean_ctor_get(v_newNode_580_, 1);
lean_inc_ref(v_vs_584_);
lean_dec_ref(v_newNode_580_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_524_, v_ks_583_, v_vs_584_, v___x_585_, v___x_586_);
lean_dec_ref(v_vs_584_);
lean_dec_ref(v_ks_583_);
return v___x_587_;
}
else
{
return v_newNode_580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_595_, lean_object* v_keys_596_, lean_object* v_vals_597_, lean_object* v_i_598_, lean_object* v_entries_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_keys_596_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v_entries_599_;
}
else
{
lean_object* v_k_602_; lean_object* v_v_603_; uint64_t v___y_605_; 
v_k_602_ = lean_array_fget_borrowed(v_keys_596_, v_i_598_);
v_v_603_ = lean_array_fget_borrowed(v_vals_597_, v_i_598_);
if (lean_obj_tag(v_k_602_) == 0)
{
uint64_t v___x_616_; 
v___x_616_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_605_ = v___x_616_;
goto v___jp_604_;
}
else
{
uint64_t v_hash_617_; 
v_hash_617_ = lean_ctor_get_uint64(v_k_602_, sizeof(void*)*2);
v___y_605_ = v_hash_617_;
goto v___jp_604_;
}
v___jp_604_:
{
size_t v_h_606_; size_t v___x_607_; lean_object* v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v_h_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_h_606_ = lean_uint64_to_usize(v___y_605_);
v___x_607_ = ((size_t)5ULL);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v_depth_595_, v___x_609_);
v___x_611_ = lean_usize_mul(v___x_607_, v___x_610_);
v_h_612_ = lean_usize_shift_right(v_h_606_, v___x_611_);
v___x_613_ = lean_nat_add(v_i_598_, v___x_608_);
lean_dec(v_i_598_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_599_, v_h_612_, v_depth_595_, v_k_602_, v_v_603_);
v_i_598_ = v___x_613_;
v_entries_599_ = v___x_614_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_618_, lean_object* v_keys_619_, lean_object* v_vals_620_, lean_object* v_i_621_, lean_object* v_entries_622_){
_start:
{
size_t v_depth_boxed_623_; lean_object* v_res_624_; 
v_depth_boxed_623_ = lean_unbox_usize(v_depth_618_);
lean_dec(v_depth_618_);
v_res_624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_623_, v_keys_619_, v_vals_620_, v_i_621_, v_entries_622_);
lean_dec_ref(v_vals_620_);
lean_dec_ref(v_keys_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
size_t v_x_1828__boxed_630_; size_t v_x_1829__boxed_631_; lean_object* v_res_632_; 
v_x_1828__boxed_630_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_x_1829__boxed_631_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_res_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_625_, v_x_1828__boxed_630_, v_x_1829__boxed_631_, v_x_628_, v_x_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
uint64_t v___y_637_; 
if (lean_obj_tag(v_x_634_) == 0)
{
uint64_t v___x_641_; 
v___x_641_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_637_ = v___x_641_;
goto v___jp_636_;
}
else
{
uint64_t v_hash_642_; 
v_hash_642_ = lean_ctor_get_uint64(v_x_634_, sizeof(void*)*2);
v___y_637_ = v_hash_642_;
goto v___jp_636_;
}
v___jp_636_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_uint64_to_usize(v___y_637_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_633_, v___x_638_, v___x_639_, v_x_634_, v_x_635_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_643_, lean_object* v_x_644_, lean_object* v_e_645_){
_start:
{
lean_object* v_snd_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v_snd_646_ = lean_ctor_get(v_x_644_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_644_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_x_644_, 0);
lean_dec(v_unused_656_);
v___x_648_ = v_x_644_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snd_646_);
lean_dec(v_x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_structName_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v_structName_650_ = lean_ctor_get(v_e_645_, 0);
lean_inc(v_structName_650_);
v___x_651_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_646_, v_structName_650_, v_e_645_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_651_);
lean_ctor_set(v___x_648_, 0, v___x_643_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_663_, lean_object* v_x_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_663_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_668_, v_x_669_, v___y_670_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v_x_669_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
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
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_705_; lean_object* v___f_706_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_706_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_706_, 0, v___x_705_);
return v___f_706_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_707_; lean_object* v___f_708_; 
v___x_707_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_708_, 0, v___x_707_);
return v___f_708_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_box(2);
v___f_711_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_712_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_713_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_714_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_715_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_716_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_717_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___f_715_);
lean_ctor_set(v___x_717_, 2, v___f_714_);
lean_ctor_set(v___x_717_, 3, v___f_713_);
lean_ctor_set(v___x_717_, 4, v___f_712_);
lean_ctor_set(v___x_717_, 5, v___f_711_);
lean_ctor_set(v___x_717_, 6, v___x_710_);
lean_ctor_set(v___x_717_, 7, v___x_709_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___f_718_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_719_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___f_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_723_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_726_, lean_object* v_m_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_729_, lean_object* v_m_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_729_, v_m_730_);
lean_dec_ref(v_m_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_732_, lean_object* v_as_733_, lean_object* v_lo_734_, lean_object* v_hi_735_, lean_object* v_w_736_, lean_object* v_hlo_737_, lean_object* v_hhi_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_732_, v_as_733_, v_lo_734_, v_hi_735_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_740_, lean_object* v_as_741_, lean_object* v_lo_742_, lean_object* v_hi_743_, lean_object* v_w_744_, lean_object* v_hlo_745_, lean_object* v_hhi_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_740_, v_as_741_, v_lo_742_, v_hi_743_, v_w_744_, v_hlo_745_, v_hhi_746_);
lean_dec(v_hi_743_);
lean_dec(v_n_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_749_, v_x_750_, v_x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_753_, lean_object* v_00_u03b2_754_, lean_object* v_map_755_, lean_object* v_f_756_, lean_object* v_init_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_755_, v_f_756_, v_init_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_759_, lean_object* v_00_u03b2_760_, lean_object* v_map_761_, lean_object* v_f_762_, lean_object* v_init_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_759_, v_00_u03b2_760_, v_map_761_, v_f_762_, v_init_763_);
lean_dec_ref(v_map_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_765_, lean_object* v_lo_766_, lean_object* v_hi_767_, lean_object* v_hhi_768_, lean_object* v_pivot_769_, lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_k_772_, lean_object* v_ilo_773_, lean_object* v_ik_774_, lean_object* v_w_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_767_, v_pivot_769_, v_as_770_, v_i_771_, v_k_772_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_777_, lean_object* v_lo_778_, lean_object* v_hi_779_, lean_object* v_hhi_780_, lean_object* v_pivot_781_, lean_object* v_as_782_, lean_object* v_i_783_, lean_object* v_k_784_, lean_object* v_ilo_785_, lean_object* v_ik_786_, lean_object* v_w_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_777_, v_lo_778_, v_hi_779_, v_hhi_780_, v_pivot_781_, v_as_782_, v_i_783_, v_k_784_, v_ilo_785_, v_ik_786_, v_w_787_);
lean_dec_ref(v_pivot_781_);
lean_dec(v_hi_779_);
lean_dec(v_lo_778_);
lean_dec(v_n_777_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, size_t v_x_791_, size_t v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_790_, v_x_791_, v_x_792_, v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
size_t v_x_2225__boxed_802_; size_t v_x_2226__boxed_803_; lean_object* v_res_804_; 
v_x_2225__boxed_802_ = lean_unbox_usize(v_x_798_);
lean_dec(v_x_798_);
v_x_2226__boxed_803_ = lean_unbox_usize(v_x_799_);
lean_dec(v_x_799_);
v_res_804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_796_, v_x_797_, v_x_2225__boxed_802_, v_x_2226__boxed_803_, v_x_800_, v_x_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_805_, lean_object* v_f_806_, lean_object* v_init_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_806_, v_map_805_, v_init_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_809_, lean_object* v_f_810_, lean_object* v_init_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_809_, v_f_810_, v_init_811_);
lean_dec_ref(v_map_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_813_, lean_object* v_00_u03b2_814_, lean_object* v_map_815_, lean_object* v_f_816_, lean_object* v_init_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_816_, v_map_815_, v_init_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_819_, lean_object* v_00_u03b2_820_, lean_object* v_map_821_, lean_object* v_f_822_, lean_object* v_init_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_819_, v_00_u03b2_820_, v_map_821_, v_f_822_, v_init_823_);
lean_dec_ref(v_map_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_825_, lean_object* v_n_826_, lean_object* v_k_827_, lean_object* v_v_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_826_, v_k_827_, v_v_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_830_, size_t v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_heq_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_831_, v_keys_832_, v_vals_833_, v_i_835_, v_entries_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_838_, lean_object* v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
size_t v_depth_boxed_845_; lean_object* v_res_846_; 
v_depth_boxed_845_ = lean_unbox_usize(v_depth_839_);
lean_dec(v_depth_839_);
v_res_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_838_, v_depth_boxed_845_, v_keys_840_, v_vals_841_, v_heq_842_, v_i_843_, v_entries_844_);
lean_dec_ref(v_vals_841_);
lean_dec_ref(v_keys_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_847_, lean_object* v_00_u03b1_848_, lean_object* v_00_u03b2_849_, lean_object* v_f_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_850_, v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_854_, lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_f_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_854_, v_00_u03b1_855_, v_00_u03b2_856_, v_f_857_, v_x_858_, v_x_859_);
lean_dec_ref(v_x_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_862_, v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_00_u03c3_869_, lean_object* v_f_870_, lean_object* v_as_871_, size_t v_i_872_, size_t v_stop_873_, lean_object* v_b_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_870_, v_as_871_, v_i_872_, v_stop_873_, v_b_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_00_u03c3_878_, lean_object* v_f_879_, lean_object* v_as_880_, lean_object* v_i_881_, lean_object* v_stop_882_, lean_object* v_b_883_){
_start:
{
size_t v_i_boxed_884_; size_t v_stop_boxed_885_; lean_object* v_res_886_; 
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_stop_boxed_885_ = lean_unbox_usize(v_stop_882_);
lean_dec(v_stop_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_876_, v_00_u03b2_877_, v_00_u03c3_878_, v_f_879_, v_as_880_, v_i_boxed_884_, v_stop_boxed_885_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_887_, lean_object* v_00_u03b1_888_, lean_object* v_00_u03b2_889_, lean_object* v_f_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_heq_893_, lean_object* v_i_894_, lean_object* v_acc_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_890_, v_keys_891_, v_vals_892_, v_i_894_, v_acc_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_897_, lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_f_900_, lean_object* v_keys_901_, lean_object* v_vals_902_, lean_object* v_heq_903_, lean_object* v_i_904_, lean_object* v_acc_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_897_, v_00_u03b1_898_, v_00_u03b2_899_, v_f_900_, v_keys_901_, v_vals_902_, v_heq_903_, v_i_904_, v_acc_905_);
lean_dec_ref(v_vals_902_);
lean_dec_ref(v_keys_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_914_, size_t v_i_915_, lean_object* v_bs_916_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_lt(v_i_915_, v_sz_914_);
if (v___x_917_ == 0)
{
return v_bs_916_;
}
else
{
lean_object* v_v_918_; lean_object* v_fieldName_919_; lean_object* v___x_920_; lean_object* v_bs_x27_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; 
v_v_918_ = lean_array_uget_borrowed(v_bs_916_, v_i_915_);
v_fieldName_919_ = lean_ctor_get(v_v_918_, 0);
lean_inc(v_fieldName_919_);
v___x_920_ = lean_unsigned_to_nat(0u);
v_bs_x27_921_ = lean_array_uset(v_bs_916_, v_i_915_, v___x_920_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_915_, v___x_922_);
v___x_924_ = lean_array_uset(v_bs_x27_921_, v_i_915_, v_fieldName_919_);
v_i_915_ = v___x_923_;
v_bs_916_ = v___x_924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_926_, lean_object* v_i_927_, lean_object* v_bs_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_930_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_929_, v_i_boxed_930_, v_bs_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object* v_hi_932_, lean_object* v_pivot_933_, lean_object* v_as_934_, lean_object* v_i_935_, lean_object* v_k_936_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_lt(v_k_936_, v_hi_932_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_k_936_);
v___x_938_ = lean_array_fswap(v_as_934_, v_i_935_, v_hi_932_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_i_935_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_array_fget_borrowed(v_as_934_, v_k_936_);
v___x_941_ = l_Lean_StructureFieldInfo_lt(v___x_940_, v_pivot_933_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_k_936_, v___x_942_);
lean_dec(v_k_936_);
v_k_936_ = v___x_943_;
goto _start;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_945_ = lean_array_fswap(v_as_934_, v_i_935_, v_k_936_);
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_i_935_, v___x_946_);
lean_dec(v_i_935_);
v___x_948_ = lean_nat_add(v_k_936_, v___x_946_);
lean_dec(v_k_936_);
v_as_934_ = v___x_945_;
v_i_935_ = v___x_947_;
v_k_936_ = v___x_948_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object* v_hi_950_, lean_object* v_pivot_951_, lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_950_, v_pivot_951_, v_as_952_, v_i_953_, v_k_954_);
lean_dec_ref(v_pivot_951_);
lean_dec(v_hi_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_n_956_, lean_object* v_as_957_, lean_object* v_lo_958_, lean_object* v_hi_959_){
_start:
{
lean_object* v___y_961_; uint8_t v___x_971_; 
v___x_971_ = lean_nat_dec_lt(v_lo_958_, v_hi_959_);
if (v___x_971_ == 0)
{
lean_dec(v_lo_958_);
return v_as_957_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_mid_974_; lean_object* v___y_976_; lean_object* v___y_982_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_972_ = lean_nat_add(v_lo_958_, v_hi_959_);
v___x_973_ = lean_unsigned_to_nat(1u);
v_mid_974_ = lean_nat_shiftr(v___x_972_, v___x_973_);
lean_dec(v___x_972_);
v___x_987_ = lean_array_fget_borrowed(v_as_957_, v_mid_974_);
v___x_988_ = lean_array_fget_borrowed(v_as_957_, v_lo_958_);
v___x_989_ = l_Lean_StructureFieldInfo_lt(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
v___y_982_ = v_as_957_;
goto v___jp_981_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_array_fswap(v_as_957_, v_lo_958_, v_mid_974_);
v___y_982_ = v___x_990_;
goto v___jp_981_;
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_array_fget_borrowed(v___y_976_, v_mid_974_);
v___x_978_ = lean_array_fget_borrowed(v___y_976_, v_hi_959_);
v___x_979_ = l_Lean_StructureFieldInfo_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_dec(v_mid_974_);
v___y_961_ = v___y_976_;
goto v___jp_960_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_array_fswap(v___y_976_, v_mid_974_, v_hi_959_);
lean_dec(v_mid_974_);
v___y_961_ = v___x_980_;
goto v___jp_960_;
}
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_array_fget_borrowed(v___y_982_, v_hi_959_);
v___x_984_ = lean_array_fget_borrowed(v___y_982_, v_lo_958_);
v___x_985_ = l_Lean_StructureFieldInfo_lt(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
v___y_976_ = v___y_982_;
goto v___jp_975_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_array_fswap(v___y_982_, v_lo_958_, v_hi_959_);
v___y_976_ = v___x_986_;
goto v___jp_975_;
}
}
}
v___jp_960_:
{
lean_object* v_pivot_962_; lean_object* v___x_963_; lean_object* v_fst_964_; lean_object* v_snd_965_; uint8_t v___x_966_; 
v_pivot_962_ = lean_array_fget(v___y_961_, v_hi_959_);
lean_inc_n(v_lo_958_, 2);
v___x_963_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_959_, v_pivot_962_, v___y_961_, v_lo_958_, v_lo_958_);
lean_dec(v_pivot_962_);
v_fst_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_fst_964_);
v_snd_965_ = lean_ctor_get(v___x_963_, 1);
lean_inc(v_snd_965_);
lean_dec_ref(v___x_963_);
v___x_966_ = lean_nat_dec_le(v_hi_959_, v_fst_964_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_956_, v_snd_965_, v_lo_958_, v_fst_964_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_fst_964_, v___x_968_);
lean_dec(v_fst_964_);
v_as_957_ = v___x_967_;
v_lo_958_ = v___x_969_;
goto _start;
}
else
{
lean_dec(v_fst_964_);
lean_dec(v_lo_958_);
return v_snd_965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_n_991_, lean_object* v_as_992_, lean_object* v_lo_993_, lean_object* v_hi_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_991_, v_as_992_, v_lo_993_, v_hi_994_);
lean_dec(v_hi_994_);
lean_dec(v_n_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_998_, lean_object* v_e_999_){
_start:
{
lean_object* v_structName_1000_; lean_object* v_fields_1001_; lean_object* v___x_1002_; size_t v_sz_1003_; size_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___y_1007_; lean_object* v___x_1014_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_structName_1000_ = lean_ctor_get(v_e_999_, 0);
lean_inc(v_structName_1000_);
v_fields_1001_ = lean_ctor_get(v_e_999_, 1);
lean_inc_ref_n(v_fields_1001_, 2);
lean_dec_ref(v_e_999_);
v___x_1002_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_1003_ = lean_array_size(v_fields_1001_);
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_1003_, v___x_1004_, v_fields_1001_);
v___x_1014_ = lean_array_get_size(v_fields_1001_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_nat_dec_eq(v___x_1014_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___y_1024_; uint8_t v___x_1026_; 
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_sub(v___x_1014_, v___x_1021_);
v___x_1026_ = lean_nat_dec_le(v___x_1019_, v___x_1022_);
if (v___x_1026_ == 0)
{
lean_inc(v___x_1022_);
v___y_1024_ = v___x_1022_;
goto v___jp_1023_;
}
else
{
v___y_1024_ = v___x_1019_;
goto v___jp_1023_;
}
v___jp_1023_:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_le(v___y_1024_, v___x_1022_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_1022_);
lean_inc(v___y_1024_);
v___y_1016_ = v___y_1024_;
v___y_1017_ = v___y_1024_;
goto v___jp_1015_;
}
else
{
v___y_1016_ = v___y_1024_;
v___y_1017_ = v___x_1022_;
goto v___jp_1015_;
}
}
}
else
{
v___y_1007_ = v_fields_1001_;
goto v___jp_1006_;
}
v___jp_1006_:
{
lean_object* v_toEnvExtension_1008_; lean_object* v_asyncMode_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_toEnvExtension_1008_ = lean_ctor_get(v___x_1002_, 0);
v_asyncMode_1009_ = lean_ctor_get(v_toEnvExtension_1008_, 2);
v___x_1010_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_1011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1011_, 0, v_structName_1000_);
lean_ctor_set(v___x_1011_, 1, v___x_1005_);
lean_ctor_set(v___x_1011_, 2, v___y_1007_);
lean_ctor_set(v___x_1011_, 3, v___x_1010_);
v___x_1012_ = lean_box(0);
v___x_1013_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1002_, v_env_998_, v___x_1011_, v_asyncMode_1009_, v___x_1012_);
return v___x_1013_;
}
v___jp_1015_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_1014_, v_fields_1001_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
v___y_1007_ = v___x_1018_;
goto v___jp_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_1027_, lean_object* v_as_1028_, lean_object* v_lo_1029_, lean_object* v_hi_1030_, lean_object* v_w_1031_, lean_object* v_hlo_1032_, lean_object* v_hhi_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_1027_, v_as_1028_, v_lo_1029_, v_hi_1030_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_1035_, lean_object* v_as_1036_, lean_object* v_lo_1037_, lean_object* v_hi_1038_, lean_object* v_w_1039_, lean_object* v_hlo_1040_, lean_object* v_hhi_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_1035_, v_as_1036_, v_lo_1037_, v_hi_1038_, v_w_1039_, v_hlo_1040_, v_hhi_1041_);
lean_dec(v_hi_1038_);
lean_dec(v_n_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object* v_n_1043_, lean_object* v_lo_1044_, lean_object* v_hi_1045_, lean_object* v_hhi_1046_, lean_object* v_pivot_1047_, lean_object* v_as_1048_, lean_object* v_i_1049_, lean_object* v_k_1050_, lean_object* v_ilo_1051_, lean_object* v_ik_1052_, lean_object* v_w_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_1045_, v_pivot_1047_, v_as_1048_, v_i_1049_, v_k_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object* v_n_1055_, lean_object* v_lo_1056_, lean_object* v_hi_1057_, lean_object* v_hhi_1058_, lean_object* v_pivot_1059_, lean_object* v_as_1060_, lean_object* v_i_1061_, lean_object* v_k_1062_, lean_object* v_ilo_1063_, lean_object* v_ik_1064_, lean_object* v_w_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_1055_, v_lo_1056_, v_hi_1057_, v_hhi_1058_, v_pivot_1059_, v_as_1060_, v_i_1061_, v_k_1062_, v_ilo_1063_, v_ik_1064_, v_w_1065_);
lean_dec_ref(v_pivot_1059_);
lean_dec(v_hi_1057_);
lean_dec(v_lo_1056_);
lean_dec(v_n_1055_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_1067_, lean_object* v_parentInfo_1068_, lean_object* v___x_1069_, lean_object* v_asyncMode_1070_, lean_object* v___x_1071_, lean_object* v_env_1072_){
_start:
{
lean_object* v_structName_1073_; lean_object* v_fieldNames_1074_; lean_object* v_fieldInfo_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_structName_1073_ = lean_ctor_get(v_val_1067_, 0);
v_fieldNames_1074_ = lean_ctor_get(v_val_1067_, 1);
v_fieldInfo_1075_ = lean_ctor_get(v_val_1067_, 2);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_val_1067_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_val_1067_, 3);
lean_dec(v_unused_1084_);
v___x_1077_ = v_val_1067_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_fieldInfo_1075_);
lean_inc(v_fieldNames_1074_);
lean_inc(v_structName_1073_);
lean_dec(v_val_1067_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 3, v_parentInfo_1068_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_structName_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_fieldNames_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_fieldInfo_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_parentInfo_1068_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1069_, v_env_1072_, v___x_1080_, v_asyncMode_1070_, v___x_1071_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_1085_, lean_object* v_parentInfo_1086_, lean_object* v___x_1087_, lean_object* v_asyncMode_1088_, lean_object* v___x_1089_, lean_object* v_env_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_setStructureParents___redArg___lam__0(v_val_1085_, v_parentInfo_1086_, v___x_1087_, v_asyncMode_1088_, v___x_1089_, v_env_1090_);
lean_dec(v_asyncMode_1088_);
return v_res_1091_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v_structName_1101_, lean_object* v_parentInfo_1102_, lean_object* v_modifyEnv_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_____do__lift_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v_toEnvExtension_1108_; lean_object* v_asyncMode_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1128_; 
v___x_1107_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1108_ = lean_ctor_get(v___x_1107_, 0);
v_asyncMode_1109_ = lean_ctor_get(v_toEnvExtension_1108_, 2);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1098_, v___x_1107_, v_____do__lift_1106_, v_asyncMode_1109_, v___x_1110_);
v_snd_1112_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1129_);
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; 
lean_inc(v_structName_1101_);
v___x_1116_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1099_, v___x_1100_, v_snd_1112_, v_structName_1101_);
lean_dec(v_snd_1112_);
if (lean_obj_tag(v___x_1116_) == 1)
{
lean_object* v_val_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; 
lean_del_object(v___x_1114_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_inst_1104_);
lean_dec(v_structName_1101_);
v_val_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v___x_1116_, 1);
lean_inc(v_asyncMode_1109_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1118_, 0, v_val_1117_);
lean_closure_set(v___f_1118_, 1, v_parentInfo_1102_);
lean_closure_set(v___f_1118_, 2, v___x_1107_);
lean_closure_set(v___f_1118_, 3, v_asyncMode_1109_);
lean_closure_set(v___f_1118_, 4, v___x_1110_);
v___x_1119_ = lean_apply_1(v_modifyEnv_1103_, v___f_1118_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_dec(v___x_1116_);
lean_dec(v_modifyEnv_1103_);
lean_dec_ref(v_parentInfo_1102_);
v___x_1120_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_1121_ = l_Lean_MessageData_ofName(v_structName_1101_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 7);
lean_ctor_set(v___x_1114_, 1, v___x_1121_);
lean_ctor_set(v___x_1114_, 0, v___x_1120_);
v___x_1123_ = v___x_1114_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_throwError___redArg(v_inst_1104_, v_inst_1105_, v___x_1125_);
return v___x_1126_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = l_Lean_instInhabitedStructureState_default;
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_structName_1138_, lean_object* v_parentInfo_1139_){
_start:
{
lean_object* v_toBind_1140_; lean_object* v_getEnv_1141_; lean_object* v_modifyEnv_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_toBind_1140_ = lean_ctor_get(v_inst_1135_, 1);
lean_inc(v_toBind_1140_);
v_getEnv_1141_ = lean_ctor_get(v_inst_1136_, 0);
lean_inc(v_getEnv_1141_);
v_modifyEnv_1142_ = lean_ctor_get(v_inst_1136_, 1);
lean_inc(v_modifyEnv_1142_);
lean_dec_ref(v_inst_1136_);
v___x_1143_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1144_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1145_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1146_, 0, v___x_1145_);
lean_closure_set(v___f_1146_, 1, v___x_1143_);
lean_closure_set(v___f_1146_, 2, v___x_1144_);
lean_closure_set(v___f_1146_, 3, v_structName_1138_);
lean_closure_set(v___f_1146_, 4, v_parentInfo_1139_);
lean_closure_set(v___f_1146_, 5, v_modifyEnv_1142_);
lean_closure_set(v___f_1146_, 6, v_inst_1135_);
lean_closure_set(v___f_1146_, 7, v_inst_1137_);
v___x_1147_ = lean_apply_4(v_toBind_1140_, lean_box(0), lean_box(0), v_getEnv_1141_, v___f_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_structName_1152_, lean_object* v_parentInfo_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_setStructureParents___redArg(v_inst_1149_, v_inst_1150_, v_inst_1151_, v_structName_1152_, v_parentInfo_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1155_, lean_object* v_k_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_m_1161_; lean_object* v_a_1162_; uint8_t v___x_1163_; 
v___x_1159_ = lean_nat_add(v_x_1157_, v_x_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v_m_1161_ = lean_nat_shiftr(v___x_1159_, v___x_1160_);
lean_dec(v___x_1159_);
v_a_1162_ = lean_array_fget_borrowed(v_as_1155_, v_m_1161_);
v___x_1163_ = l_Lean_StructureInfo_lt(v_a_1162_, v_k_1156_);
if (v___x_1163_ == 0)
{
uint8_t v___x_1164_; 
lean_dec(v_x_1158_);
v___x_1164_ = l_Lean_StructureInfo_lt(v_k_1156_, v_a_1162_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_dec(v_m_1161_);
lean_dec(v_x_1157_);
lean_inc(v_a_1162_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_a_1162_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_nat_dec_eq(v_m_1161_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = lean_nat_sub(v_m_1161_, v___x_1160_);
lean_dec(v_m_1161_);
v___x_1169_ = lean_nat_dec_lt(v___x_1168_, v_x_1157_);
if (v___x_1169_ == 0)
{
v_x_1158_ = v___x_1168_;
goto _start;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v___x_1168_);
lean_dec(v_x_1157_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; 
lean_dec(v_m_1161_);
lean_dec(v_x_1157_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
}
}
else
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
lean_dec(v_x_1157_);
v___x_1173_ = lean_nat_add(v_m_1161_, v___x_1160_);
lean_dec(v_m_1161_);
v___x_1174_ = lean_nat_dec_le(v___x_1173_, v_x_1158_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec(v___x_1173_);
lean_dec(v_x_1158_);
v___x_1175_ = lean_box(0);
return v___x_1175_;
}
else
{
v_x_1157_ = v___x_1173_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1177_, lean_object* v_k_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1177_, v_k_1178_, v_x_1179_, v_x_1180_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_as_1177_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1182_, lean_object* v_vals_1183_, lean_object* v_i_1184_, lean_object* v_k_1185_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_array_get_size(v_keys_1182_);
v___x_1187_ = lean_nat_dec_lt(v_i_1184_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_dec(v_i_1184_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v_k_x27_1189_; uint8_t v___x_1190_; 
v_k_x27_1189_ = lean_array_fget_borrowed(v_keys_1182_, v_i_1184_);
v___x_1190_ = lean_name_eq(v_k_1185_, v_k_x27_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_i_1184_, v___x_1191_);
lean_dec(v_i_1184_);
v_i_1184_ = v___x_1192_;
goto _start;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_array_fget_borrowed(v_vals_1183_, v_i_1184_);
lean_dec(v_i_1184_);
lean_inc(v___x_1194_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1196_, lean_object* v_vals_1197_, lean_object* v_i_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1196_, v_vals_1197_, v_i_1198_, v_k_1199_);
lean_dec(v_k_1199_);
lean_dec_ref(v_vals_1197_);
lean_dec_ref(v_keys_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1201_, size_t v_x_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 0)
{
lean_object* v_es_1204_; lean_object* v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v_j_1208_; lean_object* v___x_1209_; 
v_es_1204_ = lean_ctor_get(v_x_1201_, 0);
v___x_1205_ = lean_box(2);
v___x_1206_ = ((size_t)31ULL);
v___x_1207_ = lean_usize_land(v_x_1202_, v___x_1206_);
v_j_1208_ = lean_usize_to_nat(v___x_1207_);
v___x_1209_ = lean_array_get_borrowed(v___x_1205_, v_es_1204_, v_j_1208_);
lean_dec(v_j_1208_);
switch(lean_obj_tag(v___x_1209_))
{
case 0:
{
lean_object* v_key_1210_; lean_object* v_val_1211_; uint8_t v___x_1212_; 
v_key_1210_ = lean_ctor_get(v___x_1209_, 0);
v_val_1211_ = lean_ctor_get(v___x_1209_, 1);
v___x_1212_ = lean_name_eq(v_x_1203_, v_key_1210_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
lean_inc(v_val_1211_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_val_1211_);
return v___x_1214_;
}
}
case 1:
{
lean_object* v_node_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v_node_1215_ = lean_ctor_get(v___x_1209_, 0);
v___x_1216_ = ((size_t)5ULL);
v___x_1217_ = lean_usize_shift_right(v_x_1202_, v___x_1216_);
v_x_1201_ = v_node_1215_;
v_x_1202_ = v___x_1217_;
goto _start;
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_box(0);
return v___x_1219_;
}
}
}
else
{
lean_object* v_ks_1220_; lean_object* v_vs_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_ks_1220_ = lean_ctor_get(v_x_1201_, 0);
v_vs_1221_ = lean_ctor_get(v_x_1201_, 1);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1220_, v_vs_1221_, v___x_1222_, v_x_1203_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
size_t v_x_385__boxed_1227_; lean_object* v_res_1228_; 
v_x_385__boxed_1227_ = lean_unbox_usize(v_x_1225_);
lean_dec(v_x_1225_);
v_res_1228_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1224_, v_x_385__boxed_1227_, v_x_1226_);
lean_dec(v_x_1226_);
lean_dec_ref(v_x_1224_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1229_, lean_object* v_x_1230_){
_start:
{
uint64_t v___y_1232_; 
if (lean_obj_tag(v_x_1230_) == 0)
{
uint64_t v___x_1235_; 
v___x_1235_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_1232_ = v___x_1235_;
goto v___jp_1231_;
}
else
{
uint64_t v_hash_1236_; 
v_hash_1236_ = lean_ctor_get_uint64(v_x_1230_, sizeof(void*)*2);
v___y_1232_ = v_hash_1236_;
goto v___jp_1231_;
}
v___jp_1231_:
{
size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_uint64_to_usize(v___y_1232_);
v___x_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1229_, v___x_1233_, v_x_1230_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1237_, v_x_1238_);
lean_dec(v_x_1238_);
lean_dec_ref(v_x_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1240_, lean_object* v_structName_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1243_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1240_, v_structName_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; lean_object* v_toEnvExtension_1245_; lean_object* v_asyncMode_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_snd_1249_; lean_object* v___x_1250_; 
v___x_1244_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1245_ = lean_ctor_get(v___x_1244_, 0);
v_asyncMode_1246_ = lean_ctor_get(v_toEnvExtension_1245_, 2);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1242_, v___x_1244_, v_env_1240_, v_asyncMode_1246_, v___x_1247_);
v_snd_1249_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_snd_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1249_, v_structName_1241_);
lean_dec(v_structName_1241_);
lean_dec(v_snd_1249_);
return v___x_1250_;
}
else
{
lean_object* v_val_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_val_1251_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1252_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1253_ = 0;
v___x_1254_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1242_, v___x_1252_, v_env_1240_, v_val_1251_, v___x_1253_);
lean_dec(v_val_1251_);
lean_dec_ref(v_env_1240_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_array_get_size(v___x_1254_);
v___x_1257_ = lean_nat_dec_lt(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v___x_1254_);
lean_dec(v_structName_1241_);
v___x_1258_ = lean_box(0);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v___x_1256_, v___x_1259_);
v___x_1261_ = lean_nat_dec_le(v___x_1255_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v___x_1260_);
lean_dec_ref(v___x_1254_);
lean_dec(v_structName_1241_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1264_, 0, v_structName_1241_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
lean_ctor_set(v___x_1264_, 3, v___x_1263_);
v___x_1265_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1254_, v___x_1264_, v___x_1255_, v___x_1260_);
lean_dec_ref_known(v___x_1264_, 4);
lean_dec_ref(v___x_1254_);
return v___x_1265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1267_, v_x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1270_, v_x_1271_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec_ref(v_x_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1274_, lean_object* v_k_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1274_, v_k_1275_, v_x_1276_, v_x_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1280_, lean_object* v_k_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1280_, v_k_1281_, v_x_1282_, v_x_1283_, v_x_1284_);
lean_dec_ref(v_k_1281_);
lean_dec_ref(v_as_1280_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, size_t v_x_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1287_, v_x_1288_, v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_519__boxed_1295_; lean_object* v_res_1296_; 
v_x_519__boxed_1295_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_res_1296_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1291_, v_x_1292_, v_x_519__boxed_1295_, v_x_1294_);
lean_dec(v_x_1294_);
lean_dec_ref(v_x_1292_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1297_, lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_heq_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1298_, v_vals_1299_, v_i_1301_, v_k_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_keys_1305_, lean_object* v_vals_1306_, lean_object* v_heq_1307_, lean_object* v_i_1308_, lean_object* v_k_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1304_, v_keys_1305_, v_vals_1306_, v_heq_1307_, v_i_1308_, v_k_1309_);
lean_dec(v_k_1309_);
lean_dec_ref(v_vals_1306_);
lean_dec_ref(v_keys_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1313_ = lean_panic_fn_borrowed(v___x_1312_, v_msg_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1317_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1318_ = lean_unsigned_to_nat(4u);
v___x_1319_ = lean_unsigned_to_nat(139u);
v___x_1320_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1321_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1322_ = l_mkPanicMessageWithDecl(v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_, v___x_1317_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1323_, lean_object* v_structName_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_getStructureInfo_x3f(v_env_1323_, v_structName_1324_);
if (lean_obj_tag(v___x_1325_) == 1)
{
lean_object* v_val_1326_; 
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v___x_1325_, 1);
return v_val_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v___x_1325_);
v___x_1327_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1328_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1327_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1331_ = lean_panic_fn_borrowed(v___x_1330_, v_msg_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1333_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1334_ = lean_unsigned_to_nat(9u);
v___x_1335_ = lean_unsigned_to_nat(154u);
v___x_1336_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1337_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1338_ = l_mkPanicMessageWithDecl(v___x_1337_, v___x_1336_, v___x_1335_, v___x_1334_, v___x_1333_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1340_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1341_ = lean_unsigned_to_nat(11u);
v___x_1342_ = lean_unsigned_to_nat(153u);
v___x_1343_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1344_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1345_ = l_mkPanicMessageWithDecl(v___x_1344_, v___x_1343_, v___x_1342_, v___x_1341_, v___x_1340_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1346_, lean_object* v_constName_1347_){
_start:
{
uint8_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = 0;
lean_inc_ref(v_env_1346_);
v___x_1355_ = l_Lean_Environment_find_x3f(v_env_1346_, v_constName_1347_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
if (lean_obj_tag(v_val_1356_) == 5)
{
lean_object* v_val_1357_; lean_object* v_ctors_1358_; 
v_val_1357_ = lean_ctor_get(v_val_1356_, 0);
lean_inc_ref(v_val_1357_);
lean_dec_ref_known(v_val_1356_, 1);
v_ctors_1358_ = lean_ctor_get(v_val_1357_, 4);
lean_inc(v_ctors_1358_);
lean_dec_ref(v_val_1357_);
if (lean_obj_tag(v_ctors_1358_) == 1)
{
lean_object* v_tail_1359_; 
v_tail_1359_ = lean_ctor_get(v_ctors_1358_, 1);
if (lean_obj_tag(v_tail_1359_) == 0)
{
lean_object* v_head_1360_; lean_object* v___x_1361_; 
v_head_1360_ = lean_ctor_get(v_ctors_1358_, 0);
lean_inc(v_head_1360_);
lean_dec_ref_known(v_ctors_1358_, 2);
v___x_1361_ = l_Lean_Environment_find_x3f(v_env_1346_, v_head_1360_, v___x_1354_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
if (lean_obj_tag(v_val_1362_) == 6)
{
lean_object* v_val_1363_; 
v_val_1363_ = lean_ctor_get(v_val_1362_, 0);
lean_inc_ref(v_val_1363_);
lean_dec_ref_known(v_val_1362_, 1);
return v_val_1363_;
}
else
{
lean_dec(v_val_1362_);
goto v___jp_1351_;
}
}
else
{
lean_dec(v___x_1361_);
goto v___jp_1351_;
}
}
else
{
lean_dec_ref_known(v_ctors_1358_, 2);
lean_dec_ref(v_env_1346_);
goto v___jp_1348_;
}
}
else
{
lean_dec(v_ctors_1358_);
lean_dec_ref(v_env_1346_);
goto v___jp_1348_;
}
}
else
{
lean_dec(v_val_1356_);
lean_dec_ref(v_env_1346_);
goto v___jp_1348_;
}
}
else
{
lean_dec(v___x_1355_);
lean_dec_ref(v_env_1346_);
goto v___jp_1348_;
}
v___jp_1348_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1350_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1349_);
return v___x_1350_;
}
v___jp_1351_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1353_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1352_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1364_, lean_object* v_structName_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v_fieldNames_1367_; 
v___x_1366_ = l_Lean_getStructureInfo(v_env_1364_, v_structName_1365_);
v_fieldNames_1367_ = lean_ctor_get(v___x_1366_, 1);
lean_inc_ref(v_fieldNames_1367_);
lean_dec_ref(v___x_1366_);
return v_fieldNames_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1368_, lean_object* v_structName_1369_, lean_object* v_fieldName_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_getStructureInfo_x3f(v_env_1368_, v_structName_1369_);
if (lean_obj_tag(v___x_1371_) == 1)
{
lean_object* v_val_1372_; lean_object* v_fieldInfo_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v_fieldInfo_1373_ = lean_ctor_get(v_val_1372_, 2);
lean_inc_ref(v_fieldInfo_1373_);
lean_dec(v_val_1372_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_array_get_size(v_fieldInfo_1373_);
v___x_1376_ = lean_nat_dec_lt(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v_fieldInfo_1373_);
lean_dec(v_fieldName_1370_);
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_sub(v___x_1375_, v___x_1378_);
v___x_1380_ = lean_nat_dec_le(v___x_1374_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec(v___x_1379_);
lean_dec_ref(v_fieldInfo_1373_);
lean_dec(v_fieldName_1370_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_box(0);
v___x_1384_ = 0;
v___x_1385_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1385_, 0, v_fieldName_1370_);
lean_ctor_set(v___x_1385_, 1, v___x_1382_);
lean_ctor_set(v___x_1385_, 2, v___x_1383_);
lean_ctor_set(v___x_1385_, 3, v___x_1383_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*4, v___x_1384_);
v___x_1386_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1373_, v___x_1385_, v___x_1374_, v___x_1379_);
lean_dec_ref_known(v___x_1385_, 4);
lean_dec_ref(v_fieldInfo_1373_);
return v___x_1386_;
}
}
}
else
{
lean_object* v___x_1387_; 
lean_dec(v___x_1371_);
lean_dec(v_fieldName_1370_);
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1388_, lean_object* v_structName_1389_, lean_object* v_fieldName_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_getFieldInfo_x3f(v_env_1388_, v_structName_1389_, v_fieldName_1390_);
if (lean_obj_tag(v___x_1391_) == 1)
{
lean_object* v_val_1392_; lean_object* v_subobject_x3f_1393_; 
v_val_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_subobject_x3f_1393_ = lean_ctor_get(v_val_1392_, 2);
lean_inc(v_subobject_x3f_1393_);
lean_dec(v_val_1392_);
return v_subobject_x3f_1393_;
}
else
{
lean_object* v___x_1394_; 
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1395_, lean_object* v_structName_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v_parentInfo_1398_; 
v___x_1397_ = l_Lean_getStructureInfo(v_env_1395_, v_structName_1396_);
v_parentInfo_1398_ = lean_ctor_get(v___x_1397_, 3);
lean_inc_ref(v_parentInfo_1398_);
lean_dec_ref(v___x_1397_);
return v_parentInfo_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1399_, lean_object* v_structName_1400_, lean_object* v_as_1401_, size_t v_i_1402_, size_t v_stop_1403_, lean_object* v_b_1404_){
_start:
{
lean_object* v___y_1406_; uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_eq(v_i_1402_, v_stop_1403_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_array_uget_borrowed(v_as_1401_, v_i_1402_);
lean_inc(v___x_1411_);
lean_inc(v_structName_1400_);
lean_inc_ref(v_env_1399_);
v___x_1412_ = l_Lean_isSubobjectField_x3f(v_env_1399_, v_structName_1400_, v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
v___y_1406_ = v_b_1404_;
goto v___jp_1405_;
}
else
{
lean_object* v_val_1413_; lean_object* v___x_1414_; 
v_val_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = lean_array_push(v_b_1404_, v_val_1413_);
v___y_1406_ = v___x_1414_;
goto v___jp_1405_;
}
}
else
{
lean_dec(v_structName_1400_);
lean_dec_ref(v_env_1399_);
return v_b_1404_;
}
v___jp_1405_:
{
size_t v___x_1407_; size_t v___x_1408_; 
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_add(v_i_1402_, v___x_1407_);
v_i_1402_ = v___x_1408_;
v_b_1404_ = v___y_1406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1415_, lean_object* v_structName_1416_, lean_object* v_as_1417_, lean_object* v_i_1418_, lean_object* v_stop_1419_, lean_object* v_b_1420_){
_start:
{
size_t v_i_boxed_1421_; size_t v_stop_boxed_1422_; lean_object* v_res_1423_; 
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_stop_boxed_1422_ = lean_unbox_usize(v_stop_1419_);
lean_dec(v_stop_1419_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1415_, v_structName_1416_, v_as_1417_, v_i_boxed_1421_, v_stop_boxed_1422_, v_b_1420_);
lean_dec_ref(v_as_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1424_, lean_object* v_structName_1425_, lean_object* v_as_1426_, lean_object* v_start_1427_, lean_object* v_stop_1428_){
_start:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1430_ = lean_nat_dec_lt(v_start_1427_, v_stop_1428_);
if (v___x_1430_ == 0)
{
lean_dec(v_structName_1425_);
lean_dec_ref(v_env_1424_);
return v___x_1429_;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = lean_array_get_size(v_as_1426_);
v___x_1432_ = lean_nat_dec_le(v_stop_1428_, v___x_1431_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_nat_dec_lt(v_start_1427_, v___x_1431_);
if (v___x_1433_ == 0)
{
lean_dec(v_structName_1425_);
lean_dec_ref(v_env_1424_);
return v___x_1429_;
}
else
{
size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_usize_of_nat(v_start_1427_);
v___x_1435_ = lean_usize_of_nat(v___x_1431_);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1424_, v_structName_1425_, v_as_1426_, v___x_1434_, v___x_1435_, v___x_1429_);
return v___x_1436_;
}
}
else
{
size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_usize_of_nat(v_start_1427_);
v___x_1438_ = lean_usize_of_nat(v_stop_1428_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1424_, v_structName_1425_, v_as_1426_, v___x_1437_, v___x_1438_, v___x_1429_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1440_, lean_object* v_structName_1441_, lean_object* v_as_1442_, lean_object* v_start_1443_, lean_object* v_stop_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1440_, v_structName_1441_, v_as_1442_, v_start_1443_, v_stop_1444_);
lean_dec(v_stop_1444_);
lean_dec(v_start_1443_);
lean_dec_ref(v_as_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1446_, lean_object* v_structName_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_inc(v_structName_1447_);
lean_inc_ref(v_env_1446_);
v___x_1448_ = l_Lean_getStructureFields(v_env_1446_, v_structName_1447_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v___x_1448_);
v___x_1451_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1446_, v_structName_1447_, v___x_1448_, v___x_1449_, v___x_1450_);
lean_dec_ref(v___x_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1452_, lean_object* v_as_1453_, size_t v_i_1454_, size_t v_stop_1455_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_eq(v_i_1454_, v_stop_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_array_uget_borrowed(v_as_1453_, v_i_1454_);
v___x_1458_ = lean_name_eq(v_a_1452_, v___x_1457_);
if (v___x_1458_ == 0)
{
size_t v___x_1459_; size_t v___x_1460_; 
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_add(v_i_1454_, v___x_1459_);
v_i_1454_ = v___x_1460_;
goto _start;
}
else
{
return v___x_1458_;
}
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = 0;
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1463_, lean_object* v_as_1464_, lean_object* v_i_1465_, lean_object* v_stop_1466_){
_start:
{
size_t v_i_boxed_1467_; size_t v_stop_boxed_1468_; uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_i_boxed_1467_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_stop_boxed_1468_ = lean_unbox_usize(v_stop_1466_);
lean_dec(v_stop_1466_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1463_, v_as_1464_, v_i_boxed_1467_, v_stop_boxed_1468_);
lean_dec_ref(v_as_1464_);
lean_dec(v_a_1463_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_array_get_size(v_as_1471_);
v___x_1475_ = lean_nat_dec_lt(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
return v___x_1475_;
}
else
{
if (v___x_1475_ == 0)
{
return v___x_1475_;
}
else
{
size_t v___x_1476_; size_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = ((size_t)0ULL);
v___x_1477_ = lean_usize_of_nat(v___x_1474_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1472_, v_as_1471_, v___x_1476_, v___x_1477_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1479_, lean_object* v_a_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_as_1479_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1486_, lean_object* v_structName_1487_, lean_object* v_fieldName_1488_){
_start:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
lean_inc(v_structName_1487_);
lean_inc_ref(v_env_1486_);
v___x_1489_ = l_Lean_getStructureFields(v_env_1486_, v_structName_1487_);
v___x_1490_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1489_, v_fieldName_1488_);
lean_dec_ref(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; size_t v_sz_1494_; size_t v___x_1495_; lean_object* v___x_1496_; lean_object* v_fst_1497_; 
lean_inc_ref(v_env_1486_);
v___x_1491_ = l_Lean_getStructureSubobjects(v_env_1486_, v_structName_1487_);
v___x_1492_ = lean_box(0);
v___x_1493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1494_ = lean_array_size(v___x_1491_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1486_, v_fieldName_1488_, v___x_1491_, v_sz_1494_, v___x_1495_, v___x_1493_);
lean_dec_ref(v___x_1491_);
v_fst_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_fst_1497_);
lean_dec_ref(v___x_1496_);
if (lean_obj_tag(v_fst_1497_) == 0)
{
return v___x_1492_;
}
else
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v_fst_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v_fst_1497_, 1);
return v_val_1498_;
}
}
else
{
lean_object* v___x_1499_; 
lean_dec_ref(v_env_1486_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_structName_1487_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1500_, lean_object* v_fieldName_1501_, lean_object* v_as_1502_, size_t v_sz_1503_, size_t v_i_1504_, lean_object* v_b_1505_){
_start:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_usize_dec_lt(v_i_1504_, v_sz_1503_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v_env_1500_);
lean_inc_ref(v_b_1505_);
return v_b_1505_;
}
else
{
lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_box(0);
v_a_1508_ = lean_array_uget_borrowed(v_as_1502_, v_i_1504_);
lean_inc(v_a_1508_);
lean_inc_ref(v_env_1500_);
v___x_1509_ = l_Lean_findField_x3f(v_env_1500_, v_a_1508_, v_fieldName_1501_);
if (lean_obj_tag(v___x_1509_) == 1)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_env_1500_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1507_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; 
lean_dec(v___x_1509_);
v___x_1512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1504_, v___x_1513_);
v_i_1504_ = v___x_1514_;
v_b_1505_ = v___x_1512_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1516_, lean_object* v_fieldName_1517_, lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_){
_start:
{
size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1516_, v_fieldName_1517_, v_as_1518_, v_sz_boxed_1522_, v_i_boxed_1523_, v_b_1521_);
lean_dec_ref(v_b_1521_);
lean_dec_ref(v_as_1518_);
lean_dec(v_fieldName_1517_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1525_, lean_object* v_structName_1526_, lean_object* v_fieldName_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_findField_x3f(v_env_1525_, v_structName_1526_, v_fieldName_1527_);
lean_dec(v_fieldName_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1532_, lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1535_, v_sz_1534_);
if (v___x_1537_ == 0)
{
lean_inc_ref(v_b_1536_);
return v_b_1536_;
}
else
{
lean_object* v_a_1538_; lean_object* v_projFn_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_a_1538_ = lean_array_uget_borrowed(v_as_1533_, v_i_1535_);
v_projFn_1539_ = lean_ctor_get(v_a_1538_, 1);
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Lean_Name_isSuffixOf(v_projName_1532_, v_projFn_1539_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; 
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1543_ = ((size_t)1ULL);
v___x_1544_ = lean_usize_add(v_i_1535_, v___x_1543_);
v_i_1535_ = v___x_1544_;
v_b_1536_ = v___x_1542_;
goto _start;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc(v_a_1538_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_a_1538_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1540_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1549_, lean_object* v_as_1550_, lean_object* v_sz_1551_, lean_object* v_i_1552_, lean_object* v_b_1553_){
_start:
{
size_t v_sz_boxed_1554_; size_t v_i_boxed_1555_; lean_object* v_res_1556_; 
v_sz_boxed_1554_ = lean_unbox_usize(v_sz_1551_);
lean_dec(v_sz_1551_);
v_i_boxed_1555_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1549_, v_as_1550_, v_sz_boxed_1554_, v_i_boxed_1555_, v_b_1553_);
lean_dec_ref(v_b_1553_);
lean_dec_ref(v_as_1550_);
lean_dec(v_projName_1549_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1557_, lean_object* v_projName_1558_, lean_object* v_structName_1559_, lean_object* v_a_1560_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_NameSet_contains(v_a_1560_, v_structName_1559_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; lean_object* v_fst_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1607_; 
lean_inc(v_structName_1559_);
lean_inc_ref(v_env_1557_);
v___x_1562_ = l_Lean_getStructureParentInfo(v_env_1557_, v_structName_1559_);
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1587_ = lean_array_size(v___x_1562_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1558_, v___x_1562_, v_sz_1587_, v___x_1588_, v___x_1586_);
v_fst_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1589_, 1);
lean_dec(v_unused_1608_);
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1607_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_fst_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1607_;
goto v_resetjp_1591_;
}
v___jp_1563_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; lean_object* v_fst_1570_; lean_object* v_fst_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1584_; 
v___x_1564_ = l_Lean_NameSet_insert(v_a_1560_, v_structName_1559_);
v___x_1565_ = lean_box(0);
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1567_ = lean_array_size(v___x_1562_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1557_, v_projName_1558_, v___x_1562_, v_sz_1567_, v___x_1568_, v___x_1566_, v___x_1564_);
lean_dec_ref(v___x_1562_);
v_fst_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_fst_1570_);
v_fst_1571_ = lean_ctor_get(v_fst_1570_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_fst_1570_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_fst_1570_, 1);
lean_dec(v_unused_1585_);
v___x_1573_ = v_fst_1570_;
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_fst_1571_);
lean_dec(v_fst_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
if (lean_obj_tag(v_fst_1571_) == 0)
{
lean_object* v_snd_1575_; lean_object* v___x_1577_; 
v_snd_1575_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_snd_1575_);
lean_dec_ref(v___x_1569_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v_snd_1575_);
lean_ctor_set(v___x_1573_, 0, v___x_1565_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_snd_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
lean_object* v_snd_1579_; lean_object* v_val_1580_; lean_object* v___x_1582_; 
v_snd_1579_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_snd_1579_);
lean_dec_ref(v___x_1569_);
v_val_1580_ = lean_ctor_get(v_fst_1571_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_fst_1571_, 1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v_snd_1579_);
lean_ctor_set(v___x_1573_, 0, v_val_1580_);
v___x_1582_ = v___x_1573_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_val_1580_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_snd_1579_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v_resetjp_1591_:
{
if (lean_obj_tag(v_fst_1590_) == 0)
{
lean_del_object(v___x_1592_);
goto v___jp_1563_;
}
else
{
lean_object* v_val_1594_; 
v_val_1594_ = lean_ctor_get(v_fst_1590_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_fst_1590_, 1);
if (lean_obj_tag(v_val_1594_) == 1)
{
lean_object* v_val_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v___x_1562_);
lean_dec(v_structName_1559_);
lean_dec_ref(v_env_1557_);
v_val_1595_ = lean_ctor_get(v_val_1594_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_val_1594_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1597_ = v_val_1594_;
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_val_1595_);
lean_dec(v_val_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1606_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_structName_1599_; lean_object* v___x_1601_; 
v_structName_1599_ = lean_ctor_get(v_val_1595_, 0);
lean_inc(v_structName_1599_);
lean_dec(v_val_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_structName_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_structName_1599_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v_a_1560_);
lean_ctor_set(v___x_1592_, 0, v___x_1601_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_a_1560_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_dec(v_val_1594_);
lean_del_object(v___x_1592_);
goto v___jp_1563_;
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v_structName_1559_);
lean_dec_ref(v_env_1557_);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1560_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1611_, lean_object* v_projName_1612_, lean_object* v_as_1613_, size_t v_sz_1614_, size_t v_i_1615_, lean_object* v_b_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_usize_dec_lt(v_i_1615_, v_sz_1614_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v_env_1611_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_b_1616_);
lean_ctor_set(v___x_1619_, 1, v___y_1617_);
return v___x_1619_;
}
else
{
lean_object* v_a_1620_; lean_object* v_structName_1621_; lean_object* v___x_1622_; lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_b_1616_);
v_a_1620_ = lean_array_uget_borrowed(v_as_1613_, v_i_1615_);
v_structName_1621_ = lean_ctor_get(v_a_1620_, 0);
lean_inc(v_structName_1621_);
lean_inc_ref(v_env_1611_);
v___x_1622_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1611_, v_projName_1612_, v_structName_1621_, v___y_1617_);
v_fst_1623_ = lean_ctor_get(v___x_1622_, 0);
v_snd_1624_ = lean_ctor_get(v___x_1622_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1626_ = v___x_1622_;
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_inc(v_fst_1623_);
lean_dec(v___x_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_box(0);
if (lean_obj_tag(v_fst_1623_) == 1)
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec_ref(v_env_1611_);
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_fst_1623_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1628_);
lean_ctor_set(v___x_1626_, 0, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___x_1628_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_snd_1624_);
return v___x_1632_;
}
}
else
{
lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; 
lean_del_object(v___x_1626_);
lean_dec(v_fst_1623_);
v___x_1634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1635_ = ((size_t)1ULL);
v___x_1636_ = lean_usize_add(v_i_1615_, v___x_1635_);
v_i_1615_ = v___x_1636_;
v_b_1616_ = v___x_1634_;
v___y_1617_ = v_snd_1624_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1639_, lean_object* v_projName_1640_, lean_object* v_as_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_){
_start:
{
size_t v_sz_boxed_1646_; size_t v_i_boxed_1647_; lean_object* v_res_1648_; 
v_sz_boxed_1646_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1647_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1639_, v_projName_1640_, v_as_1641_, v_sz_boxed_1646_, v_i_boxed_1647_, v_b_1644_, v___y_1645_);
lean_dec_ref(v_as_1641_);
lean_dec(v_projName_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1649_, lean_object* v_projName_1650_, lean_object* v_structName_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1649_, v_projName_1650_, v_structName_1651_, v_a_1652_);
lean_dec(v_projName_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1654_, lean_object* v_structName_1655_, lean_object* v_projName_1656_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_fst_1659_; 
v___x_1657_ = l_Lean_NameSet_empty;
v___x_1658_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1654_, v_projName_1656_, v_structName_1655_, v___x_1657_);
v_fst_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_fst_1659_);
lean_dec_ref(v___x_1658_);
return v_fst_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1660_, lean_object* v_structName_1661_, lean_object* v_projName_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_findParentProjStruct_x3f(v_env_1660_, v_structName_1661_, v_projName_1662_);
lean_dec(v_projName_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1669_ = l_Lean_Name_append(v_structCtorName_1667_, v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1670_, lean_object* v_structName_1671_, uint8_t v_includeSubobjectFields_1672_, lean_object* v_as_1673_, size_t v_i_1674_, size_t v_stop_1675_, lean_object* v_b_1676_){
_start:
{
lean_object* v___y_1678_; uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_eq(v_i_1674_, v_stop_1675_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_array_uget_borrowed(v_as_1673_, v_i_1674_);
lean_inc(v___x_1683_);
lean_inc(v_structName_1671_);
lean_inc_ref(v_env_1670_);
v___x_1684_ = l_Lean_isSubobjectField_x3f(v_env_1670_, v_structName_1671_, v___x_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_inc(v___x_1683_);
v___x_1685_ = lean_array_push(v_b_1676_, v___x_1683_);
v___y_1678_ = v___x_1685_;
goto v___jp_1677_;
}
else
{
if (v_includeSubobjectFields_1672_ == 0)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; 
v_val_1686_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1684_, 1);
lean_inc_ref(v_env_1670_);
v___x_1687_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1670_, v_val_1686_, v_b_1676_, v_includeSubobjectFields_1672_);
v___y_1678_ = v___x_1687_;
goto v___jp_1677_;
}
else
{
lean_object* v_val_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_val_1688_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1688_);
lean_dec_ref_known(v___x_1684_, 1);
lean_inc(v___x_1683_);
v___x_1689_ = lean_array_push(v_b_1676_, v___x_1683_);
lean_inc_ref(v_env_1670_);
v___x_1690_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1670_, v_val_1688_, v___x_1689_, v_includeSubobjectFields_1672_);
v___y_1678_ = v___x_1690_;
goto v___jp_1677_;
}
}
}
else
{
lean_dec(v_structName_1671_);
lean_dec_ref(v_env_1670_);
return v_b_1676_;
}
v___jp_1677_:
{
size_t v___x_1679_; size_t v___x_1680_; 
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1674_, v___x_1679_);
v_i_1674_ = v___x_1680_;
v_b_1676_ = v___y_1678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1691_, lean_object* v_structName_1692_, lean_object* v_fullNames_1693_, uint8_t v_includeSubobjectFields_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
lean_inc(v_structName_1692_);
lean_inc_ref(v_env_1691_);
v___x_1695_ = l_Lean_getStructureFields(v_env_1691_, v_structName_1692_);
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_array_get_size(v___x_1695_);
v___x_1698_ = lean_nat_dec_lt(v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_dec_ref(v___x_1695_);
lean_dec(v_structName_1692_);
lean_dec_ref(v_env_1691_);
return v_fullNames_1693_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_nat_dec_le(v___x_1697_, v___x_1697_);
if (v___x_1699_ == 0)
{
if (v___x_1698_ == 0)
{
lean_dec_ref(v___x_1695_);
lean_dec(v_structName_1692_);
lean_dec_ref(v_env_1691_);
return v_fullNames_1693_;
}
else
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = lean_usize_of_nat(v___x_1697_);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1691_, v_structName_1692_, v_includeSubobjectFields_1694_, v___x_1695_, v___x_1700_, v___x_1701_, v_fullNames_1693_);
lean_dec_ref(v___x_1695_);
return v___x_1702_;
}
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1697_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1691_, v_structName_1692_, v_includeSubobjectFields_1694_, v___x_1695_, v___x_1703_, v___x_1704_, v_fullNames_1693_);
lean_dec_ref(v___x_1695_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1706_, lean_object* v_structName_1707_, lean_object* v_fullNames_1708_, lean_object* v_includeSubobjectFields_1709_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1710_; lean_object* v_res_1711_; 
v_includeSubobjectFields_boxed_1710_ = lean_unbox(v_includeSubobjectFields_1709_);
v_res_1711_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1706_, v_structName_1707_, v_fullNames_1708_, v_includeSubobjectFields_boxed_1710_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1712_, lean_object* v_structName_1713_, lean_object* v_includeSubobjectFields_1714_, lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_, lean_object* v_b_1718_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1719_; size_t v_i_boxed_1720_; size_t v_stop_boxed_1721_; lean_object* v_res_1722_; 
v_includeSubobjectFields_boxed_1719_ = lean_unbox(v_includeSubobjectFields_1714_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1721_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1712_, v_structName_1713_, v_includeSubobjectFields_boxed_1719_, v_as_1715_, v_i_boxed_1720_, v_stop_boxed_1721_, v_b_1718_);
lean_dec_ref(v_as_1715_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1723_, lean_object* v_structName_1724_, uint8_t v_includeSubobjectFields_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1727_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1723_, v_structName_1724_, v___x_1726_, v_includeSubobjectFields_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1728_, lean_object* v_structName_1729_, lean_object* v_includeSubobjectFields_1730_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1731_; lean_object* v_res_1732_; 
v_includeSubobjectFields_boxed_1731_ = lean_unbox(v_includeSubobjectFields_1730_);
v_res_1732_ = l_Lean_getStructureFieldsFlattened(v_env_1728_, v_structName_1729_, v_includeSubobjectFields_boxed_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1733_, lean_object* v_constName_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_getStructureInfo_x3f(v_env_1733_, v_constName_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
else
{
uint8_t v___x_1737_; 
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = 1;
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1738_, lean_object* v_constName_1739_){
_start:
{
uint8_t v_res_1740_; lean_object* v_r_1741_; 
v_res_1740_ = l_Lean_isStructure(v_env_1738_, v_constName_1739_);
v_r_1741_ = lean_box(v_res_1740_);
return v_r_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1742_, lean_object* v_structName_1743_, lean_object* v_fieldName_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_getFieldInfo_x3f(v_env_1742_, v_structName_1743_, v_fieldName_1744_);
if (lean_obj_tag(v___x_1745_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_val_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_projFn_1750_; lean_object* v___x_1752_; 
v_projFn_1750_ = lean_ctor_get(v_val_1746_, 1);
lean_inc(v_projFn_1750_);
lean_dec(v_val_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v_projFn_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_projFn_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v___x_1745_);
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1756_, lean_object* v_structName_1757_, lean_object* v_fieldName_1758_){
_start:
{
lean_object* v___x_1759_; 
lean_inc_ref(v_env_1756_);
v___x_1759_ = l_Lean_getProjFnForField_x3f(v_env_1756_, v_structName_1757_, v_fieldName_1758_);
if (lean_obj_tag(v___x_1759_) == 1)
{
lean_object* v_val_1760_; lean_object* v___x_1761_; 
v_val_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc_n(v_val_1760_, 2);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1756_, v_val_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1762_; 
lean_dec(v_val_1760_);
v___x_1762_ = lean_box(0);
return v___x_1762_;
}
else
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
v_val_1763_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1765_ = v___x_1761_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_val_1760_);
lean_ctor_set(v___x_1767_, 1, v_val_1763_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v___x_1772_; 
lean_dec(v___x_1759_);
lean_dec_ref(v_env_1756_);
v___x_1772_ = lean_box(0);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1778_ = l_Lean_Name_append(v_projFn_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1784_ = l_Lean_Name_append(v_projFn_1782_, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1785_, lean_object* v_env_1786_, lean_object* v_structName_1787_, lean_object* v_fieldName_1788_){
_start:
{
lean_object* v___x_1789_; 
lean_inc(v_fieldName_1788_);
lean_inc(v_structName_1787_);
lean_inc_ref(v_env_1786_);
v___x_1789_ = l_Lean_getProjFnForField_x3f(v_env_1786_, v_structName_1787_, v_fieldName_1788_);
if (lean_obj_tag(v___x_1789_) == 1)
{
lean_object* v_val_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_fieldName_1788_);
lean_dec(v_structName_1787_);
v_val_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_val_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_defFn_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; 
v_defFn_1794_ = lean_apply_1(v_mkName_1785_, v_val_1790_);
v___x_1795_ = 1;
lean_inc(v_defFn_1794_);
v___x_1796_ = l_Lean_Environment_contains(v_env_1786_, v_defFn_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec(v_defFn_1794_);
lean_del_object(v___x_1792_);
v___x_1797_ = lean_box(0);
return v___x_1797_;
}
else
{
lean_object* v___x_1799_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_defFn_1794_);
v___x_1799_ = v___x_1792_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_defFn_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v_defFn_1803_; uint8_t v___x_1804_; uint8_t v___x_1805_; 
lean_dec(v___x_1789_);
v___x_1802_ = l_Lean_Name_append(v_structName_1787_, v_fieldName_1788_);
v_defFn_1803_ = lean_apply_1(v_mkName_1785_, v___x_1802_);
v___x_1804_ = 1;
lean_inc(v_defFn_1803_);
v___x_1805_ = l_Lean_Environment_contains(v_env_1786_, v_defFn_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
lean_dec(v_defFn_1803_);
v___x_1806_ = lean_box(0);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_defFn_1803_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1809_, lean_object* v_structName_1810_, lean_object* v_fieldName_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1813_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1812_, v_env_1809_, v_structName_1810_, v_fieldName_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1815_, lean_object* v_structName_1816_, lean_object* v_fieldName_1817_){
_start:
{
lean_object* v___x_1818_; 
lean_inc(v_fieldName_1817_);
lean_inc(v_structName_1816_);
lean_inc_ref(v_env_1815_);
v___x_1818_ = l_Lean_getDefaultFnForField_x3f(v_env_1815_, v_structName_1816_, v_fieldName_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1820_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1819_, v_env_1815_, v_structName_1816_, v_fieldName_1817_);
return v___x_1820_;
}
else
{
lean_dec(v_fieldName_1817_);
lean_dec(v_structName_1816_);
lean_dec_ref(v_env_1815_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1826_ = l_Lean_Name_append(v_projFn_1824_, v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1828_, lean_object* v_structName_1829_, lean_object* v_fieldName_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1832_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1831_, v_env_1828_, v_structName_1829_, v_fieldName_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1833_, lean_object* v_env_1834_, lean_object* v_baseStructName_1835_, lean_object* v_as_1836_, lean_object* v_i_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_snd_1840_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_array_get_size(v_as_1836_);
v___x_1845_ = lean_nat_dec_lt(v_i_1837_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v_i_1837_);
lean_dec_ref(v_env_1834_);
lean_dec(v_path_1833_);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v___y_1838_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_subobject_x3f_1849_; 
v___x_1848_ = lean_array_fget_borrowed(v_as_1836_, v_i_1837_);
v_subobject_x3f_1849_ = lean_ctor_get(v___x_1848_, 2);
if (lean_obj_tag(v_subobject_x3f_1849_) == 1)
{
lean_object* v_projFn_1850_; lean_object* v_val_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_fst_1854_; 
v_projFn_1850_ = lean_ctor_get(v___x_1848_, 1);
v_val_1851_ = lean_ctor_get(v_subobject_x3f_1849_, 0);
lean_inc(v_path_1833_);
lean_inc(v_projFn_1850_);
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_projFn_1850_);
lean_ctor_set(v___x_1852_, 1, v_path_1833_);
lean_inc(v_val_1851_);
lean_inc_ref(v_env_1834_);
v___x_1853_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1834_, v_baseStructName_1835_, v_val_1851_, v___x_1852_, v___y_1838_);
v_fst_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_fst_1854_);
if (lean_obj_tag(v_fst_1854_) == 0)
{
lean_object* v_snd_1855_; 
v_snd_1855_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1853_);
v_snd_1840_ = v_snd_1855_;
goto v___jp_1839_;
}
else
{
lean_dec_ref_known(v_fst_1854_, 1);
lean_dec(v_i_1837_);
lean_dec_ref(v_env_1834_);
lean_dec(v_path_1833_);
return v___x_1853_;
}
}
else
{
v_snd_1840_ = v___y_1838_;
goto v___jp_1839_;
}
}
v___jp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_i_1837_, v___x_1841_);
lean_dec(v_i_1837_);
v_i_1837_ = v___x_1842_;
v___y_1838_ = v_snd_1840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1856_, lean_object* v_baseStructName_1857_, lean_object* v_structName_1858_, lean_object* v_path_1859_, lean_object* v_a_1860_){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = lean_name_eq(v_baseStructName_1857_, v_structName_1858_);
if (v___x_1874_ == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Lean_NameSet_contains(v_a_1860_, v_structName_1858_);
if (v___x_1875_ == 0)
{
goto v___jp_1861_;
}
else
{
if (v___x_1874_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec(v_path_1859_);
lean_dec(v_structName_1858_);
lean_dec_ref(v_env_1856_);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_a_1860_);
return v___x_1877_;
}
else
{
goto v___jp_1861_;
}
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec(v_structName_1858_);
lean_dec_ref(v_env_1856_);
v___x_1878_ = l_List_reverse___redArg(v_path_1859_);
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v_a_1860_);
return v___x_1880_;
}
v___jp_1861_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_inc(v_structName_1858_);
v___x_1862_ = l_Lean_NameSet_insert(v_a_1860_, v_structName_1858_);
lean_inc_ref(v_env_1856_);
v___x_1863_ = l_Lean_getStructureInfo_x3f(v_env_1856_, v_structName_1858_);
if (lean_obj_tag(v___x_1863_) == 1)
{
lean_object* v_val_1864_; lean_object* v_fieldInfo_1865_; lean_object* v_parentInfo_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_fst_1869_; 
v_val_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v_fieldInfo_1865_ = lean_ctor_get(v_val_1864_, 2);
lean_inc_ref(v_fieldInfo_1865_);
v_parentInfo_1866_ = lean_ctor_get(v_val_1864_, 3);
lean_inc_ref(v_parentInfo_1866_);
lean_dec(v_val_1864_);
v___x_1867_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1856_);
lean_inc(v_path_1859_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1859_, v_env_1856_, v_baseStructName_1857_, v_fieldInfo_1865_, v___x_1867_, v___x_1862_);
lean_dec_ref(v_fieldInfo_1865_);
v_fst_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_fst_1869_);
if (lean_obj_tag(v_fst_1869_) == 0)
{
lean_object* v_snd_1870_; lean_object* v___x_1871_; 
v_snd_1870_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_snd_1870_);
lean_dec_ref(v___x_1868_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1859_, v_env_1856_, v_baseStructName_1857_, v_parentInfo_1866_, v___x_1867_, v_snd_1870_);
lean_dec_ref(v_parentInfo_1866_);
return v___x_1871_;
}
else
{
lean_dec_ref_known(v_fst_1869_, 1);
lean_dec_ref(v_parentInfo_1866_);
lean_dec(v_path_1859_);
lean_dec_ref(v_env_1856_);
return v___x_1868_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec(v___x_1863_);
lean_dec(v_path_1859_);
lean_dec_ref(v_env_1856_);
v___x_1872_ = lean_box(0);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1862_);
return v___x_1873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1881_, lean_object* v_env_1882_, lean_object* v_baseStructName_1883_, lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_array_get_size(v_as_1884_);
v___x_1888_ = lean_nat_dec_lt(v_i_1885_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_i_1885_);
lean_dec_ref(v_env_1882_);
lean_dec(v_path_1881_);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___y_1886_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; lean_object* v_structName_1892_; lean_object* v_projFn_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_fst_1896_; 
v___x_1891_ = lean_array_fget_borrowed(v_as_1884_, v_i_1885_);
v_structName_1892_ = lean_ctor_get(v___x_1891_, 0);
v_projFn_1893_ = lean_ctor_get(v___x_1891_, 1);
lean_inc(v_path_1881_);
lean_inc(v_projFn_1893_);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_projFn_1893_);
lean_ctor_set(v___x_1894_, 1, v_path_1881_);
lean_inc(v_structName_1892_);
lean_inc_ref(v_env_1882_);
v___x_1895_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1882_, v_baseStructName_1883_, v_structName_1892_, v___x_1894_, v___y_1886_);
v_fst_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_fst_1896_);
if (lean_obj_tag(v_fst_1896_) == 0)
{
lean_object* v_snd_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_snd_1897_ = lean_ctor_get(v___x_1895_, 1);
lean_inc(v_snd_1897_);
lean_dec_ref(v___x_1895_);
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_i_1885_, v___x_1898_);
lean_dec(v_i_1885_);
v_i_1885_ = v___x_1899_;
v___y_1886_ = v_snd_1897_;
goto _start;
}
else
{
lean_dec_ref_known(v_fst_1896_, 1);
lean_dec(v_i_1885_);
lean_dec_ref(v_env_1882_);
lean_dec(v_path_1881_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1901_, lean_object* v_env_1902_, lean_object* v_baseStructName_1903_, lean_object* v_as_1904_, lean_object* v_i_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1901_, v_env_1902_, v_baseStructName_1903_, v_as_1904_, v_i_1905_, v___y_1906_);
lean_dec_ref(v_as_1904_);
lean_dec(v_baseStructName_1903_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1908_, lean_object* v_env_1909_, lean_object* v_baseStructName_1910_, lean_object* v_as_1911_, lean_object* v_i_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1908_, v_env_1909_, v_baseStructName_1910_, v_as_1911_, v_i_1912_, v___y_1913_);
lean_dec_ref(v_as_1911_);
lean_dec(v_baseStructName_1910_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1915_, lean_object* v_baseStructName_1916_, lean_object* v_structName_1917_, lean_object* v_path_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1915_, v_baseStructName_1916_, v_structName_1917_, v_path_1918_, v_a_1919_);
lean_dec(v_baseStructName_1916_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1921_, lean_object* v_baseStructName_1922_, lean_object* v_structName_1923_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_fst_1927_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = l_Lean_NameSet_empty;
v___x_1926_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1921_, v_baseStructName_1922_, v_structName_1923_, v___x_1924_, v___x_1925_);
v_fst_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_fst_1927_);
lean_dec_ref(v___x_1926_);
return v_fst_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1928_, lean_object* v_baseStructName_1929_, lean_object* v_structName_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_getPathToBaseStructure_x3f(v_env_1928_, v_baseStructName_1929_, v_structName_1930_);
lean_dec(v_baseStructName_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1932_, lean_object* v_constName_1933_){
_start:
{
uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = 0;
v___x_1935_ = l_Lean_Environment_find_x3f(v_env_1932_, v_constName_1933_, v___x_1934_);
if (lean_obj_tag(v___x_1935_) == 1)
{
lean_object* v_val_1936_; 
v_val_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v___x_1935_, 1);
if (lean_obj_tag(v_val_1936_) == 5)
{
lean_object* v_val_1937_; lean_object* v_numIndices_1938_; lean_object* v_ctors_1939_; uint8_t v_isRec_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_val_1937_ = lean_ctor_get(v_val_1936_, 0);
lean_inc_ref(v_val_1937_);
lean_dec_ref_known(v_val_1936_, 1);
v_numIndices_1938_ = lean_ctor_get(v_val_1937_, 2);
lean_inc(v_numIndices_1938_);
v_ctors_1939_ = lean_ctor_get(v_val_1937_, 4);
lean_inc(v_ctors_1939_);
v_isRec_1940_ = lean_ctor_get_uint8(v_val_1937_, sizeof(void*)*6);
lean_dec_ref(v_val_1937_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_nat_dec_eq(v_numIndices_1938_, v___x_1941_);
lean_dec(v_numIndices_1938_);
if (v___x_1942_ == 0)
{
lean_dec(v_ctors_1939_);
return v___x_1934_;
}
else
{
if (lean_obj_tag(v_ctors_1939_) == 1)
{
lean_object* v_tail_1943_; 
v_tail_1943_ = lean_ctor_get(v_ctors_1939_, 1);
lean_inc(v_tail_1943_);
lean_dec_ref_known(v_ctors_1939_, 2);
if (lean_obj_tag(v_tail_1943_) == 0)
{
if (v_isRec_1940_ == 0)
{
return v___x_1942_;
}
else
{
return v___x_1934_;
}
}
else
{
lean_dec(v_tail_1943_);
return v___x_1934_;
}
}
else
{
lean_dec(v_ctors_1939_);
return v___x_1934_;
}
}
}
else
{
lean_dec(v_val_1936_);
return v___x_1934_;
}
}
else
{
lean_dec(v___x_1935_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1944_, lean_object* v_constName_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l_Lean_isNonRecStructure(v_env_1944_, v_constName_1945_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_panic_fn_borrowed(v___x_1949_, v_msg_1948_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1952_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1953_ = lean_unsigned_to_nat(11u);
v___x_1954_ = lean_unsigned_to_nat(374u);
v___x_1955_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1956_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1957_ = l_mkPanicMessageWithDecl(v___x_1956_, v___x_1955_, v___x_1954_, v___x_1953_, v___x_1952_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1958_, lean_object* v_constName_1959_){
_start:
{
uint8_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = 0;
lean_inc_ref(v_env_1958_);
v___x_1964_ = l_Lean_Environment_find_x3f(v_env_1958_, v_constName_1959_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 1)
{
lean_object* v_val_1965_; 
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_val_1965_) == 5)
{
lean_object* v_val_1966_; lean_object* v_numIndices_1967_; lean_object* v_ctors_1968_; uint8_t v_isRec_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_val_1966_ = lean_ctor_get(v_val_1965_, 0);
lean_inc_ref(v_val_1966_);
lean_dec_ref_known(v_val_1965_, 1);
v_numIndices_1967_ = lean_ctor_get(v_val_1966_, 2);
lean_inc(v_numIndices_1967_);
v_ctors_1968_ = lean_ctor_get(v_val_1966_, 4);
lean_inc(v_ctors_1968_);
v_isRec_1969_ = lean_ctor_get_uint8(v_val_1966_, sizeof(void*)*6);
lean_dec_ref(v_val_1966_);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_nat_dec_eq(v_numIndices_1967_, v___x_1970_);
lean_dec(v_numIndices_1967_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
lean_dec(v_ctors_1968_);
lean_dec_ref(v_env_1958_);
v___x_1972_ = lean_box(0);
return v___x_1972_;
}
else
{
if (lean_obj_tag(v_ctors_1968_) == 1)
{
lean_object* v_tail_1973_; 
v_tail_1973_ = lean_ctor_get(v_ctors_1968_, 1);
if (lean_obj_tag(v_tail_1973_) == 0)
{
if (v_isRec_1969_ == 0)
{
lean_object* v_head_1974_; lean_object* v___x_1975_; 
v_head_1974_ = lean_ctor_get(v_ctors_1968_, 0);
lean_inc(v_head_1974_);
lean_dec_ref_known(v_ctors_1968_, 2);
v___x_1975_ = l_Lean_Environment_find_x3f(v_env_1958_, v_head_1974_, v_isRec_1969_);
if (lean_obj_tag(v___x_1975_) == 1)
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
v_val_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
if (lean_obj_tag(v_val_1976_) == 6)
{
lean_object* v_val_1980_; lean_object* v___x_1982_; 
v_val_1980_ = lean_ctor_get(v_val_1976_, 0);
lean_inc_ref(v_val_1980_);
lean_dec_ref_known(v_val_1976_, 1);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v_val_1980_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_val_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
goto v___jp_1960_;
}
}
}
else
{
lean_dec(v___x_1975_);
goto v___jp_1960_;
}
}
else
{
lean_object* v___x_1985_; 
lean_dec_ref_known(v_ctors_1968_, 2);
lean_dec_ref(v_env_1958_);
v___x_1985_ = lean_box(0);
return v___x_1985_;
}
}
else
{
lean_object* v___x_1986_; 
lean_dec_ref_known(v_ctors_1968_, 2);
lean_dec_ref(v_env_1958_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
}
else
{
lean_object* v___x_1987_; 
lean_dec(v_ctors_1968_);
lean_dec_ref(v_env_1958_);
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
}
}
else
{
lean_object* v___x_1988_; 
lean_dec(v_val_1965_);
lean_dec_ref(v_env_1958_);
v___x_1988_ = lean_box(0);
return v___x_1988_;
}
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___x_1964_);
lean_dec_ref(v_env_1958_);
v___x_1989_ = lean_box(0);
return v___x_1989_;
}
v___jp_1960_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1962_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1990_, lean_object* v_constName_1991_){
_start:
{
uint8_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = 0;
lean_inc_ref(v_env_1990_);
v___x_1993_ = l_Lean_Environment_find_x3f(v_env_1990_, v_constName_1991_, v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 1)
{
lean_object* v_val_1994_; 
v_val_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_val_1994_) == 5)
{
lean_object* v_val_1995_; lean_object* v_numIndices_1996_; lean_object* v_ctors_1997_; uint8_t v_isRec_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_val_1995_ = lean_ctor_get(v_val_1994_, 0);
lean_inc_ref(v_val_1995_);
lean_dec_ref_known(v_val_1994_, 1);
v_numIndices_1996_ = lean_ctor_get(v_val_1995_, 2);
lean_inc(v_numIndices_1996_);
v_ctors_1997_ = lean_ctor_get(v_val_1995_, 4);
lean_inc(v_ctors_1997_);
v_isRec_1998_ = lean_ctor_get_uint8(v_val_1995_, sizeof(void*)*6);
lean_dec_ref(v_val_1995_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_nat_dec_eq(v_numIndices_1996_, v___x_1999_);
lean_dec(v_numIndices_1996_);
if (v___x_2000_ == 0)
{
lean_dec(v_ctors_1997_);
lean_dec_ref(v_env_1990_);
return v___x_1999_;
}
else
{
if (lean_obj_tag(v_ctors_1997_) == 1)
{
lean_object* v_tail_2001_; 
v_tail_2001_ = lean_ctor_get(v_ctors_1997_, 1);
if (lean_obj_tag(v_tail_2001_) == 0)
{
if (v_isRec_1998_ == 0)
{
lean_object* v_head_2002_; lean_object* v___x_2003_; 
v_head_2002_ = lean_ctor_get(v_ctors_1997_, 0);
lean_inc(v_head_2002_);
lean_dec_ref_known(v_ctors_1997_, 2);
v___x_2003_ = l_Lean_Environment_find_x3f(v_env_1990_, v_head_2002_, v_isRec_1998_);
if (lean_obj_tag(v___x_2003_) == 1)
{
lean_object* v_val_2004_; 
v_val_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v___x_2003_, 1);
if (lean_obj_tag(v_val_2004_) == 6)
{
lean_object* v_val_2005_; lean_object* v_numFields_2006_; 
v_val_2005_ = lean_ctor_get(v_val_2004_, 0);
lean_inc_ref(v_val_2005_);
lean_dec_ref_known(v_val_2004_, 1);
v_numFields_2006_ = lean_ctor_get(v_val_2005_, 4);
lean_inc(v_numFields_2006_);
lean_dec_ref(v_val_2005_);
return v_numFields_2006_;
}
else
{
lean_dec(v_val_2004_);
return v___x_1999_;
}
}
else
{
lean_dec(v___x_2003_);
return v___x_1999_;
}
}
else
{
lean_dec_ref_known(v_ctors_1997_, 2);
lean_dec_ref(v_env_1990_);
return v___x_1999_;
}
}
else
{
lean_dec_ref_known(v_ctors_1997_, 2);
lean_dec_ref(v_env_1990_);
return v___x_1999_;
}
}
else
{
lean_dec(v_ctors_1997_);
lean_dec_ref(v_env_1990_);
return v___x_1999_;
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_val_1994_);
lean_dec_ref(v_env_1990_);
v___x_2007_ = lean_unsigned_to_nat(0u);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v___x_1993_);
lean_dec_ref(v_env_1990_);
v___x_2008_ = lean_unsigned_to_nat(0u);
return v___x_2008_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_2017_);
return v_res_2019_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___f_2021_; 
v___x_2020_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_2021_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2021_, 0, v___x_2020_);
return v___f_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___f_2023_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_box(1);
v___x_2026_ = l_Lean_registerEnvExtension___redArg(v___f_2023_, v___x_2024_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2029_, lean_object* v_structName_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v_asyncMode_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = l_Lean_structureResolutionExt;
v_asyncMode_2032_ = lean_ctor_get(v___x_2031_, 2);
v___x_2033_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2034_ = lean_box(0);
v___x_2035_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2033_, v___x_2031_, v_env_2029_, v_asyncMode_2032_, v___x_2034_);
v___x_2036_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2035_, v_structName_2030_);
lean_dec(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2037_, lean_object* v_structName_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2037_, v_structName_2038_);
lean_dec(v_structName_2038_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2040_, lean_object* v___x_2041_, lean_object* v_structName_2042_, lean_object* v_resolutionOrder_2043_, lean_object* v_s_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2040_, v___x_2041_, v_s_2044_, v_structName_2042_, v_resolutionOrder_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2046_, lean_object* v_env_2047_){
_start:
{
lean_object* v___x_2048_; lean_object* v_asyncMode_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2048_ = l_Lean_structureResolutionExt;
v_asyncMode_2049_ = lean_ctor_get(v___x_2048_, 2);
v___x_2050_ = lean_box(0);
v___x_2051_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2048_, v_env_2047_, v___f_2046_, v_asyncMode_2049_, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2052_, lean_object* v_structName_2053_, lean_object* v_resolutionOrder_2054_){
_start:
{
lean_object* v_modifyEnv_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
v_modifyEnv_2055_ = lean_ctor_get(v_inst_2052_, 1);
lean_inc(v_modifyEnv_2055_);
lean_dec_ref(v_inst_2052_);
v___x_2056_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2057_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2058_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2058_, 0, v___x_2056_);
lean_closure_set(v___f_2058_, 1, v___x_2057_);
lean_closure_set(v___f_2058_, 2, v_structName_2053_);
lean_closure_set(v___f_2058_, 3, v_resolutionOrder_2054_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2059_, 0, v___f_2058_);
v___x_2060_ = lean_apply_1(v_modifyEnv_2055_, v___f_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2061_, lean_object* v_inst_2062_, lean_object* v_structName_2063_, lean_object* v_resolutionOrder_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2062_, v_structName_2063_, v_resolutionOrder_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2083_, lean_object* v_resOrders_2084_, lean_object* v___x_2085_, lean_object* v_toPure_2086_, lean_object* v_____s_2087_){
_start:
{
lean_object* v_fst_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2103_; 
v_fst_2088_ = lean_ctor_get(v_____s_2087_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_____s_2087_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_____s_2087_, 1);
lean_dec(v_unused_2104_);
v___x_2090_ = v_____s_2087_;
v_isShared_2091_ = v_isSharedCheck_2103_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_fst_2088_);
lean_dec(v_____s_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2103_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
if (lean_obj_tag(v_fst_2088_) == 0)
{
uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2092_ = 0;
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_array_get_borrowed(v___x_2083_, v_resOrders_2084_, v___x_2093_);
v___x_2095_ = lean_array_get_borrowed(v___x_2085_, v___x_2094_, v___x_2093_);
v___x_2096_ = lean_box(v___x_2092_);
lean_inc(v___x_2095_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2095_);
lean_ctor_set(v___x_2090_, 0, v___x_2096_);
v___x_2098_ = v___x_2090_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2095_);
v___x_2098_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_apply_2(v_toPure_2086_, lean_box(0), v___x_2098_);
return v___x_2099_;
}
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2102_; 
lean_del_object(v___x_2090_);
v_val_2101_ = lean_ctor_get(v_fst_2088_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_fst_2088_, 1);
v___x_2102_ = lean_apply_2(v_toPure_2086_, lean_box(0), v_val_2101_);
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2105_, lean_object* v_resOrders_2106_, lean_object* v___x_2107_, lean_object* v_toPure_2108_, lean_object* v_____s_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2105_, v_resOrders_2106_, v___x_2107_, v_toPure_2108_, v_____s_2109_);
lean_dec(v___x_2107_);
lean_dec_ref(v_resOrders_2106_);
lean_dec_ref(v___x_2105_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2111_, lean_object* v_____do__lift_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_apply_2(v_toPure_2111_, lean_box(0), v_____do__lift_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2114_, lean_object* v_toPure_2115_, lean_object* v___x_2116_, lean_object* v_____s_2117_){
_start:
{
lean_object* v_fst_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2136_; 
v_fst_2118_ = lean_ctor_get(v_____s_2117_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_____s_2117_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_____s_2117_, 1);
lean_dec(v_unused_2137_);
v___x_2120_ = v_____s_2117_;
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_fst_2118_);
lean_dec(v_____s_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
if (lean_obj_tag(v_fst_2118_) == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_del_object(v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2114_);
v___x_2123_ = lean_apply_2(v_toPure_2115_, lean_box(0), v___x_2122_);
return v___x_2123_;
}
else
{
lean_object* v___x_2125_; 
lean_dec_ref(v___x_2114_);
lean_inc_ref(v_fst_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2116_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_fst_2118_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2116_);
v___x_2125_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
v_isSharedCheck_2133_ = !lean_is_exclusive(v_fst_2118_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_fst_2118_, 0);
lean_dec(v_unused_2134_);
v___x_2127_ = v_fst_2118_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v_fst_2118_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2125_);
v___x_2130_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_apply_2(v_toPure_2115_, lean_box(0), v___x_2130_);
return v___x_2131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2138_, lean_object* v_next_2139_, lean_object* v_G_2140_, lean_object* v_____do__lift_2141_){
_start:
{
if (lean_obj_tag(v_____do__lift_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
lean_dec(v_G_2140_);
v_a_2142_ = lean_ctor_get(v_____do__lift_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v_____do__lift_2141_, 1);
v___x_2143_ = lean_apply_2(v_toPure_2138_, lean_box(0), v_a_2142_);
return v___x_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec(v_toPure_2138_);
v_a_2144_ = lean_ctor_get(v_____do__lift_2141_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v_____do__lift_2141_, 1);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_next_2139_, v___x_2145_);
v___x_2147_ = lean_apply_4(v_G_2140_, v___x_2146_, v_a_2144_, lean_box(0), lean_box(0));
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2148_, lean_object* v_next_2149_, lean_object* v_G_2150_, lean_object* v_____do__lift_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2148_, v_next_2149_, v_G_2150_, v_____do__lift_2151_);
lean_dec(v_next_2149_);
return v_res_2152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2153_, lean_object* v_v_2154_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_name_eq(v_v_2154_, v___x_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2156_, lean_object* v_v_2157_){
_start:
{
uint8_t v_res_2158_; lean_object* v_r_2159_; 
v_res_2158_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2156_, v_v_2157_);
lean_dec(v_v_2157_);
lean_dec(v___x_2156_);
v_r_2159_ = lean_box(v_res_2158_);
return v_r_2159_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2179_, lean_object* v___f_2180_, lean_object* v_resOrder_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_array_2186_; lean_object* v_start_2187_; lean_object* v_stop_2188_; uint8_t v___x_2189_; lean_object* v___y_2191_; 
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_array_get_size(v_resOrder_2181_);
v___x_2184_ = l_Array_toSubarray___redArg(v_resOrder_2181_, v___x_2182_, v___x_2183_);
v___x_2185_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2186_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_ref(v_array_2186_);
v_start_2187_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_start_2187_);
v_stop_2188_ = lean_ctor_get(v___x_2184_, 2);
lean_inc(v_stop_2188_);
lean_dec_ref(v___x_2184_);
v___x_2189_ = lean_nat_dec_lt(v_start_2187_, v_stop_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v_stop_2188_);
lean_dec(v_start_2187_);
lean_dec_ref(v_array_2186_);
lean_dec_ref(v___f_2180_);
return v___x_2179_;
}
else
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_array_get_size(v_array_2186_);
v___x_2199_ = lean_nat_dec_le(v_stop_2188_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_dec(v_stop_2188_);
v___y_2191_ = v___x_2198_;
goto v___jp_2190_;
}
else
{
v___y_2191_ = v_stop_2188_;
goto v___jp_2190_;
}
}
v___jp_2190_:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_nat_dec_lt(v_start_2187_, v___y_2191_);
if (v___x_2192_ == 0)
{
lean_dec(v___y_2191_);
lean_dec(v_start_2187_);
lean_dec_ref(v_array_2186_);
lean_dec_ref(v___f_2180_);
return v___x_2189_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2193_ = lean_usize_of_nat(v_start_2187_);
lean_dec(v_start_2187_);
v___x_2194_ = lean_usize_of_nat(v___y_2191_);
lean_dec(v___y_2191_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2185_, v___f_2180_, v_array_2186_, v___x_2193_, v___x_2194_);
v___x_2196_ = lean_unbox(v___x_2195_);
lean_dec(v___x_2195_);
if (v___x_2196_ == 0)
{
return v___x_2192_;
}
else
{
uint8_t v___x_2197_; 
v___x_2197_ = 0;
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2200_, lean_object* v___f_2201_, lean_object* v_resOrder_2202_){
_start:
{
uint8_t v___x_1715__boxed_2203_; uint8_t v_res_2204_; lean_object* v_r_2205_; 
v___x_1715__boxed_2203_ = lean_unbox(v___x_2200_);
v_res_2204_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2203_, v___f_2201_, v_resOrder_2202_);
v_r_2205_ = lean_box(v_res_2204_);
return v_r_2205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2206_, uint8_t v___y_2207_, lean_object* v_v_2208_){
_start:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_apply_1(v___f_2206_, v_v_2208_);
v___x_2210_ = lean_unbox(v___x_2209_);
if (v___x_2210_ == 0)
{
return v___y_2207_;
}
else
{
uint8_t v___x_2211_; 
v___x_2211_ = 0;
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2212_, lean_object* v___y_2213_, lean_object* v_v_2214_){
_start:
{
uint8_t v___y_1771__boxed_2215_; uint8_t v_res_2216_; lean_object* v_r_2217_; 
v___y_1771__boxed_2215_ = lean_unbox(v___y_2213_);
v_res_2216_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2212_, v___y_1771__boxed_2215_, v_v_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2218_, uint8_t v___x_2219_, lean_object* v_v_2220_){
_start:
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_apply_1(v___f_2218_, v_v_2220_);
v___x_2222_ = lean_unbox(v___x_2221_);
if (v___x_2222_ == 0)
{
return v___x_2219_;
}
else
{
uint8_t v___x_2223_; 
v___x_2223_ = 0;
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2224_, lean_object* v___x_2225_, lean_object* v_v_2226_){
_start:
{
uint8_t v___x_1783__boxed_2227_; uint8_t v_res_2228_; lean_object* v_r_2229_; 
v___x_1783__boxed_2227_ = lean_unbox(v___x_2225_);
v_res_2228_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2224_, v___x_1783__boxed_2227_, v_v_2226_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2230_, lean_object* v_toPure_2231_, lean_object* v___x_2232_, lean_object* v_resOrders_2233_, lean_object* v___x_2234_, lean_object* v___x_2235_, lean_object* v_toBind_2236_, lean_object* v___f_2237_, lean_object* v___x_2238_, lean_object* v_next_2239_, lean_object* v___x_2240_, lean_object* v_next_2241_, lean_object* v_acc_2242_, lean_object* v_h_2243_, lean_object* v_G_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_nat_dec_lt(v_next_2241_, v___x_2230_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec(v_G_2244_);
lean_dec(v_next_2241_);
lean_dec_ref(v___x_2238_);
lean_dec(v___f_2237_);
lean_dec(v_toBind_2236_);
lean_dec(v___x_2235_);
lean_dec_ref(v_resOrders_2233_);
lean_dec(v___x_2230_);
v___x_2246_ = lean_apply_2(v_toPure_2231_, lean_box(0), v_acc_2242_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_array_2251_; lean_object* v_start_2252_; lean_object* v_stop_2253_; lean_object* v___f_2254_; lean_object* v___y_2256_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; uint8_t v___y_2285_; uint8_t v___x_2297_; 
lean_dec_ref(v_acc_2242_);
v___x_2247_ = lean_array_get_borrowed(v___x_2232_, v_resOrders_2233_, v_next_2241_);
v___x_2248_ = lean_array_get(v___x_2234_, v___x_2247_, v___x_2235_);
lean_inc_n(v_next_2241_, 2);
lean_inc(v___x_2235_);
lean_inc_ref(v_resOrders_2233_);
v___x_2249_ = l_Array_toSubarray___redArg(v_resOrders_2233_, v___x_2235_, v_next_2241_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2251_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_array_2251_);
v_start_2252_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_start_2252_);
v_stop_2253_ = lean_ctor_get(v___x_2249_, 2);
lean_inc(v_stop_2253_);
lean_dec_ref(v___x_2249_);
lean_inc(v_toPure_2231_);
v___f_2254_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2254_, 0, v_toPure_2231_);
lean_closure_set(v___f_2254_, 1, v_next_2241_);
lean_closure_set(v___f_2254_, 2, v_G_2244_);
lean_inc(v___x_2248_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2281_, 0, v___x_2248_);
v___x_2282_ = lean_box(v___x_2245_);
v___f_2283_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2283_, 0, v___x_2282_);
lean_closure_set(v___f_2283_, 1, v___f_2281_);
v___x_2297_ = lean_nat_dec_lt(v_start_2252_, v_stop_2253_);
if (v___x_2297_ == 0)
{
lean_dec(v_stop_2253_);
lean_dec(v_start_2252_);
lean_dec_ref(v_array_2251_);
v___y_2285_ = v___x_2245_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2298_; lean_object* v___f_2299_; lean_object* v___y_2301_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2298_ = lean_box(v___x_2245_);
lean_inc_ref(v___f_2283_);
v___f_2299_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2299_, 0, v___f_2283_);
lean_closure_set(v___f_2299_, 1, v___x_2298_);
v___x_2307_ = lean_array_get_size(v_array_2251_);
v___x_2308_ = lean_nat_dec_le(v_stop_2253_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_stop_2253_);
v___y_2301_ = v___x_2307_;
goto v___jp_2300_;
}
else
{
v___y_2301_ = v_stop_2253_;
goto v___jp_2300_;
}
v___jp_2300_:
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_nat_dec_lt(v_start_2252_, v___y_2301_);
if (v___x_2302_ == 0)
{
lean_dec(v___y_2301_);
lean_dec_ref(v___f_2299_);
lean_dec(v_start_2252_);
lean_dec_ref(v_array_2251_);
v___y_2285_ = v___x_2297_;
goto v___jp_2284_;
}
else
{
size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2303_ = lean_usize_of_nat(v_start_2252_);
lean_dec(v_start_2252_);
v___x_2304_ = lean_usize_of_nat(v___y_2301_);
lean_dec(v___y_2301_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2250_, v___f_2299_, v_array_2251_, v___x_2303_, v___x_2304_);
v___x_2306_ = lean_unbox(v___x_2305_);
lean_dec(v___x_2305_);
if (v___x_2306_ == 0)
{
v___y_2285_ = v___x_2302_;
goto v___jp_2284_;
}
else
{
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2248_);
lean_dec(v_next_2241_);
lean_dec(v___x_2235_);
lean_dec_ref(v_resOrders_2233_);
lean_dec(v___x_2230_);
goto v___jp_2259_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_inc(v_toBind_2236_);
v___x_2257_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___y_2256_, v___f_2237_);
v___x_2258_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2257_, v___f_2254_);
return v___x_2258_;
}
v___jp_2259_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2238_);
v___x_2261_ = lean_apply_2(v_toPure_2231_, lean_box(0), v___x_2260_);
v___y_2256_ = v___x_2261_;
goto v___jp_2255_;
}
v___jp_2262_:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2263_ = lean_nat_dec_eq(v_next_2239_, v___x_2235_);
lean_dec(v___x_2235_);
v___x_2264_ = lean_box(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2248_);
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2240_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_apply_2(v_toPure_2231_, lean_box(0), v___x_2268_);
v___y_2256_ = v___x_2269_;
goto v___jp_2255_;
}
v___jp_2270_:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_nat_dec_lt(v___y_2274_, v___y_2275_);
if (v___x_2276_ == 0)
{
lean_dec(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___x_2238_);
goto v___jp_2262_;
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2277_ = lean_usize_of_nat(v___y_2274_);
lean_dec(v___y_2274_);
v___x_2278_ = lean_usize_of_nat(v___y_2275_);
lean_dec(v___y_2275_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2271_, v___y_2272_, v___y_2273_, v___x_2277_, v___x_2278_);
v___x_2280_ = lean_unbox(v___x_2279_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_dec_ref(v___x_2238_);
goto v___jp_2262_;
}
else
{
lean_dec(v___x_2248_);
lean_dec(v___x_2235_);
goto v___jp_2259_;
}
}
}
v___jp_2284_:
{
if (v___y_2285_ == 0)
{
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2248_);
lean_dec(v_next_2241_);
lean_dec(v___x_2235_);
lean_dec_ref(v_resOrders_2233_);
lean_dec(v___x_2230_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_array_2289_; lean_object* v_start_2290_; lean_object* v_stop_2291_; uint8_t v___x_2292_; 
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_nat_add(v_next_2241_, v___x_2286_);
lean_dec(v_next_2241_);
v___x_2288_ = l_Array_toSubarray___redArg(v_resOrders_2233_, v___x_2287_, v___x_2230_);
v_array_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_ref(v_array_2289_);
v_start_2290_ = lean_ctor_get(v___x_2288_, 1);
lean_inc(v_start_2290_);
v_stop_2291_ = lean_ctor_get(v___x_2288_, 2);
lean_inc(v_stop_2291_);
lean_dec_ref(v___x_2288_);
v___x_2292_ = lean_nat_dec_lt(v_start_2290_, v_stop_2291_);
if (v___x_2292_ == 0)
{
lean_dec(v_stop_2291_);
lean_dec(v_start_2290_);
lean_dec_ref(v_array_2289_);
lean_dec_ref(v___f_2283_);
lean_dec_ref(v___x_2238_);
goto v___jp_2262_;
}
else
{
lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2293_ = lean_box(v___y_2285_);
v___f_2294_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2294_, 0, v___f_2283_);
lean_closure_set(v___f_2294_, 1, v___x_2293_);
v___x_2295_ = lean_array_get_size(v_array_2289_);
v___x_2296_ = lean_nat_dec_le(v_stop_2291_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_dec(v_stop_2291_);
v___y_2271_ = v___x_2250_;
v___y_2272_ = v___f_2294_;
v___y_2273_ = v_array_2289_;
v___y_2274_ = v_start_2290_;
v___y_2275_ = v___x_2295_;
goto v___jp_2270_;
}
else
{
v___y_2271_ = v___x_2250_;
v___y_2272_ = v___f_2294_;
v___y_2273_ = v_array_2289_;
v___y_2274_ = v_start_2290_;
v___y_2275_ = v_stop_2291_;
goto v___jp_2270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2309_, lean_object* v_toPure_2310_, lean_object* v___x_2311_, lean_object* v_resOrders_2312_, lean_object* v___x_2313_, lean_object* v___x_2314_, lean_object* v_toBind_2315_, lean_object* v___f_2316_, lean_object* v___x_2317_, lean_object* v_next_2318_, lean_object* v___x_2319_, lean_object* v_next_2320_, lean_object* v_acc_2321_, lean_object* v_h_2322_, lean_object* v_G_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2309_, v_toPure_2310_, v___x_2311_, v_resOrders_2312_, v___x_2313_, v___x_2314_, v_toBind_2315_, v___f_2316_, v___x_2317_, v_next_2318_, v___x_2319_, v_next_2320_, v_acc_2321_, v_h_2322_, v_G_2323_);
lean_dec(v_next_2318_);
lean_dec(v___x_2313_);
lean_dec_ref(v___x_2311_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2325_, lean_object* v_toPure_2326_, lean_object* v___x_2327_, lean_object* v_resOrders_2328_, lean_object* v___x_2329_, lean_object* v___x_2330_, lean_object* v_toBind_2331_, lean_object* v___f_2332_, lean_object* v___x_2333_, lean_object* v___x_2334_, lean_object* v___f_2335_, lean_object* v___f_2336_, lean_object* v_next_2337_, lean_object* v_acc_2338_, lean_object* v_h_2339_, lean_object* v_G_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_lt(v_next_2337_, v___x_2325_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec(v_G_2340_);
lean_dec(v_next_2337_);
lean_dec(v___f_2336_);
lean_dec(v___f_2335_);
lean_dec_ref(v___x_2333_);
lean_dec(v___f_2332_);
lean_dec(v_toBind_2331_);
lean_dec(v___x_2330_);
lean_dec(v___x_2329_);
lean_dec_ref(v_resOrders_2328_);
lean_dec_ref(v___x_2327_);
v___x_2342_ = lean_apply_2(v_toPure_2326_, lean_box(0), v_acc_2338_);
return v___x_2342_;
}
else
{
lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec_ref(v_acc_2338_);
lean_inc(v_next_2337_);
lean_inc(v_toPure_2326_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2343_, 0, v_toPure_2326_);
lean_closure_set(v___f_2343_, 1, v_next_2337_);
lean_closure_set(v___f_2343_, 2, v_G_2340_);
v___x_2344_ = lean_nat_sub(v___x_2325_, v_next_2337_);
lean_inc_ref(v___x_2333_);
lean_inc_n(v_toBind_2331_, 3);
lean_inc(v___x_2330_);
v___f_2345_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2345_, 0, v___x_2344_);
lean_closure_set(v___f_2345_, 1, v_toPure_2326_);
lean_closure_set(v___f_2345_, 2, v___x_2327_);
lean_closure_set(v___f_2345_, 3, v_resOrders_2328_);
lean_closure_set(v___f_2345_, 4, v___x_2329_);
lean_closure_set(v___f_2345_, 5, v___x_2330_);
lean_closure_set(v___f_2345_, 6, v_toBind_2331_);
lean_closure_set(v___f_2345_, 7, v___f_2332_);
lean_closure_set(v___f_2345_, 8, v___x_2333_);
lean_closure_set(v___f_2345_, 9, v_next_2337_);
lean_closure_set(v___f_2345_, 10, v___x_2334_);
v___x_2346_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2345_, v___x_2330_, v___x_2333_, lean_box(0));
v___x_2347_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2346_, v___f_2335_);
v___x_2348_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2347_, v___f_2336_);
v___x_2349_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v___x_2348_, v___f_2343_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2350_, lean_object* v_toPure_2351_, lean_object* v___x_2352_, lean_object* v_resOrders_2353_, lean_object* v___x_2354_, lean_object* v___x_2355_, lean_object* v_toBind_2356_, lean_object* v___f_2357_, lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v___f_2360_, lean_object* v___f_2361_, lean_object* v_next_2362_, lean_object* v_acc_2363_, lean_object* v_h_2364_, lean_object* v_G_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2350_, v_toPure_2351_, v___x_2352_, v_resOrders_2353_, v___x_2354_, v___x_2355_, v_toBind_2356_, v___f_2357_, v___x_2358_, v___x_2359_, v___f_2360_, v___f_2361_, v_next_2362_, v_acc_2363_, v_h_2364_, v_G_2365_);
lean_dec(v___x_2350_);
return v_res_2366_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Array_instInhabited(lean_box(0));
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2371_, lean_object* v_resOrders_2372_){
_start:
{
lean_object* v_toApplicative_2373_; lean_object* v_toBind_2374_; lean_object* v_toPure_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_toApplicative_2373_ = lean_ctor_get(v_inst_2371_, 0);
lean_inc_ref(v_toApplicative_2373_);
v_toBind_2374_ = lean_ctor_get(v_inst_2371_, 1);
lean_inc_n(v_toBind_2374_, 2);
lean_dec_ref(v_inst_2371_);
v_toPure_2375_ = lean_ctor_get(v_toApplicative_2373_, 1);
lean_inc_n(v_toPure_2375_, 4);
lean_dec_ref(v_toApplicative_2373_);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2378_ = lean_array_get_size(v_resOrders_2372_);
lean_inc_ref(v_resOrders_2372_);
v___f_2379_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2379_, 0, v___x_2377_);
lean_closure_set(v___f_2379_, 1, v_resOrders_2372_);
lean_closure_set(v___f_2379_, 2, v___x_2376_);
lean_closure_set(v___f_2379_, 3, v_toPure_2375_);
v___f_2380_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2380_, 0, v_toPure_2375_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = lean_box(0);
v___x_2383_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2384_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2384_, 0, v___x_2383_);
lean_closure_set(v___f_2384_, 1, v_toPure_2375_);
lean_closure_set(v___f_2384_, 2, v___x_2382_);
lean_inc_ref(v___f_2380_);
v___f_2385_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2385_, 0, v___x_2378_);
lean_closure_set(v___f_2385_, 1, v_toPure_2375_);
lean_closure_set(v___f_2385_, 2, v___x_2377_);
lean_closure_set(v___f_2385_, 3, v_resOrders_2372_);
lean_closure_set(v___f_2385_, 4, v___x_2376_);
lean_closure_set(v___f_2385_, 5, v___x_2381_);
lean_closure_set(v___f_2385_, 6, v_toBind_2374_);
lean_closure_set(v___f_2385_, 7, v___f_2380_);
lean_closure_set(v___f_2385_, 8, v___x_2383_);
lean_closure_set(v___f_2385_, 9, v___x_2382_);
lean_closure_set(v___f_2385_, 10, v___f_2384_);
lean_closure_set(v___f_2385_, 11, v___f_2380_);
v___x_2386_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2385_, v___x_2381_, v___x_2383_, lean_box(0));
v___x_2387_ = lean_apply_4(v_toBind_2374_, lean_box(0), lean_box(0), v___x_2386_, v___f_2379_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2388_, lean_object* v_inst_2389_, lean_object* v_resOrders_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2389_, v_resOrders_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2392_){
_start:
{
lean_object* v_structName_2393_; 
v_structName_2393_ = lean_ctor_get(v_x_2392_, 0);
lean_inc(v_structName_2393_);
return v_structName_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2394_);
lean_dec_ref(v_x_2394_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2396_, lean_object* v_result_2397_, lean_object* v_____r_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_apply_2(v_toPure_2396_, lean_box(0), v_result_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2400_, lean_object* v_inst_2401_, lean_object* v_structName_2402_, lean_object* v_toBind_2403_, lean_object* v_result_2404_){
_start:
{
lean_object* v_resolutionOrder_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_resolutionOrder_2405_ = lean_ctor_get(v_result_2404_, 0);
lean_inc_ref(v_resolutionOrder_2405_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2406_, 0, v_toPure_2400_);
lean_closure_set(v___f_2406_, 1, v_result_2404_);
v___x_2407_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2401_, v_structName_2402_, v_resolutionOrder_2405_);
v___x_2408_ = lean_apply_4(v_toBind_2403_, lean_box(0), lean_box(0), v___x_2407_, v___f_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2409_, lean_object* v_____s_2410_){
_start:
{
lean_object* v_snd_2411_; lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2421_; 
v_snd_2411_ = lean_ctor_get(v_____s_2410_, 1);
lean_inc(v_snd_2411_);
lean_dec_ref(v_____s_2410_);
v_fst_2412_ = lean_ctor_get(v_snd_2411_, 0);
v_snd_2413_ = lean_ctor_get(v_snd_2411_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_snd_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2415_ = v_snd_2411_;
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_snd_2413_);
lean_inc(v_fst_2412_);
lean_dec(v_snd_2411_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fst_2412_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_snd_2413_);
v___x_2418_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_apply_2(v_toPure_2409_, lean_box(0), v___x_2418_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2422_, lean_object* v_parentNames_2423_, lean_object* v_x_2424_){
_start:
{
uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_inc(v_x_2424_);
v___x_2425_ = l_Array_contains___redArg(v___x_2422_, v_parentNames_2423_, v_x_2424_);
v___x_2426_ = lean_box(v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_x_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2428_, lean_object* v___f_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2431_ = lean_array_get_size(v_x_2430_);
v___x_2432_ = lean_mk_empty_array_with_capacity(v___x_2428_);
v___x_2433_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2434_ = lean_nat_dec_lt(v___x_2428_, v___x_2431_);
if (v___x_2434_ == 0)
{
lean_dec_ref(v_x_2430_);
lean_dec_ref(v___f_2429_);
return v___x_2432_;
}
else
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_nat_dec_le(v___x_2431_, v___x_2431_);
if (v___x_2435_ == 0)
{
if (v___x_2434_ == 0)
{
lean_dec_ref(v_x_2430_);
lean_dec_ref(v___f_2429_);
return v___x_2432_;
}
else
{
size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = lean_usize_of_nat(v___x_2431_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2433_, v___f_2429_, v_x_2430_, v___x_2436_, v___x_2437_, v___x_2432_);
return v___x_2438_;
}
}
else
{
size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = lean_usize_of_nat(v___x_2431_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2433_, v___f_2429_, v_x_2430_, v___x_2439_, v___x_2440_, v___x_2432_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v___x_2442_, lean_object* v___f_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v___x_2442_, v___f_2443_, v_x_2444_);
lean_dec(v___x_2442_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v_snd_2446_, lean_object* v_x1_2447_, lean_object* v_x2_2448_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_name_eq(v_x2_2448_, v_snd_2446_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_array_push(v_x1_2447_, v_x2_2448_);
return v___x_2450_;
}
else
{
lean_dec(v_x2_2448_);
return v_x1_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v_snd_2451_, lean_object* v_x1_2452_, lean_object* v_x2_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v_snd_2451_, v_x1_2452_, v_x2_2453_);
lean_dec(v_snd_2451_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2455_, lean_object* v___f_2456_, lean_object* v_x1_2457_, lean_object* v_x2_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_array_2462_; lean_object* v_start_2463_; lean_object* v_stop_2464_; lean_object* v___y_2466_; uint8_t v___x_2473_; 
v___x_2459_ = lean_array_get_size(v_x2_2458_);
lean_inc_ref(v_x2_2458_);
v___x_2460_ = l_Array_toSubarray___redArg(v_x2_2458_, v___x_2455_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2462_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_ref(v_array_2462_);
v_start_2463_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_start_2463_);
v_stop_2464_ = lean_ctor_get(v___x_2460_, 2);
lean_inc(v_stop_2464_);
lean_dec_ref(v___x_2460_);
v___x_2473_ = lean_nat_dec_lt(v_start_2463_, v_stop_2464_);
if (v___x_2473_ == 0)
{
lean_dec(v_stop_2464_);
lean_dec(v_start_2463_);
lean_dec_ref(v_array_2462_);
lean_dec_ref(v_x2_2458_);
lean_dec_ref(v___f_2456_);
return v_x1_2457_;
}
else
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = lean_array_get_size(v_array_2462_);
v___x_2475_ = lean_nat_dec_le(v_stop_2464_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_dec(v_stop_2464_);
v___y_2466_ = v___x_2474_;
goto v___jp_2465_;
}
else
{
v___y_2466_ = v_stop_2464_;
goto v___jp_2465_;
}
}
v___jp_2465_:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_nat_dec_lt(v_start_2463_, v___y_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v___y_2466_);
lean_dec(v_start_2463_);
lean_dec_ref(v_array_2462_);
lean_dec_ref(v_x2_2458_);
lean_dec_ref(v___f_2456_);
return v_x1_2457_;
}
else
{
size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2468_ = lean_usize_of_nat(v_start_2463_);
lean_dec(v_start_2463_);
v___x_2469_ = lean_usize_of_nat(v___y_2466_);
lean_dec(v___y_2466_);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2461_, v___f_2456_, v_array_2462_, v___x_2468_, v___x_2469_);
v___x_2471_ = lean_unbox(v___x_2470_);
lean_dec(v___x_2470_);
if (v___x_2471_ == 0)
{
lean_dec_ref(v_x2_2458_);
return v_x1_2457_;
}
else
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_array_push(v_x1_2457_, v_x2_2458_);
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2476_, lean_object* v_x_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_name_eq(v_x_2477_, v_snd_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2479_, lean_object* v_x_2480_){
_start:
{
uint8_t v_res_2481_; lean_object* v_r_2482_; 
v_res_2481_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2479_, v_x_2480_);
lean_dec(v_x_2480_);
lean_dec(v_snd_2479_);
v_r_2482_ = lean_box(v_res_2481_);
return v_r_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2484_, lean_object* v___x_2485_, lean_object* v_fst_2486_, lean_object* v_fst_2487_, lean_object* v___f_2488_, uint8_t v_relaxed_2489_, lean_object* v_parentNames_2490_, lean_object* v_snd_2491_, lean_object* v___f_2492_, lean_object* v___x_2493_, lean_object* v_____x_2494_){
_start:
{
lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v_defects_2508_; uint8_t v___x_2522_; 
v_fst_2503_ = lean_ctor_get(v_____x_2494_, 0);
lean_inc(v_fst_2503_);
v_snd_2504_ = lean_ctor_get(v_____x_2494_, 1);
lean_inc_n(v_snd_2504_, 2);
lean_dec_ref(v_____x_2494_);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2505_, 0, v_snd_2504_);
lean_inc(v___x_2485_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2506_, 0, v___x_2485_);
lean_closure_set(v___f_2506_, 1, v___f_2505_);
v___x_2522_ = lean_unbox(v_fst_2503_);
lean_dec(v_fst_2503_);
if (v___x_2522_ == 0)
{
if (v_relaxed_2489_ == 0)
{
lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___y_2526_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2550_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2523_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2490_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9), 3, 2);
lean_closure_set(v___f_2524_, 0, v___x_2523_);
lean_closure_set(v___f_2524_, 1, v_parentNames_2490_);
v___x_2560_ = lean_array_get_size(v_fst_2487_);
v___x_2561_ = lean_mk_empty_array_with_capacity(v___x_2485_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2563_ = lean_nat_dec_lt(v___x_2485_, v___x_2560_);
if (v___x_2563_ == 0)
{
v___y_2550_ = v___x_2561_;
goto v___jp_2549_;
}
else
{
lean_object* v___f_2564_; lean_object* v___f_2565_; uint8_t v___x_2566_; 
lean_inc(v_snd_2504_);
v___f_2564_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2564_, 0, v_snd_2504_);
lean_inc(v___x_2493_);
v___f_2565_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2565_, 0, v___x_2493_);
lean_closure_set(v___f_2565_, 1, v___f_2564_);
v___x_2566_ = lean_nat_dec_le(v___x_2560_, v___x_2560_);
if (v___x_2566_ == 0)
{
if (v___x_2563_ == 0)
{
lean_dec_ref(v___f_2565_);
v___y_2550_ = v___x_2561_;
goto v___jp_2549_;
}
else
{
size_t v___x_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = lean_usize_of_nat(v___x_2560_);
lean_inc(v_fst_2487_);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2562_, v___f_2565_, v_fst_2487_, v___x_2567_, v___x_2568_, v___x_2561_);
v___y_2550_ = v___x_2569_;
goto v___jp_2549_;
}
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = lean_usize_of_nat(v___x_2560_);
lean_inc(v_fst_2487_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2562_, v___f_2565_, v_fst_2487_, v___x_2570_, v___x_2571_, v___x_2561_);
v___y_2550_ = v___x_2572_;
goto v___jp_2549_;
}
}
v___jp_2525_:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; size_t v_sz_2530_; size_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2527_ = l_Array_eraseReps___redArg(v___x_2523_, v___y_2526_);
lean_inc_n(v_snd_2504_, 2);
v___x_2528_ = l_Array_contains___redArg(v___x_2523_, v_parentNames_2490_, v_snd_2504_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2530_ = lean_array_size(v___x_2527_);
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2529_, v___f_2524_, v_sz_2530_, v___x_2531_, v___x_2527_);
v___x_2533_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2533_, 0, v_snd_2504_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*2, v___x_2528_);
v___x_2534_ = lean_array_push(v_snd_2491_, v___x_2533_);
v_defects_2508_ = v___x_2534_;
goto v___jp_2507_;
}
v___jp_2535_:
{
lean_object* v___x_2541_; 
lean_inc_ref(v___y_2537_);
v___x_2541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2537_, v___y_2536_, v___y_2538_, v___y_2539_, v___y_2540_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2540_);
lean_dec(v___y_2536_);
v___y_2526_ = v___x_2541_;
goto v___jp_2525_;
}
v___jp_2542_:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_le(v___y_2547_, v___y_2544_);
if (v___x_2548_ == 0)
{
lean_dec(v___y_2544_);
lean_inc(v___y_2547_);
v___y_2536_ = v___y_2543_;
v___y_2537_ = v___y_2545_;
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___y_2547_;
v___y_2540_ = v___y_2547_;
goto v___jp_2535_;
}
else
{
v___y_2536_ = v___y_2543_;
v___y_2537_ = v___y_2545_;
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___y_2547_;
v___y_2540_ = v___y_2544_;
goto v___jp_2535_;
}
}
v___jp_2549_:
{
lean_object* v___x_2551_; size_t v_sz_2552_; size_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2552_ = lean_array_size(v___y_2550_);
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2551_, v___f_2492_, v_sz_2552_, v___x_2553_, v___y_2550_);
v___x_2555_ = lean_array_get_size(v___x_2554_);
v___x_2556_ = lean_nat_dec_eq(v___x_2555_, v___x_2485_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2558_ = lean_nat_sub(v___x_2555_, v___x_2493_);
lean_dec(v___x_2493_);
v___x_2559_ = lean_nat_dec_le(v___x_2485_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_inc(v___x_2558_);
v___y_2543_ = v___x_2555_;
v___y_2544_ = v___x_2558_;
v___y_2545_ = v___x_2557_;
v___y_2546_ = v___x_2554_;
v___y_2547_ = v___x_2558_;
goto v___jp_2542_;
}
else
{
lean_inc(v___x_2485_);
v___y_2543_ = v___x_2555_;
v___y_2544_ = v___x_2558_;
v___y_2545_ = v___x_2557_;
v___y_2546_ = v___x_2554_;
v___y_2547_ = v___x_2485_;
goto v___jp_2542_;
}
}
else
{
lean_dec(v___x_2493_);
v___y_2526_ = v___x_2554_;
goto v___jp_2525_;
}
}
}
else
{
lean_dec(v___x_2493_);
lean_dec_ref(v___f_2492_);
lean_dec_ref(v_parentNames_2490_);
v_defects_2508_ = v_snd_2491_;
goto v___jp_2507_;
}
}
else
{
lean_dec(v___x_2493_);
lean_dec_ref(v___f_2492_);
lean_dec_ref(v_parentNames_2490_);
v_defects_2508_ = v_snd_2491_;
goto v___jp_2507_;
}
v___jp_2495_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2496_);
lean_ctor_set(v___x_2499_, 1, v___y_2497_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___y_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
v___x_2502_ = lean_apply_2(v_toPure_2484_, lean_box(0), v___x_2501_);
return v___x_2502_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2509_ = lean_array_push(v_fst_2486_, v_snd_2504_);
v___x_2510_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2511_ = lean_array_size(v_fst_2487_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2510_, v___f_2506_, v_sz_2511_, v___x_2512_, v_fst_2487_);
v___x_2514_ = lean_array_get_size(v___x_2513_);
v___x_2515_ = lean_mk_empty_array_with_capacity(v___x_2485_);
v___x_2516_ = lean_nat_dec_lt(v___x_2485_, v___x_2514_);
lean_dec(v___x_2485_);
if (v___x_2516_ == 0)
{
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2488_);
v___y_2496_ = v___x_2509_;
v___y_2497_ = v_defects_2508_;
v___y_2498_ = v___x_2515_;
goto v___jp_2495_;
}
else
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_le(v___x_2514_, v___x_2514_);
if (v___x_2517_ == 0)
{
if (v___x_2516_ == 0)
{
lean_dec(v___x_2513_);
lean_dec_ref(v___f_2488_);
v___y_2496_ = v___x_2509_;
v___y_2497_ = v_defects_2508_;
v___y_2498_ = v___x_2515_;
goto v___jp_2495_;
}
else
{
size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_usize_of_nat(v___x_2514_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2510_, v___f_2488_, v___x_2513_, v___x_2512_, v___x_2518_, v___x_2515_);
v___y_2496_ = v___x_2509_;
v___y_2497_ = v_defects_2508_;
v___y_2498_ = v___x_2519_;
goto v___jp_2495_;
}
}
else
{
size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_usize_of_nat(v___x_2514_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2510_, v___f_2488_, v___x_2513_, v___x_2512_, v___x_2520_, v___x_2515_);
v___y_2496_ = v___x_2509_;
v___y_2497_ = v_defects_2508_;
v___y_2498_ = v___x_2521_;
goto v___jp_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2573_, lean_object* v___x_2574_, lean_object* v_fst_2575_, lean_object* v_fst_2576_, lean_object* v___f_2577_, lean_object* v_relaxed_2578_, lean_object* v_parentNames_2579_, lean_object* v_snd_2580_, lean_object* v___f_2581_, lean_object* v___x_2582_, lean_object* v_____x_2583_){
_start:
{
uint8_t v_relaxed_boxed_2584_; lean_object* v_res_2585_; 
v_relaxed_boxed_2584_ = lean_unbox(v_relaxed_2578_);
v_res_2585_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2573_, v___x_2574_, v_fst_2575_, v_fst_2576_, v___f_2577_, v_relaxed_boxed_2584_, v_parentNames_2579_, v_snd_2580_, v___f_2581_, v___x_2582_, v_____x_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2586_, lean_object* v_toPure_2587_, lean_object* v___f_2588_, uint8_t v_relaxed_2589_, lean_object* v_parentNames_2590_, lean_object* v___f_2591_, lean_object* v___x_2592_, lean_object* v_inst_2593_, lean_object* v_toBind_2594_, lean_object* v___f_2595_, lean_object* v_b_2596_){
_start:
{
lean_object* v_snd_2597_; lean_object* v_fst_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2624_; 
v_snd_2597_ = lean_ctor_get(v_b_2596_, 1);
v_fst_2598_ = lean_ctor_get(v_b_2596_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_b_2596_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2600_ = v_b_2596_;
v_isShared_2601_ = v_isSharedCheck_2624_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2597_);
lean_inc(v_fst_2598_);
lean_dec(v_b_2596_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2624_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_fst_2602_; lean_object* v_snd_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2623_; 
v_fst_2602_ = lean_ctor_get(v_snd_2597_, 0);
v_snd_2603_ = lean_ctor_get(v_snd_2597_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_snd_2597_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2605_ = v_snd_2597_;
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_snd_2603_);
lean_inc(v_fst_2602_);
lean_dec(v_snd_2597_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2623_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = lean_array_get_size(v_fst_2598_);
v___x_2608_ = lean_nat_dec_eq(v___x_2607_, v___x_2586_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_del_object(v___x_2605_);
lean_del_object(v___x_2600_);
v___x_2609_ = lean_box(v_relaxed_2589_);
lean_inc(v_fst_2598_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_2610_, 0, v_toPure_2587_);
lean_closure_set(v___f_2610_, 1, v___x_2586_);
lean_closure_set(v___f_2610_, 2, v_fst_2602_);
lean_closure_set(v___f_2610_, 3, v_fst_2598_);
lean_closure_set(v___f_2610_, 4, v___f_2588_);
lean_closure_set(v___f_2610_, 5, v___x_2609_);
lean_closure_set(v___f_2610_, 6, v_parentNames_2590_);
lean_closure_set(v___f_2610_, 7, v_snd_2603_);
lean_closure_set(v___f_2610_, 8, v___f_2591_);
lean_closure_set(v___f_2610_, 9, v___x_2592_);
v___x_2611_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2593_, v_fst_2598_);
lean_inc(v_toBind_2594_);
v___x_2612_ = lean_apply_4(v_toBind_2594_, lean_box(0), lean_box(0), v___x_2611_, v___f_2610_);
v___x_2613_ = lean_apply_4(v_toBind_2594_, lean_box(0), lean_box(0), v___x_2612_, v___f_2595_);
return v___x_2613_;
}
else
{
lean_object* v___x_2615_; 
lean_dec_ref(v_inst_2593_);
lean_dec(v___x_2592_);
lean_dec_ref(v___f_2591_);
lean_dec_ref(v_parentNames_2590_);
lean_dec_ref(v___f_2588_);
lean_dec(v___x_2586_);
if (v_isShared_2606_ == 0)
{
v___x_2615_ = v___x_2605_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_fst_2602_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_snd_2603_);
v___x_2615_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___x_2615_);
v___x_2617_ = v___x_2600_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_fst_2598_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = lean_apply_2(v_toPure_2587_, lean_box(0), v___x_2618_);
v___x_2620_ = lean_apply_4(v_toBind_2594_, lean_box(0), lean_box(0), v___x_2619_, v___f_2595_);
return v___x_2620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2625_, lean_object* v_toPure_2626_, lean_object* v___f_2627_, lean_object* v_relaxed_2628_, lean_object* v_parentNames_2629_, lean_object* v___f_2630_, lean_object* v___x_2631_, lean_object* v_inst_2632_, lean_object* v_toBind_2633_, lean_object* v___f_2634_, lean_object* v_b_2635_){
_start:
{
uint8_t v_relaxed_boxed_2636_; lean_object* v_res_2637_; 
v_relaxed_boxed_2636_ = lean_unbox(v_relaxed_2628_);
v_res_2637_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2625_, v_toPure_2626_, v___f_2627_, v_relaxed_boxed_2636_, v_parentNames_2629_, v___f_2630_, v___x_2631_, v_inst_2632_, v_toBind_2633_, v___f_2634_, v_b_2635_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v___x_2638_, lean_object* v_x_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_array_get_borrowed(v___x_2640_, v_x_2639_, v___x_2638_);
lean_inc(v___x_2641_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v___x_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v___x_2642_, v_x_2643_);
lean_dec_ref(v_x_2643_);
lean_dec(v___x_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v_toPure_2649_, lean_object* v___f_2650_, uint8_t v_relaxed_2651_, lean_object* v_parentNames_2652_, lean_object* v_inst_2653_, lean_object* v_toBind_2654_, lean_object* v___f_2655_, lean_object* v_structName_2656_, lean_object* v___f_2657_, lean_object* v___f_2658_, lean_object* v_parentResOrders_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___y_2663_; lean_object* v_j_2674_; lean_object* v_as_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___f_2661_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v_j_2674_ = lean_array_get_size(v_parentResOrders_2659_);
lean_inc_ref(v_parentNames_2652_);
v_as_2675_ = lean_array_push(v_parentResOrders_2659_, v_parentNames_2652_);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2660_, v_as_2675_, v_j_2674_);
v___x_2677_ = lean_array_get_size(v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__1));
v___x_2679_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2680_ = lean_nat_dec_lt(v___x_2660_, v___x_2677_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v___x_2676_);
lean_dec_ref(v___f_2658_);
v___y_2663_ = v___x_2678_;
goto v___jp_2662_;
}
else
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_nat_dec_le(v___x_2677_, v___x_2677_);
if (v___x_2681_ == 0)
{
if (v___x_2680_ == 0)
{
lean_dec_ref(v___x_2676_);
lean_dec_ref(v___f_2658_);
v___y_2663_ = v___x_2678_;
goto v___jp_2662_;
}
else
{
size_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = lean_usize_of_nat(v___x_2677_);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2679_, v___f_2658_, v___x_2676_, v___x_2682_, v___x_2683_, v___x_2678_);
v___y_2663_ = v___x_2684_;
goto v___jp_2662_;
}
}
else
{
size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = ((size_t)0ULL);
v___x_2686_ = lean_usize_of_nat(v___x_2677_);
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2679_, v___f_2658_, v___x_2676_, v___x_2685_, v___x_2686_, v___x_2678_);
v___y_2663_ = v___x_2687_;
goto v___jp_2662_;
}
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v_resOrder_2668_; lean_object* v_defects_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_box(v_relaxed_2651_);
lean_inc(v_toBind_2654_);
lean_inc_ref(v_inst_2653_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 11, 10);
lean_closure_set(v___f_2666_, 0, v___x_2660_);
lean_closure_set(v___f_2666_, 1, v_toPure_2649_);
lean_closure_set(v___f_2666_, 2, v___f_2650_);
lean_closure_set(v___f_2666_, 3, v___x_2665_);
lean_closure_set(v___f_2666_, 4, v_parentNames_2652_);
lean_closure_set(v___f_2666_, 5, v___f_2661_);
lean_closure_set(v___f_2666_, 6, v___x_2664_);
lean_closure_set(v___f_2666_, 7, v_inst_2653_);
lean_closure_set(v___f_2666_, 8, v_toBind_2654_);
lean_closure_set(v___f_2666_, 9, v___f_2655_);
v___x_2667_ = lean_mk_empty_array_with_capacity(v___x_2664_);
v_resOrder_2668_ = lean_array_push(v___x_2667_, v_structName_2656_);
v_defects_2669_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_resOrder_2668_);
lean_ctor_set(v___x_2670_, 1, v_defects_2669_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2663_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2653_, v___f_2666_, v___x_2671_);
v___x_2673_ = lean_apply_4(v_toBind_2654_, lean_box(0), lean_box(0), v___x_2672_, v___f_2657_);
return v___x_2673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v_toPure_2688_, lean_object* v___f_2689_, lean_object* v_relaxed_2690_, lean_object* v_parentNames_2691_, lean_object* v_inst_2692_, lean_object* v_toBind_2693_, lean_object* v___f_2694_, lean_object* v_structName_2695_, lean_object* v___f_2696_, lean_object* v___f_2697_, lean_object* v_parentResOrders_2698_){
_start:
{
uint8_t v_relaxed_boxed_2699_; lean_object* v_res_2700_; 
v_relaxed_boxed_2699_ = lean_unbox(v_relaxed_2690_);
v_res_2700_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v_toPure_2688_, v___f_2689_, v_relaxed_boxed_2699_, v_parentNames_2691_, v_inst_2692_, v_toBind_2693_, v___f_2694_, v_structName_2695_, v___f_2696_, v___f_2697_, v_parentResOrders_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2701_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2702_ = lean_array_get_size(v_x_2701_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_nat_dec_eq(v___x_2702_, v___x_2703_);
if (v___x_2704_ == 0)
{
uint8_t v___x_2705_; 
v___x_2705_ = 1;
return v___x_2705_;
}
else
{
uint8_t v___x_2706_; 
v___x_2706_ = 0;
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2707_){
_start:
{
uint8_t v_res_2708_; lean_object* v_r_2709_; 
v_res_2708_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2707_);
lean_dec_ref(v_x_2707_);
v_r_2709_ = lean_box(v_res_2708_);
return v_r_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2710_, lean_object* v_x1_2711_, lean_object* v_x2_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
lean_inc_ref(v_x2_2712_);
v___x_2713_ = lean_apply_1(v___f_2710_, v_x2_2712_);
v___x_2714_ = lean_unbox(v___x_2713_);
if (v___x_2714_ == 0)
{
lean_dec_ref(v_x2_2712_);
return v_x1_2711_;
}
else
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_array_push(v_x1_2711_, v_x2_2712_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2716_, lean_object* v_____do__lift_2717_){
_start:
{
if (lean_obj_tag(v_____do__lift_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2726_; 
v_a_2718_ = lean_ctor_get(v_____do__lift_2717_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_____do__lift_2717_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2720_ = v_____do__lift_2717_;
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v_____do__lift_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 1);
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_apply_2(v_toPure_2716_, lean_box(0), v___x_2723_);
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2735_; 
v_a_2727_ = lean_ctor_get(v_____do__lift_2717_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_____do__lift_2717_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2729_ = v_____do__lift_2717_;
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v_____do__lift_2717_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 0);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_apply_2(v_toPure_2716_, lean_box(0), v___x_2732_);
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2736_, lean_object* v_____do__lift_2737_){
_start:
{
lean_object* v_resolutionOrder_2738_; lean_object* v___x_2739_; 
v_resolutionOrder_2738_ = lean_ctor_get(v_____do__lift_2737_, 0);
lean_inc_ref(v_resolutionOrder_2738_);
lean_dec_ref(v_____do__lift_2737_);
v___x_2739_ = lean_apply_2(v_toPure_2736_, lean_box(0), v_resolutionOrder_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_structName_2746_, lean_object* v_parentNames_2747_, uint8_t v_relaxed_2748_){
_start:
{
lean_object* v_toApplicative_2749_; lean_object* v_toBind_2750_; lean_object* v_toPure_2751_; lean_object* v___f_2752_; lean_object* v___f_2753_; lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v___f_2758_; size_t v_sz_2759_; size_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_toApplicative_2749_ = lean_ctor_get(v_inst_2744_, 0);
v_toBind_2750_ = lean_ctor_get(v_inst_2744_, 1);
lean_inc_n(v_toBind_2750_, 3);
v_toPure_2751_ = lean_ctor_get(v_toApplicative_2749_, 1);
v___f_2752_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc_n(v_toPure_2751_, 4);
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2753_, 0, v_toPure_2751_);
lean_inc_ref_n(v_inst_2744_, 2);
v___f_2754_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2754_, 0, v_inst_2744_);
lean_closure_set(v___f_2754_, 1, v_inst_2745_);
lean_closure_set(v___f_2754_, 2, v_toBind_2750_);
lean_closure_set(v___f_2754_, 3, v___f_2753_);
v___f_2755_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2755_, 0, v_toPure_2751_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2756_, 0, v_toPure_2751_);
v___x_2757_ = lean_box(v_relaxed_2748_);
lean_inc_ref(v_parentNames_2747_);
v___f_2758_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 11, 10);
lean_closure_set(v___f_2758_, 0, v_toPure_2751_);
lean_closure_set(v___f_2758_, 1, v___f_2752_);
lean_closure_set(v___f_2758_, 2, v___x_2757_);
lean_closure_set(v___f_2758_, 3, v_parentNames_2747_);
lean_closure_set(v___f_2758_, 4, v_inst_2744_);
lean_closure_set(v___f_2758_, 5, v_toBind_2750_);
lean_closure_set(v___f_2758_, 6, v___f_2755_);
lean_closure_set(v___f_2758_, 7, v_structName_2746_);
lean_closure_set(v___f_2758_, 8, v___f_2756_);
lean_closure_set(v___f_2758_, 9, v___f_2752_);
v_sz_2759_ = lean_array_size(v_parentNames_2747_);
v___x_2760_ = ((size_t)0ULL);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2744_, v___f_2754_, v_sz_2759_, v___x_2760_, v_parentNames_2747_);
v___x_2762_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2761_, v___f_2758_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2763_, lean_object* v_toPure_2764_, lean_object* v___f_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, uint8_t v_relaxed_2768_, lean_object* v_toBind_2769_, lean_object* v___f_2770_, lean_object* v_env_2771_){
_start:
{
lean_object* v___x_2772_; 
lean_inc_ref(v_env_2771_);
v___x_2772_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2771_, v_structName_2763_);
if (lean_obj_tag(v___x_2772_) == 1)
{
lean_object* v_val_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v_env_2771_);
lean_dec(v___f_2770_);
lean_dec(v_toBind_2769_);
lean_dec_ref(v_inst_2767_);
lean_dec_ref(v_inst_2766_);
lean_dec_ref(v___f_2765_);
lean_dec(v_structName_2763_);
v_val_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_val_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_apply_2(v_toPure_2764_, lean_box(0), v___x_2775_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; size_t v_sz_2779_; size_t v___x_2780_; lean_object* v_parentNames_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v___x_2772_);
lean_dec(v_toPure_2764_);
lean_inc(v_structName_2763_);
v___x_2777_ = l_Lean_getStructureParentInfo(v_env_2771_, v_structName_2763_);
v___x_2778_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2779_ = lean_array_size(v___x_2777_);
v___x_2780_ = ((size_t)0ULL);
v_parentNames_2781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2778_, v___f_2765_, v_sz_2779_, v___x_2780_, v___x_2777_);
v___x_2782_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2766_, v_inst_2767_, v_structName_2763_, v_parentNames_2781_, v_relaxed_2768_);
v___x_2783_ = lean_apply_4(v_toBind_2769_, lean_box(0), lean_box(0), v___x_2782_, v___f_2770_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2784_, lean_object* v_toPure_2785_, lean_object* v___f_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_relaxed_2789_, lean_object* v_toBind_2790_, lean_object* v___f_2791_, lean_object* v_env_2792_){
_start:
{
uint8_t v_relaxed_boxed_2793_; lean_object* v_res_2794_; 
v_relaxed_boxed_2793_ = lean_unbox(v_relaxed_2789_);
v_res_2794_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2784_, v_toPure_2785_, v___f_2786_, v_inst_2787_, v_inst_2788_, v_relaxed_boxed_2793_, v_toBind_2790_, v___f_2791_, v_env_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2795_, lean_object* v_inst_2796_, lean_object* v_structName_2797_, uint8_t v_relaxed_2798_){
_start:
{
lean_object* v_toApplicative_2799_; lean_object* v_toBind_2800_; lean_object* v_getEnv_2801_; lean_object* v_toPure_2802_; lean_object* v___f_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___f_2806_; lean_object* v___x_2807_; 
v_toApplicative_2799_ = lean_ctor_get(v_inst_2795_, 0);
v_toBind_2800_ = lean_ctor_get(v_inst_2795_, 1);
lean_inc_n(v_toBind_2800_, 3);
v_getEnv_2801_ = lean_ctor_get(v_inst_2796_, 0);
lean_inc(v_getEnv_2801_);
v_toPure_2802_ = lean_ctor_get(v_toApplicative_2799_, 1);
lean_inc_n(v_toPure_2802_, 2);
v___f_2803_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2797_);
lean_inc_ref(v_inst_2796_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2804_, 0, v_toPure_2802_);
lean_closure_set(v___f_2804_, 1, v_inst_2796_);
lean_closure_set(v___f_2804_, 2, v_structName_2797_);
lean_closure_set(v___f_2804_, 3, v_toBind_2800_);
v___x_2805_ = lean_box(v_relaxed_2798_);
v___f_2806_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2806_, 0, v_structName_2797_);
lean_closure_set(v___f_2806_, 1, v_toPure_2802_);
lean_closure_set(v___f_2806_, 2, v___f_2803_);
lean_closure_set(v___f_2806_, 3, v_inst_2795_);
lean_closure_set(v___f_2806_, 4, v_inst_2796_);
lean_closure_set(v___f_2806_, 5, v___x_2805_);
lean_closure_set(v___f_2806_, 6, v_toBind_2800_);
lean_closure_set(v___f_2806_, 7, v___f_2804_);
v___x_2807_ = lean_apply_4(v_toBind_2800_, lean_box(0), lean_box(0), v_getEnv_2801_, v___f_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_toBind_2810_, lean_object* v___f_2811_, lean_object* v_parentName_2812_){
_start:
{
uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = 1;
v___x_2814_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2808_, v_inst_2809_, v_parentName_2812_, v___x_2813_);
v___x_2815_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2814_, v___f_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_structName_2818_, lean_object* v_relaxed_2819_){
_start:
{
uint8_t v_relaxed_boxed_2820_; lean_object* v_res_2821_; 
v_relaxed_boxed_2820_ = lean_unbox(v_relaxed_2819_);
v_res_2821_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2816_, v_inst_2817_, v_structName_2818_, v_relaxed_boxed_2820_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_structName_2824_, lean_object* v_parentNames_2825_, lean_object* v_relaxed_2826_){
_start:
{
uint8_t v_relaxed_boxed_2827_; lean_object* v_res_2828_; 
v_relaxed_boxed_2827_ = lean_unbox(v_relaxed_2826_);
v_res_2828_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2822_, v_inst_2823_, v_structName_2824_, v_parentNames_2825_, v_relaxed_boxed_2827_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_structName_2832_, uint8_t v_relaxed_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2830_, v_inst_2831_, v_structName_2832_, v_relaxed_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_structName_2838_, lean_object* v_relaxed_2839_){
_start:
{
uint8_t v_relaxed_boxed_2840_; lean_object* v_res_2841_; 
v_relaxed_boxed_2840_ = lean_unbox(v_relaxed_2839_);
v_res_2841_ = l_Lean_computeStructureResolutionOrder(v_m_2835_, v_inst_2836_, v_inst_2837_, v_structName_2838_, v_relaxed_boxed_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2842_, lean_object* v_inst_2843_, lean_object* v_inst_2844_, lean_object* v_structName_2845_, lean_object* v_parentNames_2846_, uint8_t v_relaxed_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2843_, v_inst_2844_, v_structName_2845_, v_parentNames_2846_, v_relaxed_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_structName_2852_, lean_object* v_parentNames_2853_, lean_object* v_relaxed_2854_){
_start:
{
uint8_t v_relaxed_boxed_2855_; lean_object* v_res_2856_; 
v_relaxed_boxed_2855_ = lean_unbox(v_relaxed_2854_);
v_res_2856_ = l_Lean_mergeStructureResolutionOrders(v_m_2849_, v_inst_2850_, v_inst_2851_, v_structName_2852_, v_parentNames_2853_, v_relaxed_boxed_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2857_){
_start:
{
lean_object* v_resolutionOrder_2858_; 
v_resolutionOrder_2858_ = lean_ctor_get(v_x_2857_, 0);
lean_inc_ref(v_resolutionOrder_2858_);
return v_resolutionOrder_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2859_);
lean_dec_ref(v_x_2859_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_structName_2864_){
_start:
{
lean_object* v_toApplicative_2865_; lean_object* v_toFunctor_2866_; lean_object* v_map_2867_; lean_object* v___f_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_toApplicative_2865_ = lean_ctor_get(v_inst_2862_, 0);
v_toFunctor_2866_ = lean_ctor_get(v_toApplicative_2865_, 0);
v_map_2867_ = lean_ctor_get(v_toFunctor_2866_, 0);
lean_inc(v_map_2867_);
v___f_2868_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2869_ = 1;
v___x_2870_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2862_, v_inst_2863_, v_structName_2864_, v___x_2869_);
v___x_2871_ = lean_apply_4(v_map_2867_, lean_box(0), lean_box(0), v___f_2868_, v___x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_structName_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2873_, v_inst_2874_, v_structName_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2877_, lean_object* v_structName_2878_, lean_object* v_x_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Array_erase___redArg(v___x_2877_, v_x_2879_, v_structName_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_structName_2883_){
_start:
{
lean_object* v_toApplicative_2884_; lean_object* v_toFunctor_2885_; lean_object* v_map_2886_; lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_toApplicative_2884_ = lean_ctor_get(v_inst_2881_, 0);
v_toFunctor_2885_ = lean_ctor_get(v_toApplicative_2884_, 0);
v_map_2886_ = lean_ctor_get(v_toFunctor_2885_, 0);
lean_inc(v_map_2886_);
v___x_2887_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2883_);
v___f_2888_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2888_, 0, v___x_2887_);
lean_closure_set(v___f_2888_, 1, v_structName_2883_);
v___x_2889_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2881_, v_inst_2882_, v_structName_2883_);
v___x_2890_ = lean_apply_4(v_map_2886_, lean_box(0), lean_box(0), v___f_2888_, v___x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_structName_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_getAllParentStructures___redArg(v_inst_2892_, v_inst_2893_, v_structName_2894_);
return v___x_2895_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
