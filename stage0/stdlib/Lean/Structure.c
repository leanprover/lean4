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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0_value;
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_13_);
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
lean_dec_ref(v_x_25_);
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
lean_dec_ref(v___x_227_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; 
v___x_521_ = ((size_t)5ULL);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_shift_left(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; 
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_526_ = lean_usize_sub(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_528_, size_t v_x_529_, size_t v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_es_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v_j_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_es_533_ = lean_ctor_get(v_x_528_, 0);
v___x_534_ = ((size_t)5ULL);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_537_ = lean_usize_land(v_x_529_, v___x_536_);
v_j_538_ = lean_usize_to_nat(v___x_537_);
v___x_539_ = lean_array_get_size(v_es_533_);
v___x_540_ = lean_nat_dec_lt(v_j_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec(v_j_538_);
lean_dec(v_x_532_);
lean_dec(v_x_531_);
return v_x_528_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_577_; 
lean_inc_ref(v_es_533_);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_x_528_, 0);
lean_dec(v_unused_578_);
v___x_542_ = v_x_528_;
v_isShared_543_ = v_isSharedCheck_577_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_x_528_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_577_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_v_544_; lean_object* v___x_545_; lean_object* v_xs_x27_546_; lean_object* v___y_548_; 
v_v_544_ = lean_array_fget(v_es_533_, v_j_538_);
v___x_545_ = lean_box(0);
v_xs_x27_546_ = lean_array_fset(v_es_533_, v_j_538_, v___x_545_);
switch(lean_obj_tag(v_v_544_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v_key_553_ = lean_ctor_get(v_v_544_, 0);
v_val_554_ = lean_ctor_get(v_v_544_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_564_ == 0)
{
v___x_556_ = v_v_544_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_inc(v_key_553_);
lean_dec(v_v_544_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_name_eq(v_x_531_, v_key_553_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_556_);
v___x_559_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_553_, v_val_554_, v_x_531_, v_x_532_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___y_548_ = v___x_560_;
goto v___jp_547_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v_val_554_);
lean_dec(v_key_553_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_x_532_);
lean_ctor_set(v___x_556_, 0, v_x_531_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_x_531_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_x_532_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
}
}
}
case 1:
{
lean_object* v_node_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
v_node_565_ = lean_ctor_get(v_v_544_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_575_ == 0)
{
v___x_567_ = v_v_544_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_node_565_);
lean_dec(v_v_544_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_569_ = lean_usize_shift_right(v_x_529_, v___x_534_);
v___x_570_ = lean_usize_add(v_x_530_, v___x_535_);
v___x_571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_565_, v___x_569_, v___x_570_, v_x_531_, v_x_532_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_548_ = v___x_573_;
goto v___jp_547_;
}
}
}
default: 
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_x_531_);
lean_ctor_set(v___x_576_, 1, v_x_532_);
v___y_548_ = v___x_576_;
goto v___jp_547_;
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_fset(v_xs_x27_546_, v_j_538_, v___y_548_);
lean_dec(v_j_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_551_ = v___x_542_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v_ks_579_; lean_object* v_vs_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_600_; 
v_ks_579_ = lean_ctor_get(v_x_528_, 0);
v_vs_580_ = lean_ctor_get(v_x_528_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_600_ == 0)
{
v___x_582_ = v_x_528_;
v_isShared_583_ = v_isSharedCheck_600_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_vs_580_);
lean_inc(v_ks_579_);
lean_dec(v_x_528_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_600_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_ks_579_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_vs_580_);
v___x_585_ = v_reuseFailAlloc_599_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v_newNode_586_; uint8_t v___y_588_; size_t v___x_594_; uint8_t v___x_595_; 
v_newNode_586_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_585_, v_x_531_, v_x_532_);
v___x_594_ = ((size_t)7ULL);
v___x_595_ = lean_usize_dec_le(v___x_594_, v_x_530_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_586_);
v___x_597_ = lean_unsigned_to_nat(4u);
v___x_598_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
lean_dec(v___x_596_);
v___y_588_ = v___x_598_;
goto v___jp_587_;
}
else
{
v___y_588_ = v___x_595_;
goto v___jp_587_;
}
v___jp_587_:
{
if (v___y_588_ == 0)
{
lean_object* v_ks_589_; lean_object* v_vs_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_ks_589_ = lean_ctor_get(v_newNode_586_, 0);
lean_inc_ref(v_ks_589_);
v_vs_590_ = lean_ctor_get(v_newNode_586_, 1);
lean_inc_ref(v_vs_590_);
lean_dec_ref(v_newNode_586_);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__2);
v___x_593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_530_, v_ks_589_, v_vs_590_, v___x_591_, v___x_592_);
lean_dec_ref(v_vs_590_);
lean_dec_ref(v_ks_589_);
return v___x_593_;
}
else
{
return v_newNode_586_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_601_, lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_i_604_, lean_object* v_entries_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_array_get_size(v_keys_602_);
v___x_607_ = lean_nat_dec_lt(v_i_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v_i_604_);
return v_entries_605_;
}
else
{
lean_object* v_k_608_; lean_object* v_v_609_; uint64_t v___y_611_; 
v_k_608_ = lean_array_fget_borrowed(v_keys_602_, v_i_604_);
v_v_609_ = lean_array_fget_borrowed(v_vals_603_, v_i_604_);
if (lean_obj_tag(v_k_608_) == 0)
{
uint64_t v___x_622_; 
v___x_622_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_611_ = v___x_622_;
goto v___jp_610_;
}
else
{
uint64_t v_hash_623_; 
v_hash_623_ = lean_ctor_get_uint64(v_k_608_, sizeof(void*)*2);
v___y_611_ = v_hash_623_;
goto v___jp_610_;
}
v___jp_610_:
{
size_t v_h_612_; size_t v___x_613_; lean_object* v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v_h_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_h_612_ = lean_uint64_to_usize(v___y_611_);
v___x_613_ = ((size_t)5ULL);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_sub(v_depth_601_, v___x_615_);
v___x_617_ = lean_usize_mul(v___x_613_, v___x_616_);
v_h_618_ = lean_usize_shift_right(v_h_612_, v___x_617_);
v___x_619_ = lean_nat_add(v_i_604_, v___x_614_);
lean_dec(v_i_604_);
lean_inc(v_v_609_);
lean_inc(v_k_608_);
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_605_, v_h_618_, v_depth_601_, v_k_608_, v_v_609_);
v_i_604_ = v___x_619_;
v_entries_605_ = v___x_620_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_i_627_, lean_object* v_entries_628_){
_start:
{
size_t v_depth_boxed_629_; lean_object* v_res_630_; 
v_depth_boxed_629_ = lean_unbox_usize(v_depth_624_);
lean_dec(v_depth_624_);
v_res_630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_629_, v_keys_625_, v_vals_626_, v_i_627_, v_entries_628_);
lean_dec_ref(v_vals_626_);
lean_dec_ref(v_keys_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
size_t v_x_1842__boxed_636_; size_t v_x_1843__boxed_637_; lean_object* v_res_638_; 
v_x_1842__boxed_636_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_x_1843__boxed_637_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_res_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_631_, v_x_1842__boxed_636_, v_x_1843__boxed_637_, v_x_634_, v_x_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
uint64_t v___y_643_; 
if (lean_obj_tag(v_x_640_) == 0)
{
uint64_t v___x_647_; 
v___x_647_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_643_ = v___x_647_;
goto v___jp_642_;
}
else
{
uint64_t v_hash_648_; 
v_hash_648_ = lean_ctor_get_uint64(v_x_640_, sizeof(void*)*2);
v___y_643_ = v_hash_648_;
goto v___jp_642_;
}
v___jp_642_:
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_uint64_to_usize(v___y_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_639_, v___x_644_, v___x_645_, v_x_640_, v_x_641_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_649_, lean_object* v_x_650_, lean_object* v_e_651_){
_start:
{
lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v_snd_652_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_x_650_, 0);
lean_dec(v_unused_662_);
v___x_654_ = v_x_650_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_dec(v_x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_structName_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_structName_656_ = lean_ctor_get(v_e_651_, 0);
lean_inc(v_structName_656_);
v___x_657_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_652_, v_structName_656_, v_e_651_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_657_);
lean_ctor_set(v___x_654_, 0, v___x_649_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_669_, lean_object* v_x_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_669_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_674_, v_x_675_, v___y_676_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_x_675_);
return v_res_678_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_711_; lean_object* v___f_712_; 
v___x_711_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_712_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_712_, 0, v___x_711_);
return v___f_712_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_713_; lean_object* v___f_714_; 
v___x_713_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_714_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_714_, 0, v___x_713_);
return v___f_714_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_715_ = lean_box(0);
v___x_716_ = lean_box(2);
v___f_717_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_718_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_719_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_720_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_721_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_722_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_723_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___f_721_);
lean_ctor_set(v___x_723_, 2, v___f_720_);
lean_ctor_set(v___x_723_, 3, v___f_719_);
lean_ctor_set(v___x_723_, 4, v___f_718_);
lean_ctor_set(v___x_723_, 5, v___f_717_);
lean_ctor_set(v___x_723_, 6, v___x_716_);
lean_ctor_set(v___x_723_, 7, v___x_715_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___f_724_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_725_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___f_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_729_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_732_, lean_object* v_m_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_735_, lean_object* v_m_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_735_, v_m_736_);
lean_dec_ref(v_m_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_738_, lean_object* v_as_739_, lean_object* v_lo_740_, lean_object* v_hi_741_, lean_object* v_w_742_, lean_object* v_hlo_743_, lean_object* v_hhi_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_738_, v_as_739_, v_lo_740_, v_hi_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_746_, lean_object* v_as_747_, lean_object* v_lo_748_, lean_object* v_hi_749_, lean_object* v_w_750_, lean_object* v_hlo_751_, lean_object* v_hhi_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_746_, v_as_747_, v_lo_748_, v_hi_749_, v_w_750_, v_hlo_751_, v_hhi_752_);
lean_dec(v_hi_749_);
lean_dec(v_n_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_755_, v_x_756_, v_x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_759_, lean_object* v_00_u03b2_760_, lean_object* v_map_761_, lean_object* v_f_762_, lean_object* v_init_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_761_, v_f_762_, v_init_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_765_, lean_object* v_00_u03b2_766_, lean_object* v_map_767_, lean_object* v_f_768_, lean_object* v_init_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_765_, v_00_u03b2_766_, v_map_767_, v_f_768_, v_init_769_);
lean_dec_ref(v_map_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_771_, lean_object* v_lo_772_, lean_object* v_hi_773_, lean_object* v_hhi_774_, lean_object* v_pivot_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_k_778_, lean_object* v_ilo_779_, lean_object* v_ik_780_, lean_object* v_w_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_773_, v_pivot_775_, v_as_776_, v_i_777_, v_k_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_783_, lean_object* v_lo_784_, lean_object* v_hi_785_, lean_object* v_hhi_786_, lean_object* v_pivot_787_, lean_object* v_as_788_, lean_object* v_i_789_, lean_object* v_k_790_, lean_object* v_ilo_791_, lean_object* v_ik_792_, lean_object* v_w_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_783_, v_lo_784_, v_hi_785_, v_hhi_786_, v_pivot_787_, v_as_788_, v_i_789_, v_k_790_, v_ilo_791_, v_ik_792_, v_w_793_);
lean_dec_ref(v_pivot_787_);
lean_dec(v_hi_785_);
lean_dec(v_lo_784_);
lean_dec(v_n_783_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, size_t v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_796_, v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
size_t v_x_2245__boxed_808_; size_t v_x_2246__boxed_809_; lean_object* v_res_810_; 
v_x_2245__boxed_808_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_x_2246__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_res_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_802_, v_x_803_, v_x_2245__boxed_808_, v_x_2246__boxed_809_, v_x_806_, v_x_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_811_, lean_object* v_f_812_, lean_object* v_init_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_812_, v_map_811_, v_init_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_815_, lean_object* v_f_816_, lean_object* v_init_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_815_, v_f_816_, v_init_817_);
lean_dec_ref(v_map_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_819_, lean_object* v_00_u03b2_820_, lean_object* v_map_821_, lean_object* v_f_822_, lean_object* v_init_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_822_, v_map_821_, v_init_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_825_, lean_object* v_00_u03b2_826_, lean_object* v_map_827_, lean_object* v_f_828_, lean_object* v_init_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_825_, v_00_u03b2_826_, v_map_827_, v_f_828_, v_init_829_);
lean_dec_ref(v_map_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_831_, lean_object* v_n_832_, lean_object* v_k_833_, lean_object* v_v_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_832_, v_k_833_, v_v_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_836_, size_t v_depth_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_837_, v_keys_838_, v_vals_839_, v_i_841_, v_entries_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_844_, lean_object* v_depth_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_heq_848_, lean_object* v_i_849_, lean_object* v_entries_850_){
_start:
{
size_t v_depth_boxed_851_; lean_object* v_res_852_; 
v_depth_boxed_851_ = lean_unbox_usize(v_depth_845_);
lean_dec(v_depth_845_);
v_res_852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_844_, v_depth_boxed_851_, v_keys_846_, v_vals_847_, v_heq_848_, v_i_849_, v_entries_850_);
lean_dec_ref(v_vals_847_);
lean_dec_ref(v_keys_846_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_853_, lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_f_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_860_, lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_f_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_860_, v_00_u03b1_861_, v_00_u03b2_862_, v_f_863_, v_x_864_, v_x_865_);
lean_dec_ref(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_868_, v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_00_u03c3_875_, lean_object* v_f_876_, lean_object* v_as_877_, size_t v_i_878_, size_t v_stop_879_, lean_object* v_b_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_876_, v_as_877_, v_i_878_, v_stop_879_, v_b_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_00_u03c3_884_, lean_object* v_f_885_, lean_object* v_as_886_, lean_object* v_i_887_, lean_object* v_stop_888_, lean_object* v_b_889_){
_start:
{
size_t v_i_boxed_890_; size_t v_stop_boxed_891_; lean_object* v_res_892_; 
v_i_boxed_890_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_stop_boxed_891_ = lean_unbox_usize(v_stop_888_);
lean_dec(v_stop_888_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_882_, v_00_u03b2_883_, v_00_u03c3_884_, v_f_885_, v_as_886_, v_i_boxed_890_, v_stop_boxed_891_, v_b_889_);
lean_dec_ref(v_as_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_893_, lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_f_896_, lean_object* v_keys_897_, lean_object* v_vals_898_, lean_object* v_heq_899_, lean_object* v_i_900_, lean_object* v_acc_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_896_, v_keys_897_, v_vals_898_, v_i_900_, v_acc_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_903_, lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_f_906_, lean_object* v_keys_907_, lean_object* v_vals_908_, lean_object* v_heq_909_, lean_object* v_i_910_, lean_object* v_acc_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_903_, v_00_u03b1_904_, v_00_u03b2_905_, v_f_906_, v_keys_907_, v_vals_908_, v_heq_909_, v_i_910_, v_acc_911_);
lean_dec_ref(v_vals_908_);
lean_dec_ref(v_keys_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_920_, size_t v_i_921_, lean_object* v_bs_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_923_ == 0)
{
return v_bs_922_;
}
else
{
lean_object* v_v_924_; lean_object* v_fieldName_925_; lean_object* v___x_926_; lean_object* v_bs_x27_927_; size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; 
v_v_924_ = lean_array_uget_borrowed(v_bs_922_, v_i_921_);
v_fieldName_925_ = lean_ctor_get(v_v_924_, 0);
lean_inc(v_fieldName_925_);
v___x_926_ = lean_unsigned_to_nat(0u);
v_bs_x27_927_ = lean_array_uset(v_bs_922_, v_i_921_, v___x_926_);
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_921_, v___x_928_);
v___x_930_ = lean_array_uset(v_bs_x27_927_, v_i_921_, v_fieldName_925_);
v_i_921_ = v___x_929_;
v_bs_922_ = v___x_930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_bs_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_936_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_935_, v_i_boxed_936_, v_bs_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object* v_hi_938_, lean_object* v_pivot_939_, lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_k_942_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = lean_nat_dec_lt(v_k_942_, v_hi_938_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_k_942_);
v___x_944_ = lean_array_fswap(v_as_940_, v_i_941_, v_hi_938_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_i_941_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_fget_borrowed(v_as_940_, v_k_942_);
v___x_947_ = l_Lean_StructureFieldInfo_lt(v___x_946_, v_pivot_939_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_k_942_, v___x_948_);
lean_dec(v_k_942_);
v_k_942_ = v___x_949_;
goto _start;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_951_ = lean_array_fswap(v_as_940_, v_i_941_, v_k_942_);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_i_941_, v___x_952_);
lean_dec(v_i_941_);
v___x_954_ = lean_nat_add(v_k_942_, v___x_952_);
lean_dec(v_k_942_);
v_as_940_ = v___x_951_;
v_i_941_ = v___x_953_;
v_k_942_ = v___x_954_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object* v_hi_956_, lean_object* v_pivot_957_, lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_k_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_956_, v_pivot_957_, v_as_958_, v_i_959_, v_k_960_);
lean_dec_ref(v_pivot_957_);
lean_dec(v_hi_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_n_962_, lean_object* v_as_963_, lean_object* v_lo_964_, lean_object* v_hi_965_){
_start:
{
lean_object* v___y_967_; uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_lt(v_lo_964_, v_hi_965_);
if (v___x_977_ == 0)
{
lean_dec(v_lo_964_);
return v_as_963_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_mid_980_; lean_object* v___y_982_; lean_object* v___y_988_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_978_ = lean_nat_add(v_lo_964_, v_hi_965_);
v___x_979_ = lean_unsigned_to_nat(1u);
v_mid_980_ = lean_nat_shiftr(v___x_978_, v___x_979_);
lean_dec(v___x_978_);
v___x_993_ = lean_array_fget_borrowed(v_as_963_, v_mid_980_);
v___x_994_ = lean_array_fget_borrowed(v_as_963_, v_lo_964_);
v___x_995_ = l_Lean_StructureFieldInfo_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
v___y_988_ = v_as_963_;
goto v___jp_987_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = lean_array_fswap(v_as_963_, v_lo_964_, v_mid_980_);
v___y_988_ = v___x_996_;
goto v___jp_987_;
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_array_fget_borrowed(v___y_982_, v_mid_980_);
v___x_984_ = lean_array_fget_borrowed(v___y_982_, v_hi_965_);
v___x_985_ = l_Lean_StructureFieldInfo_lt(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec(v_mid_980_);
v___y_967_ = v___y_982_;
goto v___jp_966_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_array_fswap(v___y_982_, v_mid_980_, v_hi_965_);
lean_dec(v_mid_980_);
v___y_967_ = v___x_986_;
goto v___jp_966_;
}
}
v___jp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_array_fget_borrowed(v___y_988_, v_hi_965_);
v___x_990_ = lean_array_fget_borrowed(v___y_988_, v_lo_964_);
v___x_991_ = l_Lean_StructureFieldInfo_lt(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
v___y_982_ = v___y_988_;
goto v___jp_981_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_array_fswap(v___y_988_, v_lo_964_, v_hi_965_);
v___y_982_ = v___x_992_;
goto v___jp_981_;
}
}
}
v___jp_966_:
{
lean_object* v_pivot_968_; lean_object* v___x_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; uint8_t v___x_972_; 
v_pivot_968_ = lean_array_fget(v___y_967_, v_hi_965_);
lean_inc_n(v_lo_964_, 2);
v___x_969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_965_, v_pivot_968_, v___y_967_, v_lo_964_, v_lo_964_);
lean_dec(v_pivot_968_);
v_fst_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_fst_970_);
v_snd_971_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_snd_971_);
lean_dec_ref(v___x_969_);
v___x_972_ = lean_nat_dec_le(v_hi_965_, v_fst_970_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_962_, v_snd_971_, v_lo_964_, v_fst_970_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_add(v_fst_970_, v___x_974_);
lean_dec(v_fst_970_);
v_as_963_ = v___x_973_;
v_lo_964_ = v___x_975_;
goto _start;
}
else
{
lean_dec(v_fst_970_);
lean_dec(v_lo_964_);
return v_snd_971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_n_997_, lean_object* v_as_998_, lean_object* v_lo_999_, lean_object* v_hi_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_997_, v_as_998_, v_lo_999_, v_hi_1000_);
lean_dec(v_hi_1000_);
lean_dec(v_n_997_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_1004_, lean_object* v_e_1005_){
_start:
{
lean_object* v_structName_1006_; lean_object* v_fields_1007_; lean_object* v___x_1008_; size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___y_1013_; lean_object* v___x_1020_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_structName_1006_ = lean_ctor_get(v_e_1005_, 0);
lean_inc(v_structName_1006_);
v_fields_1007_ = lean_ctor_get(v_e_1005_, 1);
lean_inc_ref_n(v_fields_1007_, 2);
lean_dec_ref(v_e_1005_);
v___x_1008_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_1009_ = lean_array_size(v_fields_1007_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_1009_, v___x_1010_, v_fields_1007_);
v___x_1020_ = lean_array_get_size(v_fields_1007_);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_nat_dec_eq(v___x_1020_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___y_1030_; uint8_t v___x_1032_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_sub(v___x_1020_, v___x_1027_);
v___x_1032_ = lean_nat_dec_le(v___x_1025_, v___x_1028_);
if (v___x_1032_ == 0)
{
lean_inc(v___x_1028_);
v___y_1030_ = v___x_1028_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v___x_1025_;
goto v___jp_1029_;
}
v___jp_1029_:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_nat_dec_le(v___y_1030_, v___x_1028_);
if (v___x_1031_ == 0)
{
lean_dec(v___x_1028_);
lean_inc(v___y_1030_);
v___y_1022_ = v___y_1030_;
v___y_1023_ = v___y_1030_;
goto v___jp_1021_;
}
else
{
v___y_1022_ = v___y_1030_;
v___y_1023_ = v___x_1028_;
goto v___jp_1021_;
}
}
}
else
{
v___y_1013_ = v_fields_1007_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v_toEnvExtension_1014_; lean_object* v_asyncMode_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_toEnvExtension_1014_ = lean_ctor_get(v___x_1008_, 0);
v_asyncMode_1015_ = lean_ctor_get(v_toEnvExtension_1014_, 2);
v___x_1016_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_1017_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1017_, 0, v_structName_1006_);
lean_ctor_set(v___x_1017_, 1, v___x_1011_);
lean_ctor_set(v___x_1017_, 2, v___y_1013_);
lean_ctor_set(v___x_1017_, 3, v___x_1016_);
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1008_, v_env_1004_, v___x_1017_, v_asyncMode_1015_, v___x_1018_);
return v___x_1019_;
}
v___jp_1021_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_1020_, v_fields_1007_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
v___y_1013_ = v___x_1024_;
goto v___jp_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_1033_, lean_object* v_as_1034_, lean_object* v_lo_1035_, lean_object* v_hi_1036_, lean_object* v_w_1037_, lean_object* v_hlo_1038_, lean_object* v_hhi_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_1033_, v_as_1034_, v_lo_1035_, v_hi_1036_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_1041_, lean_object* v_as_1042_, lean_object* v_lo_1043_, lean_object* v_hi_1044_, lean_object* v_w_1045_, lean_object* v_hlo_1046_, lean_object* v_hhi_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_1041_, v_as_1042_, v_lo_1043_, v_hi_1044_, v_w_1045_, v_hlo_1046_, v_hhi_1047_);
lean_dec(v_hi_1044_);
lean_dec(v_n_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object* v_n_1049_, lean_object* v_lo_1050_, lean_object* v_hi_1051_, lean_object* v_hhi_1052_, lean_object* v_pivot_1053_, lean_object* v_as_1054_, lean_object* v_i_1055_, lean_object* v_k_1056_, lean_object* v_ilo_1057_, lean_object* v_ik_1058_, lean_object* v_w_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_1051_, v_pivot_1053_, v_as_1054_, v_i_1055_, v_k_1056_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object* v_n_1061_, lean_object* v_lo_1062_, lean_object* v_hi_1063_, lean_object* v_hhi_1064_, lean_object* v_pivot_1065_, lean_object* v_as_1066_, lean_object* v_i_1067_, lean_object* v_k_1068_, lean_object* v_ilo_1069_, lean_object* v_ik_1070_, lean_object* v_w_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_1061_, v_lo_1062_, v_hi_1063_, v_hhi_1064_, v_pivot_1065_, v_as_1066_, v_i_1067_, v_k_1068_, v_ilo_1069_, v_ik_1070_, v_w_1071_);
lean_dec_ref(v_pivot_1065_);
lean_dec(v_hi_1063_);
lean_dec(v_lo_1062_);
lean_dec(v_n_1061_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_1073_, lean_object* v_parentInfo_1074_, lean_object* v___x_1075_, lean_object* v_asyncMode_1076_, lean_object* v___x_1077_, lean_object* v_env_1078_){
_start:
{
lean_object* v_structName_1079_; lean_object* v_fieldNames_1080_; lean_object* v_fieldInfo_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_structName_1079_ = lean_ctor_get(v_val_1073_, 0);
v_fieldNames_1080_ = lean_ctor_get(v_val_1073_, 1);
v_fieldInfo_1081_ = lean_ctor_get(v_val_1073_, 2);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_val_1073_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_val_1073_, 3);
lean_dec(v_unused_1090_);
v___x_1083_ = v_val_1073_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_fieldInfo_1081_);
lean_inc(v_fieldNames_1080_);
lean_inc(v_structName_1079_);
lean_dec(v_val_1073_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 3, v_parentInfo_1074_);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_structName_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_fieldNames_1080_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_fieldInfo_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_parentInfo_1074_);
v___x_1086_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1075_, v_env_1078_, v___x_1086_, v_asyncMode_1076_, v___x_1077_);
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_1091_, lean_object* v_parentInfo_1092_, lean_object* v___x_1093_, lean_object* v_asyncMode_1094_, lean_object* v___x_1095_, lean_object* v_env_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_setStructureParents___redArg___lam__0(v_val_1091_, v_parentInfo_1092_, v___x_1093_, v_asyncMode_1094_, v___x_1095_, v_env_1096_);
lean_dec(v_asyncMode_1094_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_structName_1107_, lean_object* v_parentInfo_1108_, lean_object* v_modifyEnv_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_____do__lift_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v_toEnvExtension_1114_; lean_object* v_asyncMode_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_snd_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1134_; 
v___x_1113_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1114_ = lean_ctor_get(v___x_1113_, 0);
v_asyncMode_1115_ = lean_ctor_get(v_toEnvExtension_1114_, 2);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1104_, v___x_1113_, v_____do__lift_1112_, v_asyncMode_1115_, v___x_1116_);
v_snd_1118_ = lean_ctor_get(v___x_1117_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1117_, 0);
lean_dec(v_unused_1135_);
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1134_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_snd_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1134_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; 
lean_inc(v_structName_1107_);
v___x_1122_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1105_, v___x_1106_, v_snd_1118_, v_structName_1107_);
lean_dec(v_snd_1118_);
if (lean_obj_tag(v___x_1122_) == 1)
{
lean_object* v_val_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1120_);
lean_dec_ref(v_inst_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec(v_structName_1107_);
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1122_);
lean_inc(v_asyncMode_1115_);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1124_, 0, v_val_1123_);
lean_closure_set(v___f_1124_, 1, v_parentInfo_1108_);
lean_closure_set(v___f_1124_, 2, v___x_1113_);
lean_closure_set(v___f_1124_, 3, v_asyncMode_1115_);
lean_closure_set(v___f_1124_, 4, v___x_1116_);
v___x_1125_ = lean_apply_1(v_modifyEnv_1109_, v___f_1124_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v___x_1122_);
lean_dec(v_modifyEnv_1109_);
lean_dec_ref(v_parentInfo_1108_);
v___x_1126_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_1127_ = l_Lean_MessageData_ofName(v_structName_1107_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 7);
lean_ctor_set(v___x_1120_, 1, v___x_1127_);
lean_ctor_set(v___x_1120_, 0, v___x_1126_);
v___x_1129_ = v___x_1120_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_throwError___redArg(v_inst_1110_, v_inst_1111_, v___x_1131_);
return v___x_1132_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_instInhabitedStructureState_default;
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_structName_1144_, lean_object* v_parentInfo_1145_){
_start:
{
lean_object* v_toBind_1146_; lean_object* v_getEnv_1147_; lean_object* v_modifyEnv_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; 
v_toBind_1146_ = lean_ctor_get(v_inst_1141_, 1);
lean_inc(v_toBind_1146_);
v_getEnv_1147_ = lean_ctor_get(v_inst_1142_, 0);
lean_inc(v_getEnv_1147_);
v_modifyEnv_1148_ = lean_ctor_get(v_inst_1142_, 1);
lean_inc(v_modifyEnv_1148_);
lean_dec_ref(v_inst_1142_);
v___x_1149_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1150_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1151_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1152_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1152_, 0, v___x_1151_);
lean_closure_set(v___f_1152_, 1, v___x_1149_);
lean_closure_set(v___f_1152_, 2, v___x_1150_);
lean_closure_set(v___f_1152_, 3, v_structName_1144_);
lean_closure_set(v___f_1152_, 4, v_parentInfo_1145_);
lean_closure_set(v___f_1152_, 5, v_modifyEnv_1148_);
lean_closure_set(v___f_1152_, 6, v_inst_1141_);
lean_closure_set(v___f_1152_, 7, v_inst_1143_);
v___x_1153_ = lean_apply_4(v_toBind_1146_, lean_box(0), lean_box(0), v_getEnv_1147_, v___f_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_structName_1158_, lean_object* v_parentInfo_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_setStructureParents___redArg(v_inst_1155_, v_inst_1156_, v_inst_1157_, v_structName_1158_, v_parentInfo_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1161_, lean_object* v_k_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_m_1167_; lean_object* v_a_1168_; uint8_t v___x_1169_; 
v___x_1165_ = lean_nat_add(v_x_1163_, v_x_1164_);
v___x_1166_ = lean_unsigned_to_nat(1u);
v_m_1167_ = lean_nat_shiftr(v___x_1165_, v___x_1166_);
lean_dec(v___x_1165_);
v_a_1168_ = lean_array_fget_borrowed(v_as_1161_, v_m_1167_);
v___x_1169_ = l_Lean_StructureInfo_lt(v_a_1168_, v_k_1162_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; 
lean_dec(v_x_1164_);
v___x_1170_ = l_Lean_StructureInfo_lt(v_k_1162_, v_a_1168_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec(v_m_1167_);
lean_dec(v_x_1163_);
lean_inc(v_a_1168_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1168_);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_nat_dec_eq(v_m_1167_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_nat_sub(v_m_1167_, v___x_1166_);
lean_dec(v_m_1167_);
v___x_1175_ = lean_nat_dec_lt(v___x_1174_, v_x_1163_);
if (v___x_1175_ == 0)
{
v_x_1164_ = v___x_1174_;
goto _start;
}
else
{
lean_object* v___x_1177_; 
lean_dec(v___x_1174_);
lean_dec(v_x_1163_);
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
}
else
{
lean_object* v___x_1178_; 
lean_dec(v_m_1167_);
lean_dec(v_x_1163_);
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
}
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
lean_dec(v_x_1163_);
v___x_1179_ = lean_nat_add(v_m_1167_, v___x_1166_);
lean_dec(v_m_1167_);
v___x_1180_ = lean_nat_dec_le(v___x_1179_, v_x_1164_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v___x_1179_);
lean_dec(v_x_1164_);
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
v_x_1163_ = v___x_1179_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1183_, lean_object* v_k_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1183_, v_k_1184_, v_x_1185_, v_x_1186_);
lean_dec_ref(v_k_1184_);
lean_dec_ref(v_as_1183_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1188_, lean_object* v_vals_1189_, lean_object* v_i_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_array_get_size(v_keys_1188_);
v___x_1193_ = lean_nat_dec_lt(v_i_1190_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_i_1190_);
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
else
{
lean_object* v_k_x27_1195_; uint8_t v___x_1196_; 
v_k_x27_1195_ = lean_array_fget_borrowed(v_keys_1188_, v_i_1190_);
v___x_1196_ = lean_name_eq(v_k_1191_, v_k_x27_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_add(v_i_1190_, v___x_1197_);
lean_dec(v_i_1190_);
v_i_1190_ = v___x_1198_;
goto _start;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_array_fget_borrowed(v_vals_1189_, v_i_1190_);
lean_dec(v_i_1190_);
lean_inc(v___x_1200_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1202_, lean_object* v_vals_1203_, lean_object* v_i_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1202_, v_vals_1203_, v_i_1204_, v_k_1205_);
lean_dec(v_k_1205_);
lean_dec_ref(v_vals_1203_);
lean_dec_ref(v_keys_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1207_, size_t v_x_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1210_; lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; 
v_es_1210_ = lean_ctor_get(v_x_1207_, 0);
v___x_1211_ = lean_box(2);
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__1);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_borrowed(v___x_1211_, v_es_1210_, v_j_1215_);
lean_dec(v_j_1215_);
switch(lean_obj_tag(v___x_1216_))
{
case 0:
{
lean_object* v_key_1217_; lean_object* v_val_1218_; uint8_t v___x_1219_; 
v_key_1217_ = lean_ctor_get(v___x_1216_, 0);
v_val_1218_ = lean_ctor_get(v___x_1216_, 1);
v___x_1219_ = lean_name_eq(v_x_1209_, v_key_1217_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_box(0);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; 
lean_inc(v_val_1218_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_val_1218_);
return v___x_1221_;
}
}
case 1:
{
lean_object* v_node_1222_; size_t v___x_1223_; 
v_node_1222_ = lean_ctor_get(v___x_1216_, 0);
v___x_1223_ = lean_usize_shift_right(v_x_1208_, v___x_1212_);
v_x_1207_ = v_node_1222_;
v_x_1208_ = v___x_1223_;
goto _start;
}
default: 
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
}
}
else
{
lean_object* v_ks_1226_; lean_object* v_vs_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_ks_1226_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1227_ = lean_ctor_get(v_x_1207_, 1);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1226_, v_vs_1227_, v___x_1228_, v_x_1209_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
size_t v_x_395__boxed_1233_; lean_object* v_res_1234_; 
v_x_395__boxed_1233_ = lean_unbox_usize(v_x_1231_);
lean_dec(v_x_1231_);
v_res_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1230_, v_x_395__boxed_1233_, v_x_1232_);
lean_dec(v_x_1232_);
lean_dec_ref(v_x_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
uint64_t v___y_1238_; 
if (lean_obj_tag(v_x_1236_) == 0)
{
uint64_t v___x_1241_; 
v___x_1241_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0);
v___y_1238_ = v___x_1241_;
goto v___jp_1237_;
}
else
{
uint64_t v_hash_1242_; 
v_hash_1242_ = lean_ctor_get_uint64(v_x_1236_, sizeof(void*)*2);
v___y_1238_ = v_hash_1242_;
goto v___jp_1237_;
}
v___jp_1237_:
{
size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_uint64_to_usize(v___y_1238_);
v___x_1240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1235_, v___x_1239_, v_x_1236_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1243_, v_x_1244_);
lean_dec(v_x_1244_);
lean_dec_ref(v_x_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1246_, lean_object* v_structName_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1249_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1246_, v_structName_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; lean_object* v_toEnvExtension_1251_; lean_object* v_asyncMode_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; 
v___x_1250_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1251_ = lean_ctor_get(v___x_1250_, 0);
v_asyncMode_1252_ = lean_ctor_get(v_toEnvExtension_1251_, 2);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1248_, v___x_1250_, v_env_1246_, v_asyncMode_1252_, v___x_1253_);
v_snd_1255_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_snd_1255_);
lean_dec(v___x_1254_);
v___x_1256_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1255_, v_structName_1247_);
lean_dec(v_structName_1247_);
lean_dec(v_snd_1255_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_val_1257_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1257_);
lean_dec_ref(v___x_1249_);
v___x_1258_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1259_ = 0;
v___x_1260_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1248_, v___x_1258_, v_env_1246_, v_val_1257_, v___x_1259_);
lean_dec(v_val_1257_);
lean_dec_ref(v_env_1246_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v___x_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1260_);
lean_dec(v_structName_1247_);
v___x_1264_ = lean_box(0);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_sub(v___x_1262_, v___x_1265_);
v___x_1267_ = lean_nat_dec_le(v___x_1261_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v___x_1266_);
lean_dec_ref(v___x_1260_);
lean_dec(v_structName_1247_);
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1270_, 0, v_structName_1247_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_ctor_set(v___x_1270_, 2, v___x_1269_);
lean_ctor_set(v___x_1270_, 3, v___x_1269_);
v___x_1271_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1260_, v___x_1270_, v___x_1261_, v___x_1266_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1260_);
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1273_, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1276_, v_x_1277_, v_x_1278_);
lean_dec(v_x_1278_);
lean_dec_ref(v_x_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1280_, lean_object* v_k_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1280_, v_k_1281_, v_x_1282_, v_x_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1286_, lean_object* v_k_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1286_, v_k_1287_, v_x_1288_, v_x_1289_, v_x_1290_);
lean_dec_ref(v_k_1287_);
lean_dec_ref(v_as_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, size_t v_x_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1293_, v_x_1294_, v_x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
size_t v_x_531__boxed_1301_; lean_object* v_res_1302_; 
v_x_531__boxed_1301_ = lean_unbox_usize(v_x_1299_);
lean_dec(v_x_1299_);
v_res_1302_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1297_, v_x_1298_, v_x_531__boxed_1301_, v_x_1300_);
lean_dec(v_x_1300_);
lean_dec_ref(v_x_1298_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1303_, lean_object* v_keys_1304_, lean_object* v_vals_1305_, lean_object* v_heq_1306_, lean_object* v_i_1307_, lean_object* v_k_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1304_, v_vals_1305_, v_i_1307_, v_k_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_keys_1311_, lean_object* v_vals_1312_, lean_object* v_heq_1313_, lean_object* v_i_1314_, lean_object* v_k_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1310_, v_keys_1311_, v_vals_1312_, v_heq_1313_, v_i_1314_, v_k_1315_);
lean_dec(v_k_1315_);
lean_dec_ref(v_vals_1312_);
lean_dec_ref(v_keys_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1319_ = lean_panic_fn_borrowed(v___x_1318_, v_msg_1317_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1324_ = lean_unsigned_to_nat(4u);
v___x_1325_ = lean_unsigned_to_nat(139u);
v___x_1326_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1327_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1328_ = l_mkPanicMessageWithDecl(v___x_1327_, v___x_1326_, v___x_1325_, v___x_1324_, v___x_1323_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1329_, lean_object* v_structName_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_getStructureInfo_x3f(v_env_1329_, v_structName_1330_);
if (lean_obj_tag(v___x_1331_) == 1)
{
lean_object* v_val_1332_; 
v_val_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref(v___x_1331_);
return v_val_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1334_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1333_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1337_ = lean_panic_fn_borrowed(v___x_1336_, v_msg_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1340_ = lean_unsigned_to_nat(9u);
v___x_1341_ = lean_unsigned_to_nat(154u);
v___x_1342_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1343_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1344_ = l_mkPanicMessageWithDecl(v___x_1343_, v___x_1342_, v___x_1341_, v___x_1340_, v___x_1339_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1346_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1347_ = lean_unsigned_to_nat(11u);
v___x_1348_ = lean_unsigned_to_nat(153u);
v___x_1349_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1350_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1351_ = l_mkPanicMessageWithDecl(v___x_1350_, v___x_1349_, v___x_1348_, v___x_1347_, v___x_1346_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1352_, lean_object* v_constName_1353_){
_start:
{
uint8_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = 0;
lean_inc_ref(v_env_1352_);
v___x_1361_ = l_Lean_Environment_find_x3f(v_env_1352_, v_constName_1353_, v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v___x_1361_);
if (lean_obj_tag(v_val_1362_) == 5)
{
lean_object* v_val_1363_; lean_object* v_ctors_1364_; 
v_val_1363_ = lean_ctor_get(v_val_1362_, 0);
lean_inc_ref(v_val_1363_);
lean_dec_ref(v_val_1362_);
v_ctors_1364_ = lean_ctor_get(v_val_1363_, 4);
lean_inc(v_ctors_1364_);
lean_dec_ref(v_val_1363_);
if (lean_obj_tag(v_ctors_1364_) == 1)
{
lean_object* v_tail_1365_; 
v_tail_1365_ = lean_ctor_get(v_ctors_1364_, 1);
if (lean_obj_tag(v_tail_1365_) == 0)
{
lean_object* v_head_1366_; lean_object* v___x_1367_; 
v_head_1366_ = lean_ctor_get(v_ctors_1364_, 0);
lean_inc(v_head_1366_);
lean_dec_ref(v_ctors_1364_);
v___x_1367_ = l_Lean_Environment_find_x3f(v_env_1352_, v_head_1366_, v___x_1360_);
if (lean_obj_tag(v___x_1367_) == 1)
{
lean_object* v_val_1368_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1368_);
lean_dec_ref(v___x_1367_);
if (lean_obj_tag(v_val_1368_) == 6)
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v_val_1368_, 0);
lean_inc_ref(v_val_1369_);
lean_dec_ref(v_val_1368_);
return v_val_1369_;
}
else
{
lean_dec(v_val_1368_);
goto v___jp_1357_;
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1357_;
}
}
else
{
lean_dec_ref(v_ctors_1364_);
lean_dec_ref(v_env_1352_);
goto v___jp_1354_;
}
}
else
{
lean_dec(v_ctors_1364_);
lean_dec_ref(v_env_1352_);
goto v___jp_1354_;
}
}
else
{
lean_dec(v_val_1362_);
lean_dec_ref(v_env_1352_);
goto v___jp_1354_;
}
}
else
{
lean_dec(v___x_1361_);
lean_dec_ref(v_env_1352_);
goto v___jp_1354_;
}
v___jp_1354_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1356_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1355_);
return v___x_1356_;
}
v___jp_1357_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1359_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1358_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1370_, lean_object* v_structName_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v_fieldNames_1373_; 
v___x_1372_ = l_Lean_getStructureInfo(v_env_1370_, v_structName_1371_);
v_fieldNames_1373_ = lean_ctor_get(v___x_1372_, 1);
lean_inc_ref(v_fieldNames_1373_);
lean_dec_ref(v___x_1372_);
return v_fieldNames_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1374_, lean_object* v_structName_1375_, lean_object* v_fieldName_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_getStructureInfo_x3f(v_env_1374_, v_structName_1375_);
if (lean_obj_tag(v___x_1377_) == 1)
{
lean_object* v_val_1378_; lean_object* v_fieldInfo_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v___x_1377_);
v_fieldInfo_1379_ = lean_ctor_get(v_val_1378_, 2);
lean_inc_ref(v_fieldInfo_1379_);
lean_dec(v_val_1378_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_array_get_size(v_fieldInfo_1379_);
v___x_1382_ = lean_nat_dec_lt(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref(v_fieldInfo_1379_);
lean_dec(v_fieldName_1376_);
v___x_1383_ = lean_box(0);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_sub(v___x_1381_, v___x_1384_);
v___x_1386_ = lean_nat_dec_le(v___x_1380_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec(v___x_1385_);
lean_dec_ref(v_fieldInfo_1379_);
lean_dec(v_fieldName_1376_);
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_box(0);
v___x_1390_ = 0;
v___x_1391_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1391_, 0, v_fieldName_1376_);
lean_ctor_set(v___x_1391_, 1, v___x_1388_);
lean_ctor_set(v___x_1391_, 2, v___x_1389_);
lean_ctor_set(v___x_1391_, 3, v___x_1389_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*4, v___x_1390_);
v___x_1392_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1379_, v___x_1391_, v___x_1380_, v___x_1385_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v_fieldInfo_1379_);
return v___x_1392_;
}
}
}
else
{
lean_object* v___x_1393_; 
lean_dec(v___x_1377_);
lean_dec(v_fieldName_1376_);
v___x_1393_ = lean_box(0);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1394_, lean_object* v_structName_1395_, lean_object* v_fieldName_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_getFieldInfo_x3f(v_env_1394_, v_structName_1395_, v_fieldName_1396_);
if (lean_obj_tag(v___x_1397_) == 1)
{
lean_object* v_val_1398_; lean_object* v_subobject_x3f_1399_; 
v_val_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1398_);
lean_dec_ref(v___x_1397_);
v_subobject_x3f_1399_ = lean_ctor_get(v_val_1398_, 2);
lean_inc(v_subobject_x3f_1399_);
lean_dec(v_val_1398_);
return v_subobject_x3f_1399_;
}
else
{
lean_object* v___x_1400_; 
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1401_, lean_object* v_structName_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v_parentInfo_1404_; 
v___x_1403_ = l_Lean_getStructureInfo(v_env_1401_, v_structName_1402_);
v_parentInfo_1404_ = lean_ctor_get(v___x_1403_, 3);
lean_inc_ref(v_parentInfo_1404_);
lean_dec_ref(v___x_1403_);
return v_parentInfo_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1405_, lean_object* v_structName_1406_, lean_object* v_as_1407_, size_t v_i_1408_, size_t v_stop_1409_, lean_object* v_b_1410_){
_start:
{
lean_object* v___y_1412_; uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1408_, v_stop_1409_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_array_uget_borrowed(v_as_1407_, v_i_1408_);
lean_inc(v___x_1417_);
lean_inc(v_structName_1406_);
lean_inc_ref(v_env_1405_);
v___x_1418_ = l_Lean_isSubobjectField_x3f(v_env_1405_, v_structName_1406_, v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
v___y_1412_ = v_b_1410_;
goto v___jp_1411_;
}
else
{
lean_object* v_val_1419_; lean_object* v___x_1420_; 
v_val_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = lean_array_push(v_b_1410_, v_val_1419_);
v___y_1412_ = v___x_1420_;
goto v___jp_1411_;
}
}
else
{
lean_dec(v_structName_1406_);
lean_dec_ref(v_env_1405_);
return v_b_1410_;
}
v___jp_1411_:
{
size_t v___x_1413_; size_t v___x_1414_; 
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1408_, v___x_1413_);
v_i_1408_ = v___x_1414_;
v_b_1410_ = v___y_1412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1421_, lean_object* v_structName_1422_, lean_object* v_as_1423_, lean_object* v_i_1424_, lean_object* v_stop_1425_, lean_object* v_b_1426_){
_start:
{
size_t v_i_boxed_1427_; size_t v_stop_boxed_1428_; lean_object* v_res_1429_; 
v_i_boxed_1427_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1425_);
lean_dec(v_stop_1425_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1421_, v_structName_1422_, v_as_1423_, v_i_boxed_1427_, v_stop_boxed_1428_, v_b_1426_);
lean_dec_ref(v_as_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1430_, lean_object* v_structName_1431_, lean_object* v_as_1432_, lean_object* v_start_1433_, lean_object* v_stop_1434_){
_start:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1436_ = lean_nat_dec_lt(v_start_1433_, v_stop_1434_);
if (v___x_1436_ == 0)
{
lean_dec(v_structName_1431_);
lean_dec_ref(v_env_1430_);
return v___x_1435_;
}
else
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_array_get_size(v_as_1432_);
v___x_1438_ = lean_nat_dec_le(v_stop_1434_, v___x_1437_);
if (v___x_1438_ == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_nat_dec_lt(v_start_1433_, v___x_1437_);
if (v___x_1439_ == 0)
{
lean_dec(v_structName_1431_);
lean_dec_ref(v_env_1430_);
return v___x_1435_;
}
else
{
size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_usize_of_nat(v_start_1433_);
v___x_1441_ = lean_usize_of_nat(v___x_1437_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1430_, v_structName_1431_, v_as_1432_, v___x_1440_, v___x_1441_, v___x_1435_);
return v___x_1442_;
}
}
else
{
size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_usize_of_nat(v_start_1433_);
v___x_1444_ = lean_usize_of_nat(v_stop_1434_);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1430_, v_structName_1431_, v_as_1432_, v___x_1443_, v___x_1444_, v___x_1435_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1446_, lean_object* v_structName_1447_, lean_object* v_as_1448_, lean_object* v_start_1449_, lean_object* v_stop_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1446_, v_structName_1447_, v_as_1448_, v_start_1449_, v_stop_1450_);
lean_dec(v_stop_1450_);
lean_dec(v_start_1449_);
lean_dec_ref(v_as_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1452_, lean_object* v_structName_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_inc(v_structName_1453_);
lean_inc_ref(v_env_1452_);
v___x_1454_ = l_Lean_getStructureFields(v_env_1452_, v_structName_1453_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_array_get_size(v___x_1454_);
v___x_1457_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1452_, v_structName_1453_, v___x_1454_, v___x_1455_, v___x_1456_);
lean_dec_ref(v___x_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1458_, lean_object* v_as_1459_, size_t v_i_1460_, size_t v_stop_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
v___x_1464_ = lean_name_eq(v_a_1458_, v___x_1463_);
if (v___x_1464_ == 0)
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1460_, v___x_1465_);
v_i_1460_ = v___x_1466_;
goto _start;
}
else
{
return v___x_1464_;
}
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = 0;
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1469_, lean_object* v_as_1470_, lean_object* v_i_1471_, lean_object* v_stop_1472_){
_start:
{
size_t v_i_boxed_1473_; size_t v_stop_boxed_1474_; uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_i_boxed_1473_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_stop_boxed_1474_ = lean_unbox_usize(v_stop_1472_);
lean_dec(v_stop_1472_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1469_, v_as_1470_, v_i_boxed_1473_, v_stop_boxed_1474_);
lean_dec_ref(v_as_1470_);
lean_dec(v_a_1469_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_array_get_size(v_as_1477_);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
return v___x_1481_;
}
else
{
if (v___x_1481_ == 0)
{
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1480_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1478_, v_as_1477_, v___x_1482_, v___x_1483_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_as_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1492_, lean_object* v_structName_1493_, lean_object* v_fieldName_1494_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
lean_inc(v_structName_1493_);
lean_inc_ref(v_env_1492_);
v___x_1495_ = l_Lean_getStructureFields(v_env_1492_, v_structName_1493_);
v___x_1496_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1495_, v_fieldName_1494_);
lean_dec_ref(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; lean_object* v_fst_1503_; 
lean_inc_ref(v_env_1492_);
v___x_1497_ = l_Lean_getStructureSubobjects(v_env_1492_, v_structName_1493_);
v___x_1498_ = lean_box(0);
v___x_1499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1500_ = lean_array_size(v___x_1497_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1492_, v_fieldName_1494_, v___x_1497_, v_sz_1500_, v___x_1501_, v___x_1499_);
lean_dec_ref(v___x_1497_);
v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_fst_1503_);
lean_dec_ref(v___x_1502_);
if (lean_obj_tag(v_fst_1503_) == 0)
{
return v___x_1498_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v_fst_1503_, 0);
lean_inc(v_val_1504_);
lean_dec_ref(v_fst_1503_);
return v_val_1504_;
}
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v_env_1492_);
v___x_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_structName_1493_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1506_, lean_object* v_fieldName_1507_, lean_object* v_as_1508_, size_t v_sz_1509_, size_t v_i_1510_, lean_object* v_b_1511_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_usize_dec_lt(v_i_1510_, v_sz_1509_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v_env_1506_);
lean_inc_ref(v_b_1511_);
return v_b_1511_;
}
else
{
lean_object* v___x_1513_; lean_object* v_a_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v_a_1514_ = lean_array_uget_borrowed(v_as_1508_, v_i_1510_);
lean_inc(v_a_1514_);
lean_inc_ref(v_env_1506_);
v___x_1515_ = l_Lean_findField_x3f(v_env_1506_, v_a_1514_, v_fieldName_1507_);
if (lean_obj_tag(v___x_1515_) == 1)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v_env_1506_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1513_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; 
lean_dec(v___x_1515_);
v___x_1518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1510_, v___x_1519_);
v_i_1510_ = v___x_1520_;
v_b_1511_ = v___x_1518_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1522_, lean_object* v_fieldName_1523_, lean_object* v_as_1524_, lean_object* v_sz_1525_, lean_object* v_i_1526_, lean_object* v_b_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1525_);
lean_dec(v_sz_1525_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1522_, v_fieldName_1523_, v_as_1524_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1527_);
lean_dec_ref(v_b_1527_);
lean_dec_ref(v_as_1524_);
lean_dec(v_fieldName_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1531_, lean_object* v_structName_1532_, lean_object* v_fieldName_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_findField_x3f(v_env_1531_, v_structName_1532_, v_fieldName_1533_);
lean_dec(v_fieldName_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1538_, lean_object* v_as_1539_, size_t v_sz_1540_, size_t v_i_1541_, lean_object* v_b_1542_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_lt(v_i_1541_, v_sz_1540_);
if (v___x_1543_ == 0)
{
lean_inc_ref(v_b_1542_);
return v_b_1542_;
}
else
{
lean_object* v_a_1544_; lean_object* v_projFn_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_a_1544_ = lean_array_uget_borrowed(v_as_1539_, v_i_1541_);
v_projFn_1545_ = lean_ctor_get(v_a_1544_, 1);
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Lean_Name_isSuffixOf(v_projName_1538_, v_projFn_1545_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; 
v___x_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1541_, v___x_1549_);
v_i_1541_ = v___x_1550_;
v_b_1542_ = v___x_1548_;
goto _start;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_inc(v_a_1544_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1544_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1546_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1555_, lean_object* v_as_1556_, lean_object* v_sz_1557_, lean_object* v_i_1558_, lean_object* v_b_1559_){
_start:
{
size_t v_sz_boxed_1560_; size_t v_i_boxed_1561_; lean_object* v_res_1562_; 
v_sz_boxed_1560_ = lean_unbox_usize(v_sz_1557_);
lean_dec(v_sz_1557_);
v_i_boxed_1561_ = lean_unbox_usize(v_i_1558_);
lean_dec(v_i_1558_);
v_res_1562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1555_, v_as_1556_, v_sz_boxed_1560_, v_i_boxed_1561_, v_b_1559_);
lean_dec_ref(v_b_1559_);
lean_dec_ref(v_as_1556_);
lean_dec(v_projName_1555_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1563_, lean_object* v_projName_1564_, lean_object* v_structName_1565_, lean_object* v_a_1566_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_NameSet_contains(v_a_1566_, v_structName_1565_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1592_; size_t v_sz_1593_; size_t v___x_1594_; lean_object* v___x_1595_; lean_object* v_fst_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1613_; 
lean_inc(v_structName_1565_);
lean_inc_ref(v_env_1563_);
v___x_1568_ = l_Lean_getStructureParentInfo(v_env_1563_, v_structName_1565_);
v___x_1592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1593_ = lean_array_size(v___x_1568_);
v___x_1594_ = ((size_t)0ULL);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1564_, v___x_1568_, v_sz_1593_, v___x_1594_, v___x_1592_);
v_fst_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1595_, 1);
lean_dec(v_unused_1614_);
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_fst_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
v___jp_1569_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v_fst_1576_; lean_object* v_fst_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v___x_1570_ = l_Lean_NameSet_insert(v_a_1566_, v_structName_1565_);
v___x_1571_ = lean_box(0);
v___x_1572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1573_ = lean_array_size(v___x_1568_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1563_, v_projName_1564_, v___x_1568_, v_sz_1573_, v___x_1574_, v___x_1572_, v___x_1570_);
lean_dec_ref(v___x_1568_);
v_fst_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_fst_1576_);
v_fst_1577_ = lean_ctor_get(v_fst_1576_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_fst_1576_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v_fst_1576_, 1);
lean_dec(v_unused_1591_);
v___x_1579_ = v_fst_1576_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_fst_1577_);
lean_dec(v_fst_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
if (lean_obj_tag(v_fst_1577_) == 0)
{
lean_object* v_snd_1581_; lean_object* v___x_1583_; 
v_snd_1581_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_snd_1581_);
lean_dec_ref(v___x_1575_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_snd_1581_);
lean_ctor_set(v___x_1579_, 0, v___x_1571_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_snd_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
lean_object* v_snd_1585_; lean_object* v_val_1586_; lean_object* v___x_1588_; 
v_snd_1585_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_snd_1585_);
lean_dec_ref(v___x_1575_);
v_val_1586_ = lean_ctor_get(v_fst_1577_, 0);
lean_inc(v_val_1586_);
lean_dec_ref(v_fst_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_snd_1585_);
lean_ctor_set(v___x_1579_, 0, v_val_1586_);
v___x_1588_ = v___x_1579_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_val_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1585_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_fst_1596_) == 0)
{
lean_del_object(v___x_1598_);
goto v___jp_1569_;
}
else
{
lean_object* v_val_1600_; 
v_val_1600_ = lean_ctor_get(v_fst_1596_, 0);
lean_inc(v_val_1600_);
lean_dec_ref(v_fst_1596_);
if (lean_obj_tag(v_val_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v___x_1568_);
lean_dec(v_structName_1565_);
lean_dec_ref(v_env_1563_);
v_val_1601_ = lean_ctor_get(v_val_1600_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_val_1600_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1603_ = v_val_1600_;
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v_val_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_structName_1605_; lean_object* v___x_1607_; 
v_structName_1605_ = lean_ctor_get(v_val_1601_, 0);
lean_inc(v_structName_1605_);
lean_dec(v_val_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_structName_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_structName_1605_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v_a_1566_);
lean_ctor_set(v___x_1598_, 0, v___x_1607_);
v___x_1609_ = v___x_1598_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1566_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_dec(v_val_1600_);
lean_del_object(v___x_1598_);
goto v___jp_1569_;
}
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_structName_1565_);
lean_dec_ref(v_env_1563_);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v_a_1566_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1617_, lean_object* v_projName_1618_, lean_object* v_as_1619_, size_t v_sz_1620_, size_t v_i_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_usize_dec_lt(v_i_1621_, v_sz_1620_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v_env_1617_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_b_1622_);
lean_ctor_set(v___x_1625_, 1, v___y_1623_);
return v___x_1625_;
}
else
{
lean_object* v_a_1626_; lean_object* v_structName_1627_; lean_object* v___x_1628_; lean_object* v_fst_1629_; lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_b_1622_);
v_a_1626_ = lean_array_uget_borrowed(v_as_1619_, v_i_1621_);
v_structName_1627_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_structName_1627_);
lean_inc_ref(v_env_1617_);
v___x_1628_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1617_, v_projName_1618_, v_structName_1627_, v___y_1623_);
v_fst_1629_ = lean_ctor_get(v___x_1628_, 0);
v_snd_1630_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_inc(v_fst_1629_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_box(0);
if (lean_obj_tag(v_fst_1629_) == 1)
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec_ref(v_env_1617_);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_fst_1629_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v___x_1634_);
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1634_);
v___x_1637_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v_snd_1630_);
return v___x_1638_;
}
}
else
{
lean_object* v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; 
lean_del_object(v___x_1632_);
lean_dec(v_fst_1629_);
v___x_1640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_add(v_i_1621_, v___x_1641_);
v_i_1621_ = v___x_1642_;
v_b_1622_ = v___x_1640_;
v___y_1623_ = v_snd_1630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1645_, lean_object* v_projName_1646_, lean_object* v_as_1647_, lean_object* v_sz_1648_, lean_object* v_i_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_){
_start:
{
size_t v_sz_boxed_1652_; size_t v_i_boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1652_ = lean_unbox_usize(v_sz_1648_);
lean_dec(v_sz_1648_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1649_);
lean_dec(v_i_1649_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1645_, v_projName_1646_, v_as_1647_, v_sz_boxed_1652_, v_i_boxed_1653_, v_b_1650_, v___y_1651_);
lean_dec_ref(v_as_1647_);
lean_dec(v_projName_1646_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1655_, lean_object* v_projName_1656_, lean_object* v_structName_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1655_, v_projName_1656_, v_structName_1657_, v_a_1658_);
lean_dec(v_projName_1656_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1660_, lean_object* v_structName_1661_, lean_object* v_projName_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_fst_1665_; 
v___x_1663_ = l_Lean_NameSet_empty;
v___x_1664_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1660_, v_projName_1662_, v_structName_1661_, v___x_1663_);
v_fst_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_fst_1665_);
lean_dec_ref(v___x_1664_);
return v_fst_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1666_, lean_object* v_structName_1667_, lean_object* v_projName_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_findParentProjStruct_x3f(v_env_1666_, v_structName_1667_, v_projName_1668_);
lean_dec(v_projName_1668_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1675_ = l_Lean_Name_append(v_structCtorName_1673_, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1676_, lean_object* v_structName_1677_, uint8_t v_includeSubobjectFields_1678_, lean_object* v_as_1679_, size_t v_i_1680_, size_t v_stop_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1680_, v_stop_1681_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_array_uget_borrowed(v_as_1679_, v_i_1680_);
lean_inc(v___x_1689_);
lean_inc(v_structName_1677_);
lean_inc_ref(v_env_1676_);
v___x_1690_ = l_Lean_isSubobjectField_x3f(v_env_1676_, v_structName_1677_, v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_inc(v___x_1689_);
v___x_1691_ = lean_array_push(v_b_1682_, v___x_1689_);
v___y_1684_ = v___x_1691_;
goto v___jp_1683_;
}
else
{
if (v_includeSubobjectFields_1678_ == 0)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; 
v_val_1692_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1692_);
lean_dec_ref(v___x_1690_);
lean_inc_ref(v_env_1676_);
v___x_1693_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1676_, v_val_1692_, v_b_1682_, v_includeSubobjectFields_1678_);
v___y_1684_ = v___x_1693_;
goto v___jp_1683_;
}
else
{
lean_object* v_val_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_val_1694_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1694_);
lean_dec_ref(v___x_1690_);
lean_inc(v___x_1689_);
v___x_1695_ = lean_array_push(v_b_1682_, v___x_1689_);
lean_inc_ref(v_env_1676_);
v___x_1696_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1676_, v_val_1694_, v___x_1695_, v_includeSubobjectFields_1678_);
v___y_1684_ = v___x_1696_;
goto v___jp_1683_;
}
}
}
else
{
lean_dec(v_structName_1677_);
lean_dec_ref(v_env_1676_);
return v_b_1682_;
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1680_, v___x_1685_);
v_i_1680_ = v___x_1686_;
v_b_1682_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1697_, lean_object* v_structName_1698_, lean_object* v_fullNames_1699_, uint8_t v_includeSubobjectFields_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
lean_inc(v_structName_1698_);
lean_inc_ref(v_env_1697_);
v___x_1701_ = l_Lean_getStructureFields(v_env_1697_, v_structName_1698_);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_array_get_size(v___x_1701_);
v___x_1704_ = lean_nat_dec_lt(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v___x_1701_);
lean_dec(v_structName_1698_);
lean_dec_ref(v_env_1697_);
return v_fullNames_1699_;
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_le(v___x_1703_, v___x_1703_);
if (v___x_1705_ == 0)
{
if (v___x_1704_ == 0)
{
lean_dec_ref(v___x_1701_);
lean_dec(v_structName_1698_);
lean_dec_ref(v_env_1697_);
return v_fullNames_1699_;
}
else
{
size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = lean_usize_of_nat(v___x_1703_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1697_, v_structName_1698_, v_includeSubobjectFields_1700_, v___x_1701_, v___x_1706_, v___x_1707_, v_fullNames_1699_);
lean_dec_ref(v___x_1701_);
return v___x_1708_;
}
}
else
{
size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = lean_usize_of_nat(v___x_1703_);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1697_, v_structName_1698_, v_includeSubobjectFields_1700_, v___x_1701_, v___x_1709_, v___x_1710_, v_fullNames_1699_);
lean_dec_ref(v___x_1701_);
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1712_, lean_object* v_structName_1713_, lean_object* v_fullNames_1714_, lean_object* v_includeSubobjectFields_1715_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1716_; lean_object* v_res_1717_; 
v_includeSubobjectFields_boxed_1716_ = lean_unbox(v_includeSubobjectFields_1715_);
v_res_1717_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1712_, v_structName_1713_, v_fullNames_1714_, v_includeSubobjectFields_boxed_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1718_, lean_object* v_structName_1719_, lean_object* v_includeSubobjectFields_1720_, lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v_stop_1723_, lean_object* v_b_1724_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1725_; size_t v_i_boxed_1726_; size_t v_stop_boxed_1727_; lean_object* v_res_1728_; 
v_includeSubobjectFields_boxed_1725_ = lean_unbox(v_includeSubobjectFields_1720_);
v_i_boxed_1726_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_stop_boxed_1727_ = lean_unbox_usize(v_stop_1723_);
lean_dec(v_stop_1723_);
v_res_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1718_, v_structName_1719_, v_includeSubobjectFields_boxed_1725_, v_as_1721_, v_i_boxed_1726_, v_stop_boxed_1727_, v_b_1724_);
lean_dec_ref(v_as_1721_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1729_, lean_object* v_structName_1730_, uint8_t v_includeSubobjectFields_1731_){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1733_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1729_, v_structName_1730_, v___x_1732_, v_includeSubobjectFields_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1734_, lean_object* v_structName_1735_, lean_object* v_includeSubobjectFields_1736_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1737_; lean_object* v_res_1738_; 
v_includeSubobjectFields_boxed_1737_ = lean_unbox(v_includeSubobjectFields_1736_);
v_res_1738_ = l_Lean_getStructureFieldsFlattened(v_env_1734_, v_structName_1735_, v_includeSubobjectFields_boxed_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1739_, lean_object* v_constName_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_getStructureInfo_x3f(v_env_1739_, v_constName_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 0;
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
lean_dec_ref(v___x_1741_);
v___x_1743_ = 1;
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1744_, lean_object* v_constName_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Lean_isStructure(v_env_1744_, v_constName_1745_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1748_, lean_object* v_structName_1749_, lean_object* v_fieldName_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_getFieldInfo_x3f(v_env_1748_, v_structName_1749_, v_fieldName_1750_);
if (lean_obj_tag(v___x_1751_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1760_; 
v_val_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_val_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_projFn_1756_; lean_object* v___x_1758_; 
v_projFn_1756_ = lean_ctor_get(v_val_1752_, 1);
lean_inc(v_projFn_1756_);
lean_dec(v_val_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v_projFn_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_projFn_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v___x_1761_; 
lean_dec(v___x_1751_);
v___x_1761_ = lean_box(0);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1762_, lean_object* v_structName_1763_, lean_object* v_fieldName_1764_){
_start:
{
lean_object* v___x_1765_; 
lean_inc_ref(v_env_1762_);
v___x_1765_ = l_Lean_getProjFnForField_x3f(v_env_1762_, v_structName_1763_, v_fieldName_1764_);
if (lean_obj_tag(v___x_1765_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1767_; 
v_val_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc_n(v_val_1766_, 2);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1762_, v_val_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; 
lean_dec(v_val_1766_);
v___x_1768_ = lean_box(0);
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1777_; 
v_val_1769_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_val_1769_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_val_1766_);
lean_ctor_set(v___x_1773_, 1, v_val_1769_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1773_);
v___x_1775_ = v___x_1771_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v___x_1765_);
lean_dec_ref(v_env_1762_);
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1784_ = l_Lean_Name_append(v_projFn_1782_, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1790_ = l_Lean_Name_append(v_projFn_1788_, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1791_, lean_object* v_env_1792_, lean_object* v_structName_1793_, lean_object* v_fieldName_1794_){
_start:
{
lean_object* v___x_1795_; 
lean_inc(v_fieldName_1794_);
lean_inc(v_structName_1793_);
lean_inc_ref(v_env_1792_);
v___x_1795_ = l_Lean_getProjFnForField_x3f(v_env_1792_, v_structName_1793_, v_fieldName_1794_);
if (lean_obj_tag(v___x_1795_) == 1)
{
lean_object* v_val_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_fieldName_1794_);
lean_dec(v_structName_1793_);
v_val_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_val_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_defFn_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; 
v_defFn_1800_ = lean_apply_1(v_mkName_1791_, v_val_1796_);
v___x_1801_ = 1;
lean_inc(v_defFn_1800_);
v___x_1802_ = l_Lean_Environment_contains(v_env_1792_, v_defFn_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_dec(v_defFn_1800_);
lean_del_object(v___x_1798_);
v___x_1803_ = lean_box(0);
return v___x_1803_;
}
else
{
lean_object* v___x_1805_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_defFn_1800_);
v___x_1805_ = v___x_1798_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_defFn_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1808_; lean_object* v_defFn_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; 
lean_dec(v___x_1795_);
v___x_1808_ = l_Lean_Name_append(v_structName_1793_, v_fieldName_1794_);
v_defFn_1809_ = lean_apply_1(v_mkName_1791_, v___x_1808_);
v___x_1810_ = 1;
lean_inc(v_defFn_1809_);
v___x_1811_ = l_Lean_Environment_contains(v_env_1792_, v_defFn_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
lean_dec(v_defFn_1809_);
v___x_1812_ = lean_box(0);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_defFn_1809_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1815_, lean_object* v_structName_1816_, lean_object* v_fieldName_1817_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1819_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1818_, v_env_1815_, v_structName_1816_, v_fieldName_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1821_, lean_object* v_structName_1822_, lean_object* v_fieldName_1823_){
_start:
{
lean_object* v___x_1824_; 
lean_inc(v_fieldName_1823_);
lean_inc(v_structName_1822_);
lean_inc_ref(v_env_1821_);
v___x_1824_ = l_Lean_getDefaultFnForField_x3f(v_env_1821_, v_structName_1822_, v_fieldName_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1826_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1825_, v_env_1821_, v_structName_1822_, v_fieldName_1823_);
return v___x_1826_;
}
else
{
lean_dec(v_fieldName_1823_);
lean_dec(v_structName_1822_);
lean_dec_ref(v_env_1821_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1832_ = l_Lean_Name_append(v_projFn_1830_, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1834_, lean_object* v_structName_1835_, lean_object* v_fieldName_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1838_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1837_, v_env_1834_, v_structName_1835_, v_fieldName_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1839_, lean_object* v_env_1840_, lean_object* v_baseStructName_1841_, lean_object* v_as_1842_, lean_object* v_i_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_snd_1846_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = lean_array_get_size(v_as_1842_);
v___x_1851_ = lean_nat_dec_lt(v_i_1843_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v_i_1843_);
lean_dec_ref(v_env_1840_);
lean_dec(v_path_1839_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___y_1844_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v_subobject_x3f_1855_; 
v___x_1854_ = lean_array_fget_borrowed(v_as_1842_, v_i_1843_);
v_subobject_x3f_1855_ = lean_ctor_get(v___x_1854_, 2);
if (lean_obj_tag(v_subobject_x3f_1855_) == 1)
{
lean_object* v_projFn_1856_; lean_object* v_val_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_fst_1860_; 
v_projFn_1856_ = lean_ctor_get(v___x_1854_, 1);
v_val_1857_ = lean_ctor_get(v_subobject_x3f_1855_, 0);
lean_inc(v_path_1839_);
lean_inc(v_projFn_1856_);
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_projFn_1856_);
lean_ctor_set(v___x_1858_, 1, v_path_1839_);
lean_inc(v_val_1857_);
lean_inc_ref(v_env_1840_);
v___x_1859_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1840_, v_baseStructName_1841_, v_val_1857_, v___x_1858_, v___y_1844_);
v_fst_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_fst_1860_);
if (lean_obj_tag(v_fst_1860_) == 0)
{
lean_object* v_snd_1861_; 
v_snd_1861_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1859_);
v_snd_1846_ = v_snd_1861_;
goto v___jp_1845_;
}
else
{
lean_dec_ref(v_fst_1860_);
lean_dec(v_i_1843_);
lean_dec_ref(v_env_1840_);
lean_dec(v_path_1839_);
return v___x_1859_;
}
}
else
{
v_snd_1846_ = v___y_1844_;
goto v___jp_1845_;
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_add(v_i_1843_, v___x_1847_);
lean_dec(v_i_1843_);
v_i_1843_ = v___x_1848_;
v___y_1844_ = v_snd_1846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1862_, lean_object* v_baseStructName_1863_, lean_object* v_structName_1864_, lean_object* v_path_1865_, lean_object* v_a_1866_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_name_eq(v_baseStructName_1863_, v_structName_1864_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; 
v___x_1881_ = l_Lean_NameSet_contains(v_a_1866_, v_structName_1864_);
if (v___x_1881_ == 0)
{
goto v___jp_1867_;
}
else
{
if (v___x_1880_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_path_1865_);
lean_dec(v_structName_1864_);
lean_dec_ref(v_env_1862_);
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_a_1866_);
return v___x_1883_;
}
else
{
goto v___jp_1867_;
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_structName_1864_);
lean_dec_ref(v_env_1862_);
v___x_1884_ = l_List_reverse___redArg(v_path_1865_);
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v_a_1866_);
return v___x_1886_;
}
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_inc(v_structName_1864_);
v___x_1868_ = l_Lean_NameSet_insert(v_a_1866_, v_structName_1864_);
lean_inc_ref(v_env_1862_);
v___x_1869_ = l_Lean_getStructureInfo_x3f(v_env_1862_, v_structName_1864_);
if (lean_obj_tag(v___x_1869_) == 1)
{
lean_object* v_val_1870_; lean_object* v_fieldInfo_1871_; lean_object* v_parentInfo_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_fst_1875_; 
v_val_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v___x_1869_);
v_fieldInfo_1871_ = lean_ctor_get(v_val_1870_, 2);
lean_inc_ref(v_fieldInfo_1871_);
v_parentInfo_1872_ = lean_ctor_get(v_val_1870_, 3);
lean_inc_ref(v_parentInfo_1872_);
lean_dec(v_val_1870_);
v___x_1873_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1862_);
lean_inc(v_path_1865_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1865_, v_env_1862_, v_baseStructName_1863_, v_fieldInfo_1871_, v___x_1873_, v___x_1868_);
lean_dec_ref(v_fieldInfo_1871_);
v_fst_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_fst_1875_);
if (lean_obj_tag(v_fst_1875_) == 0)
{
lean_object* v_snd_1876_; lean_object* v___x_1877_; 
v_snd_1876_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec_ref(v___x_1874_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1865_, v_env_1862_, v_baseStructName_1863_, v_parentInfo_1872_, v___x_1873_, v_snd_1876_);
lean_dec_ref(v_parentInfo_1872_);
return v___x_1877_;
}
else
{
lean_dec_ref(v_fst_1875_);
lean_dec_ref(v_parentInfo_1872_);
lean_dec(v_path_1865_);
lean_dec_ref(v_env_1862_);
return v___x_1874_;
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v___x_1869_);
lean_dec(v_path_1865_);
lean_dec_ref(v_env_1862_);
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1868_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1887_, lean_object* v_env_1888_, lean_object* v_baseStructName_1889_, lean_object* v_as_1890_, lean_object* v_i_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_get_size(v_as_1890_);
v___x_1894_ = lean_nat_dec_lt(v_i_1891_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_i_1891_);
lean_dec_ref(v_env_1888_);
lean_dec(v_path_1887_);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___y_1892_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v_structName_1898_; lean_object* v_projFn_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_fst_1902_; 
v___x_1897_ = lean_array_fget_borrowed(v_as_1890_, v_i_1891_);
v_structName_1898_ = lean_ctor_get(v___x_1897_, 0);
v_projFn_1899_ = lean_ctor_get(v___x_1897_, 1);
lean_inc(v_path_1887_);
lean_inc(v_projFn_1899_);
v___x_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_projFn_1899_);
lean_ctor_set(v___x_1900_, 1, v_path_1887_);
lean_inc(v_structName_1898_);
lean_inc_ref(v_env_1888_);
v___x_1901_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1888_, v_baseStructName_1889_, v_structName_1898_, v___x_1900_, v___y_1892_);
v_fst_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_fst_1902_);
if (lean_obj_tag(v_fst_1902_) == 0)
{
lean_object* v_snd_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_snd_1903_ = lean_ctor_get(v___x_1901_, 1);
lean_inc(v_snd_1903_);
lean_dec_ref(v___x_1901_);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_i_1891_, v___x_1904_);
lean_dec(v_i_1891_);
v_i_1891_ = v___x_1905_;
v___y_1892_ = v_snd_1903_;
goto _start;
}
else
{
lean_dec_ref(v_fst_1902_);
lean_dec(v_i_1891_);
lean_dec_ref(v_env_1888_);
lean_dec(v_path_1887_);
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1907_, lean_object* v_env_1908_, lean_object* v_baseStructName_1909_, lean_object* v_as_1910_, lean_object* v_i_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1907_, v_env_1908_, v_baseStructName_1909_, v_as_1910_, v_i_1911_, v___y_1912_);
lean_dec_ref(v_as_1910_);
lean_dec(v_baseStructName_1909_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1914_, lean_object* v_env_1915_, lean_object* v_baseStructName_1916_, lean_object* v_as_1917_, lean_object* v_i_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1914_, v_env_1915_, v_baseStructName_1916_, v_as_1917_, v_i_1918_, v___y_1919_);
lean_dec_ref(v_as_1917_);
lean_dec(v_baseStructName_1916_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1921_, lean_object* v_baseStructName_1922_, lean_object* v_structName_1923_, lean_object* v_path_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1921_, v_baseStructName_1922_, v_structName_1923_, v_path_1924_, v_a_1925_);
lean_dec(v_baseStructName_1922_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1927_, lean_object* v_baseStructName_1928_, lean_object* v_structName_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_fst_1933_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = l_Lean_NameSet_empty;
v___x_1932_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1927_, v_baseStructName_1928_, v_structName_1929_, v___x_1930_, v___x_1931_);
v_fst_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_fst_1933_);
lean_dec_ref(v___x_1932_);
return v_fst_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1934_, lean_object* v_baseStructName_1935_, lean_object* v_structName_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_getPathToBaseStructure_x3f(v_env_1934_, v_baseStructName_1935_, v_structName_1936_);
lean_dec(v_baseStructName_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1938_, lean_object* v_constName_1939_){
_start:
{
uint8_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = 0;
v___x_1941_ = l_Lean_Environment_find_x3f(v_env_1938_, v_constName_1939_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 1)
{
lean_object* v_val_1942_; 
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref(v___x_1941_);
if (lean_obj_tag(v_val_1942_) == 5)
{
lean_object* v_val_1943_; lean_object* v_numIndices_1944_; lean_object* v_ctors_1945_; uint8_t v_isRec_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_val_1943_ = lean_ctor_get(v_val_1942_, 0);
lean_inc_ref(v_val_1943_);
lean_dec_ref(v_val_1942_);
v_numIndices_1944_ = lean_ctor_get(v_val_1943_, 2);
lean_inc(v_numIndices_1944_);
v_ctors_1945_ = lean_ctor_get(v_val_1943_, 4);
lean_inc(v_ctors_1945_);
v_isRec_1946_ = lean_ctor_get_uint8(v_val_1943_, sizeof(void*)*6);
lean_dec_ref(v_val_1943_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_nat_dec_eq(v_numIndices_1944_, v___x_1947_);
lean_dec(v_numIndices_1944_);
if (v___x_1948_ == 0)
{
lean_dec(v_ctors_1945_);
return v___x_1940_;
}
else
{
if (lean_obj_tag(v_ctors_1945_) == 1)
{
lean_object* v_tail_1949_; 
v_tail_1949_ = lean_ctor_get(v_ctors_1945_, 1);
lean_inc(v_tail_1949_);
lean_dec_ref(v_ctors_1945_);
if (lean_obj_tag(v_tail_1949_) == 0)
{
if (v_isRec_1946_ == 0)
{
return v___x_1948_;
}
else
{
return v___x_1940_;
}
}
else
{
lean_dec(v_tail_1949_);
return v___x_1940_;
}
}
else
{
lean_dec(v_ctors_1945_);
return v___x_1940_;
}
}
}
else
{
lean_dec(v_val_1942_);
return v___x_1940_;
}
}
else
{
lean_dec(v___x_1941_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1950_, lean_object* v_constName_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l_Lean_isNonRecStructure(v_env_1950_, v_constName_1951_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_panic_fn_borrowed(v___x_1955_, v_msg_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1958_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1959_ = lean_unsigned_to_nat(11u);
v___x_1960_ = lean_unsigned_to_nat(374u);
v___x_1961_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1962_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1963_ = l_mkPanicMessageWithDecl(v___x_1962_, v___x_1961_, v___x_1960_, v___x_1959_, v___x_1958_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1964_, lean_object* v_constName_1965_){
_start:
{
uint8_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = 0;
lean_inc_ref(v_env_1964_);
v___x_1970_ = l_Lean_Environment_find_x3f(v_env_1964_, v_constName_1965_, v___x_1969_);
if (lean_obj_tag(v___x_1970_) == 1)
{
lean_object* v_val_1971_; 
v_val_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_val_1971_);
lean_dec_ref(v___x_1970_);
if (lean_obj_tag(v_val_1971_) == 5)
{
lean_object* v_val_1972_; lean_object* v_numIndices_1973_; lean_object* v_ctors_1974_; uint8_t v_isRec_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_val_1972_ = lean_ctor_get(v_val_1971_, 0);
lean_inc_ref(v_val_1972_);
lean_dec_ref(v_val_1971_);
v_numIndices_1973_ = lean_ctor_get(v_val_1972_, 2);
lean_inc(v_numIndices_1973_);
v_ctors_1974_ = lean_ctor_get(v_val_1972_, 4);
lean_inc(v_ctors_1974_);
v_isRec_1975_ = lean_ctor_get_uint8(v_val_1972_, sizeof(void*)*6);
lean_dec_ref(v_val_1972_);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_nat_dec_eq(v_numIndices_1973_, v___x_1976_);
lean_dec(v_numIndices_1973_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_ctors_1974_);
lean_dec_ref(v_env_1964_);
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
if (lean_obj_tag(v_ctors_1974_) == 1)
{
lean_object* v_tail_1979_; 
v_tail_1979_ = lean_ctor_get(v_ctors_1974_, 1);
if (lean_obj_tag(v_tail_1979_) == 0)
{
if (v_isRec_1975_ == 0)
{
lean_object* v_head_1980_; lean_object* v___x_1981_; 
v_head_1980_ = lean_ctor_get(v_ctors_1974_, 0);
lean_inc(v_head_1980_);
lean_dec_ref(v_ctors_1974_);
v___x_1981_ = l_Lean_Environment_find_x3f(v_env_1964_, v_head_1980_, v_isRec_1975_);
if (lean_obj_tag(v___x_1981_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1990_; 
v_val_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1990_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
if (lean_obj_tag(v_val_1982_) == 6)
{
lean_object* v_val_1986_; lean_object* v___x_1988_; 
v_val_1986_ = lean_ctor_get(v_val_1982_, 0);
lean_inc_ref(v_val_1986_);
lean_dec_ref(v_val_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_val_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_val_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
goto v___jp_1966_;
}
}
}
else
{
lean_dec(v___x_1981_);
goto v___jp_1966_;
}
}
else
{
lean_object* v___x_1991_; 
lean_dec_ref(v_ctors_1974_);
lean_dec_ref(v_env_1964_);
v___x_1991_ = lean_box(0);
return v___x_1991_;
}
}
else
{
lean_object* v___x_1992_; 
lean_dec_ref(v_ctors_1974_);
lean_dec_ref(v_env_1964_);
v___x_1992_ = lean_box(0);
return v___x_1992_;
}
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_ctors_1974_);
lean_dec_ref(v_env_1964_);
v___x_1993_ = lean_box(0);
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v_val_1971_);
lean_dec_ref(v_env_1964_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
}
else
{
lean_object* v___x_1995_; 
lean_dec(v___x_1970_);
lean_dec_ref(v_env_1964_);
v___x_1995_ = lean_box(0);
return v___x_1995_;
}
v___jp_1966_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1968_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1967_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1996_, lean_object* v_constName_1997_){
_start:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = 0;
lean_inc_ref(v_env_1996_);
v___x_1999_ = l_Lean_Environment_find_x3f(v_env_1996_, v_constName_1997_, v___x_1998_);
if (lean_obj_tag(v___x_1999_) == 1)
{
lean_object* v_val_2000_; 
v_val_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref(v___x_1999_);
if (lean_obj_tag(v_val_2000_) == 5)
{
lean_object* v_val_2001_; lean_object* v_numIndices_2002_; lean_object* v_ctors_2003_; uint8_t v_isRec_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_val_2001_ = lean_ctor_get(v_val_2000_, 0);
lean_inc_ref(v_val_2001_);
lean_dec_ref(v_val_2000_);
v_numIndices_2002_ = lean_ctor_get(v_val_2001_, 2);
lean_inc(v_numIndices_2002_);
v_ctors_2003_ = lean_ctor_get(v_val_2001_, 4);
lean_inc(v_ctors_2003_);
v_isRec_2004_ = lean_ctor_get_uint8(v_val_2001_, sizeof(void*)*6);
lean_dec_ref(v_val_2001_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_nat_dec_eq(v_numIndices_2002_, v___x_2005_);
lean_dec(v_numIndices_2002_);
if (v___x_2006_ == 0)
{
lean_dec(v_ctors_2003_);
lean_dec_ref(v_env_1996_);
return v___x_2005_;
}
else
{
if (lean_obj_tag(v_ctors_2003_) == 1)
{
lean_object* v_tail_2007_; 
v_tail_2007_ = lean_ctor_get(v_ctors_2003_, 1);
if (lean_obj_tag(v_tail_2007_) == 0)
{
if (v_isRec_2004_ == 0)
{
lean_object* v_head_2008_; lean_object* v___x_2009_; 
v_head_2008_ = lean_ctor_get(v_ctors_2003_, 0);
lean_inc(v_head_2008_);
lean_dec_ref(v_ctors_2003_);
v___x_2009_ = l_Lean_Environment_find_x3f(v_env_1996_, v_head_2008_, v_isRec_2004_);
if (lean_obj_tag(v___x_2009_) == 1)
{
lean_object* v_val_2010_; 
v_val_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_val_2010_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v_val_2010_) == 6)
{
lean_object* v_val_2011_; lean_object* v_numFields_2012_; 
v_val_2011_ = lean_ctor_get(v_val_2010_, 0);
lean_inc_ref(v_val_2011_);
lean_dec_ref(v_val_2010_);
v_numFields_2012_ = lean_ctor_get(v_val_2011_, 4);
lean_inc(v_numFields_2012_);
lean_dec_ref(v_val_2011_);
return v_numFields_2012_;
}
else
{
lean_dec(v_val_2010_);
return v___x_2005_;
}
}
else
{
lean_dec(v___x_2009_);
return v___x_2005_;
}
}
else
{
lean_dec_ref(v_ctors_2003_);
lean_dec_ref(v_env_1996_);
return v___x_2005_;
}
}
else
{
lean_dec_ref(v_ctors_2003_);
lean_dec_ref(v_env_1996_);
return v___x_2005_;
}
}
else
{
lean_dec(v_ctors_2003_);
lean_dec_ref(v_env_1996_);
return v___x_2005_;
}
}
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_val_2000_);
lean_dec_ref(v_env_1996_);
v___x_2013_ = lean_unsigned_to_nat(0u);
return v___x_2013_;
}
}
else
{
lean_object* v___x_2014_; 
lean_dec(v___x_1999_);
lean_dec_ref(v_env_1996_);
v___x_2014_ = lean_unsigned_to_nat(0u);
return v___x_2014_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_2023_);
return v_res_2025_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___f_2027_; 
v___x_2026_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_2027_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2027_, 0, v___x_2026_);
return v___f_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___f_2029_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_box(1);
v___x_2032_ = l_Lean_registerEnvExtension___redArg(v___f_2029_, v___x_2030_, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2035_, lean_object* v_structName_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v_asyncMode_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2037_ = l_Lean_structureResolutionExt;
v_asyncMode_2038_ = lean_ctor_get(v___x_2037_, 2);
v___x_2039_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2040_ = lean_box(0);
v___x_2041_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2039_, v___x_2037_, v_env_2035_, v_asyncMode_2038_, v___x_2040_);
v___x_2042_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2041_, v_structName_2036_);
lean_dec(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2043_, lean_object* v_structName_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2043_, v_structName_2044_);
lean_dec(v_structName_2044_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v_structName_2048_, lean_object* v_resolutionOrder_2049_, lean_object* v_s_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2046_, v___x_2047_, v_s_2050_, v_structName_2048_, v_resolutionOrder_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2052_, lean_object* v_env_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v_asyncMode_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = l_Lean_structureResolutionExt;
v_asyncMode_2055_ = lean_ctor_get(v___x_2054_, 2);
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2054_, v_env_2053_, v___f_2052_, v_asyncMode_2055_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2058_, lean_object* v_structName_2059_, lean_object* v_resolutionOrder_2060_){
_start:
{
lean_object* v_modifyEnv_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; 
v_modifyEnv_2061_ = lean_ctor_get(v_inst_2058_, 1);
lean_inc(v_modifyEnv_2061_);
lean_dec_ref(v_inst_2058_);
v___x_2062_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2063_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2064_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2064_, 0, v___x_2062_);
lean_closure_set(v___f_2064_, 1, v___x_2063_);
lean_closure_set(v___f_2064_, 2, v_structName_2059_);
lean_closure_set(v___f_2064_, 3, v_resolutionOrder_2060_);
v___f_2065_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2065_, 0, v___f_2064_);
v___x_2066_ = lean_apply_1(v_modifyEnv_2061_, v___f_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2067_, lean_object* v_inst_2068_, lean_object* v_structName_2069_, lean_object* v_resolutionOrder_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2068_, v_structName_2069_, v_resolutionOrder_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2089_, lean_object* v_resOrders_2090_, lean_object* v___x_2091_, lean_object* v_toPure_2092_, lean_object* v_____s_2093_){
_start:
{
lean_object* v_fst_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2109_; 
v_fst_2094_ = lean_ctor_get(v_____s_2093_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_____s_2093_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_____s_2093_, 1);
lean_dec(v_unused_2110_);
v___x_2096_ = v_____s_2093_;
v_isShared_2097_ = v_isSharedCheck_2109_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_fst_2094_);
lean_dec(v_____s_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2109_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_fst_2094_) == 0)
{
uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2098_ = 0;
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = lean_array_get_borrowed(v___x_2089_, v_resOrders_2090_, v___x_2099_);
v___x_2101_ = lean_array_get_borrowed(v___x_2091_, v___x_2100_, v___x_2099_);
v___x_2102_ = lean_box(v___x_2098_);
lean_inc(v___x_2101_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2101_);
lean_ctor_set(v___x_2096_, 0, v___x_2102_);
v___x_2104_ = v___x_2096_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2101_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_apply_2(v_toPure_2092_, lean_box(0), v___x_2104_);
return v___x_2105_;
}
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2108_; 
lean_del_object(v___x_2096_);
v_val_2107_ = lean_ctor_get(v_fst_2094_, 0);
lean_inc(v_val_2107_);
lean_dec_ref(v_fst_2094_);
v___x_2108_ = lean_apply_2(v_toPure_2092_, lean_box(0), v_val_2107_);
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2111_, lean_object* v_resOrders_2112_, lean_object* v___x_2113_, lean_object* v_toPure_2114_, lean_object* v_____s_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2111_, v_resOrders_2112_, v___x_2113_, v_toPure_2114_, v_____s_2115_);
lean_dec(v___x_2113_);
lean_dec_ref(v_resOrders_2112_);
lean_dec_ref(v___x_2111_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2117_, lean_object* v_____do__lift_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_apply_2(v_toPure_2117_, lean_box(0), v_____do__lift_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2120_, lean_object* v_toPure_2121_, lean_object* v___x_2122_, lean_object* v_____s_2123_){
_start:
{
lean_object* v_fst_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2142_; 
v_fst_2124_ = lean_ctor_get(v_____s_2123_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_____s_2123_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v_____s_2123_, 1);
lean_dec(v_unused_2143_);
v___x_2126_ = v_____s_2123_;
v_isShared_2127_ = v_isSharedCheck_2142_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_fst_2124_);
lean_dec(v_____s_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2142_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
if (lean_obj_tag(v_fst_2124_) == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_del_object(v___x_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2120_);
v___x_2129_ = lean_apply_2(v_toPure_2121_, lean_box(0), v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v___x_2131_; 
lean_dec_ref(v___x_2120_);
lean_inc_ref(v_fst_2124_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v___x_2122_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_fst_2124_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2122_);
v___x_2131_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
v_isSharedCheck_2139_ = !lean_is_exclusive(v_fst_2124_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v_fst_2124_, 0);
lean_dec(v_unused_2140_);
v___x_2133_ = v_fst_2124_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v_fst_2124_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
v___x_2136_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_apply_2(v_toPure_2121_, lean_box(0), v___x_2136_);
return v___x_2137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2144_, lean_object* v_next_2145_, lean_object* v_G_2146_, lean_object* v_____do__lift_2147_){
_start:
{
if (lean_obj_tag(v_____do__lift_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
lean_dec(v_G_2146_);
v_a_2148_ = lean_ctor_get(v_____do__lift_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v_____do__lift_2147_);
v___x_2149_ = lean_apply_2(v_toPure_2144_, lean_box(0), v_a_2148_);
return v___x_2149_;
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v_toPure_2144_);
v_a_2150_ = lean_ctor_get(v_____do__lift_2147_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v_____do__lift_2147_);
v___x_2151_ = lean_unsigned_to_nat(1u);
v___x_2152_ = lean_nat_add(v_next_2145_, v___x_2151_);
v___x_2153_ = lean_apply_4(v_G_2146_, v___x_2152_, v_a_2150_, lean_box(0), lean_box(0));
return v___x_2153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2154_, lean_object* v_next_2155_, lean_object* v_G_2156_, lean_object* v_____do__lift_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2154_, v_next_2155_, v_G_2156_, v_____do__lift_2157_);
lean_dec(v_next_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2159_, lean_object* v_v_2160_){
_start:
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_name_eq(v_v_2160_, v___x_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2162_, lean_object* v_v_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2162_, v_v_2163_);
lean_dec(v_v_2163_);
lean_dec(v___x_2162_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2185_, lean_object* v___f_2186_, lean_object* v_resOrder_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v_array_2192_; lean_object* v_start_2193_; lean_object* v_stop_2194_; uint8_t v___x_2195_; lean_object* v___y_2197_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_array_get_size(v_resOrder_2187_);
v___x_2190_ = l_Array_toSubarray___redArg(v_resOrder_2187_, v___x_2188_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2192_ = lean_ctor_get(v___x_2190_, 0);
lean_inc_ref(v_array_2192_);
v_start_2193_ = lean_ctor_get(v___x_2190_, 1);
lean_inc(v_start_2193_);
v_stop_2194_ = lean_ctor_get(v___x_2190_, 2);
lean_inc(v_stop_2194_);
lean_dec_ref(v___x_2190_);
v___x_2195_ = lean_nat_dec_lt(v_start_2193_, v_stop_2194_);
if (v___x_2195_ == 0)
{
lean_dec(v_stop_2194_);
lean_dec(v_start_2193_);
lean_dec_ref(v_array_2192_);
lean_dec_ref(v___f_2186_);
return v___x_2185_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_array_get_size(v_array_2192_);
v___x_2205_ = lean_nat_dec_le(v_stop_2194_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_dec(v_stop_2194_);
v___y_2197_ = v___x_2204_;
goto v___jp_2196_;
}
else
{
v___y_2197_ = v_stop_2194_;
goto v___jp_2196_;
}
}
v___jp_2196_:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_lt(v_start_2193_, v___y_2197_);
if (v___x_2198_ == 0)
{
lean_dec(v___y_2197_);
lean_dec(v_start_2193_);
lean_dec_ref(v_array_2192_);
lean_dec_ref(v___f_2186_);
return v___x_2195_;
}
else
{
size_t v___x_2199_; size_t v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2199_ = lean_usize_of_nat(v_start_2193_);
lean_dec(v_start_2193_);
v___x_2200_ = lean_usize_of_nat(v___y_2197_);
lean_dec(v___y_2197_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2191_, v___f_2186_, v_array_2192_, v___x_2199_, v___x_2200_);
v___x_2202_ = lean_unbox(v___x_2201_);
lean_dec(v___x_2201_);
if (v___x_2202_ == 0)
{
return v___x_2198_;
}
else
{
uint8_t v___x_2203_; 
v___x_2203_ = 0;
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2206_, lean_object* v___f_2207_, lean_object* v_resOrder_2208_){
_start:
{
uint8_t v___x_1715__boxed_2209_; uint8_t v_res_2210_; lean_object* v_r_2211_; 
v___x_1715__boxed_2209_ = lean_unbox(v___x_2206_);
v_res_2210_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2209_, v___f_2207_, v_resOrder_2208_);
v_r_2211_ = lean_box(v_res_2210_);
return v_r_2211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2212_, uint8_t v___y_2213_, lean_object* v_v_2214_){
_start:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_apply_1(v___f_2212_, v_v_2214_);
v___x_2216_ = lean_unbox(v___x_2215_);
if (v___x_2216_ == 0)
{
return v___y_2213_;
}
else
{
uint8_t v___x_2217_; 
v___x_2217_ = 0;
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2218_, lean_object* v___y_2219_, lean_object* v_v_2220_){
_start:
{
uint8_t v___y_1771__boxed_2221_; uint8_t v_res_2222_; lean_object* v_r_2223_; 
v___y_1771__boxed_2221_ = lean_unbox(v___y_2219_);
v_res_2222_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2218_, v___y_1771__boxed_2221_, v_v_2220_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2224_, uint8_t v___x_2225_, lean_object* v_v_2226_){
_start:
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_apply_1(v___f_2224_, v_v_2226_);
v___x_2228_ = lean_unbox(v___x_2227_);
if (v___x_2228_ == 0)
{
return v___x_2225_;
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = 0;
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2230_, lean_object* v___x_2231_, lean_object* v_v_2232_){
_start:
{
uint8_t v___x_1783__boxed_2233_; uint8_t v_res_2234_; lean_object* v_r_2235_; 
v___x_1783__boxed_2233_ = lean_unbox(v___x_2231_);
v_res_2234_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2230_, v___x_1783__boxed_2233_, v_v_2232_);
v_r_2235_ = lean_box(v_res_2234_);
return v_r_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2236_, lean_object* v_toPure_2237_, lean_object* v___x_2238_, lean_object* v_resOrders_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_toBind_2242_, lean_object* v___f_2243_, lean_object* v___x_2244_, lean_object* v_next_2245_, lean_object* v___x_2246_, lean_object* v_next_2247_, lean_object* v_acc_2248_, lean_object* v_h_2249_, lean_object* v_G_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_lt(v_next_2247_, v___x_2236_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_dec(v_G_2250_);
lean_dec(v_next_2247_);
lean_dec_ref(v___x_2244_);
lean_dec(v___f_2243_);
lean_dec(v_toBind_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v_resOrders_2239_);
lean_dec(v___x_2236_);
v___x_2252_ = lean_apply_2(v_toPure_2237_, lean_box(0), v_acc_2248_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_array_2257_; lean_object* v_start_2258_; lean_object* v_stop_2259_; lean_object* v___f_2260_; lean_object* v___y_2262_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; uint8_t v___y_2291_; uint8_t v___x_2303_; 
lean_dec_ref(v_acc_2248_);
v___x_2253_ = lean_array_get_borrowed(v___x_2238_, v_resOrders_2239_, v_next_2247_);
v___x_2254_ = lean_array_get(v___x_2240_, v___x_2253_, v___x_2241_);
lean_inc_n(v_next_2247_, 2);
lean_inc(v___x_2241_);
lean_inc_ref(v_resOrders_2239_);
v___x_2255_ = l_Array_toSubarray___redArg(v_resOrders_2239_, v___x_2241_, v_next_2247_);
v___x_2256_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2257_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_array_2257_);
v_start_2258_ = lean_ctor_get(v___x_2255_, 1);
lean_inc(v_start_2258_);
v_stop_2259_ = lean_ctor_get(v___x_2255_, 2);
lean_inc(v_stop_2259_);
lean_dec_ref(v___x_2255_);
lean_inc(v_toPure_2237_);
v___f_2260_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2260_, 0, v_toPure_2237_);
lean_closure_set(v___f_2260_, 1, v_next_2247_);
lean_closure_set(v___f_2260_, 2, v_G_2250_);
lean_inc(v___x_2254_);
v___f_2287_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2287_, 0, v___x_2254_);
v___x_2288_ = lean_box(v___x_2251_);
v___f_2289_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2289_, 0, v___x_2288_);
lean_closure_set(v___f_2289_, 1, v___f_2287_);
v___x_2303_ = lean_nat_dec_lt(v_start_2258_, v_stop_2259_);
if (v___x_2303_ == 0)
{
lean_dec(v_stop_2259_);
lean_dec(v_start_2258_);
lean_dec_ref(v_array_2257_);
v___y_2291_ = v___x_2251_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___y_2307_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2304_ = lean_box(v___x_2251_);
lean_inc_ref(v___f_2289_);
v___f_2305_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2305_, 0, v___f_2289_);
lean_closure_set(v___f_2305_, 1, v___x_2304_);
v___x_2313_ = lean_array_get_size(v_array_2257_);
v___x_2314_ = lean_nat_dec_le(v_stop_2259_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec(v_stop_2259_);
v___y_2307_ = v___x_2313_;
goto v___jp_2306_;
}
else
{
v___y_2307_ = v_stop_2259_;
goto v___jp_2306_;
}
v___jp_2306_:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_nat_dec_lt(v_start_2258_, v___y_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v___y_2307_);
lean_dec_ref(v___f_2305_);
lean_dec(v_start_2258_);
lean_dec_ref(v_array_2257_);
v___y_2291_ = v___x_2303_;
goto v___jp_2290_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2309_ = lean_usize_of_nat(v_start_2258_);
lean_dec(v_start_2258_);
v___x_2310_ = lean_usize_of_nat(v___y_2307_);
lean_dec(v___y_2307_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2256_, v___f_2305_, v_array_2257_, v___x_2309_, v___x_2310_);
v___x_2312_ = lean_unbox(v___x_2311_);
lean_dec(v___x_2311_);
if (v___x_2312_ == 0)
{
v___y_2291_ = v___x_2308_;
goto v___jp_2290_;
}
else
{
lean_dec_ref(v___f_2289_);
lean_dec(v___x_2254_);
lean_dec(v_next_2247_);
lean_dec(v___x_2241_);
lean_dec_ref(v_resOrders_2239_);
lean_dec(v___x_2236_);
goto v___jp_2265_;
}
}
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_inc(v_toBind_2242_);
v___x_2263_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___y_2262_, v___f_2243_);
v___x_2264_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___x_2263_, v___f_2260_);
return v___x_2264_;
}
v___jp_2265_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2244_);
v___x_2267_ = lean_apply_2(v_toPure_2237_, lean_box(0), v___x_2266_);
v___y_2262_ = v___x_2267_;
goto v___jp_2261_;
}
v___jp_2268_:
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2269_ = lean_nat_dec_eq(v_next_2245_, v___x_2241_);
lean_dec(v___x_2241_);
v___x_2270_ = lean_box(v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2254_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2246_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = lean_apply_2(v_toPure_2237_, lean_box(0), v___x_2274_);
v___y_2262_ = v___x_2275_;
goto v___jp_2261_;
}
v___jp_2276_:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_nat_dec_lt(v___y_2280_, v___y_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___x_2244_);
goto v___jp_2268_;
}
else
{
size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2283_ = lean_usize_of_nat(v___y_2280_);
lean_dec(v___y_2280_);
v___x_2284_ = lean_usize_of_nat(v___y_2281_);
lean_dec(v___y_2281_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2278_, v___y_2277_, v___y_2279_, v___x_2283_, v___x_2284_);
v___x_2286_ = lean_unbox(v___x_2285_);
lean_dec(v___x_2285_);
if (v___x_2286_ == 0)
{
lean_dec_ref(v___x_2244_);
goto v___jp_2268_;
}
else
{
lean_dec(v___x_2254_);
lean_dec(v___x_2241_);
goto v___jp_2265_;
}
}
}
v___jp_2290_:
{
if (v___y_2291_ == 0)
{
lean_dec_ref(v___f_2289_);
lean_dec(v___x_2254_);
lean_dec(v_next_2247_);
lean_dec(v___x_2241_);
lean_dec_ref(v_resOrders_2239_);
lean_dec(v___x_2236_);
goto v___jp_2265_;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_array_2295_; lean_object* v_start_2296_; lean_object* v_stop_2297_; uint8_t v___x_2298_; 
v___x_2292_ = lean_unsigned_to_nat(1u);
v___x_2293_ = lean_nat_add(v_next_2247_, v___x_2292_);
lean_dec(v_next_2247_);
v___x_2294_ = l_Array_toSubarray___redArg(v_resOrders_2239_, v___x_2293_, v___x_2236_);
v_array_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_array_2295_);
v_start_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_start_2296_);
v_stop_2297_ = lean_ctor_get(v___x_2294_, 2);
lean_inc(v_stop_2297_);
lean_dec_ref(v___x_2294_);
v___x_2298_ = lean_nat_dec_lt(v_start_2296_, v_stop_2297_);
if (v___x_2298_ == 0)
{
lean_dec(v_stop_2297_);
lean_dec(v_start_2296_);
lean_dec_ref(v_array_2295_);
lean_dec_ref(v___f_2289_);
lean_dec_ref(v___x_2244_);
goto v___jp_2268_;
}
else
{
lean_object* v___x_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2299_ = lean_box(v___y_2291_);
v___f_2300_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2300_, 0, v___f_2289_);
lean_closure_set(v___f_2300_, 1, v___x_2299_);
v___x_2301_ = lean_array_get_size(v_array_2295_);
v___x_2302_ = lean_nat_dec_le(v_stop_2297_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec(v_stop_2297_);
v___y_2277_ = v___f_2300_;
v___y_2278_ = v___x_2256_;
v___y_2279_ = v_array_2295_;
v___y_2280_ = v_start_2296_;
v___y_2281_ = v___x_2301_;
goto v___jp_2276_;
}
else
{
v___y_2277_ = v___f_2300_;
v___y_2278_ = v___x_2256_;
v___y_2279_ = v_array_2295_;
v___y_2280_ = v_start_2296_;
v___y_2281_ = v_stop_2297_;
goto v___jp_2276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2315_, lean_object* v_toPure_2316_, lean_object* v___x_2317_, lean_object* v_resOrders_2318_, lean_object* v___x_2319_, lean_object* v___x_2320_, lean_object* v_toBind_2321_, lean_object* v___f_2322_, lean_object* v___x_2323_, lean_object* v_next_2324_, lean_object* v___x_2325_, lean_object* v_next_2326_, lean_object* v_acc_2327_, lean_object* v_h_2328_, lean_object* v_G_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2315_, v_toPure_2316_, v___x_2317_, v_resOrders_2318_, v___x_2319_, v___x_2320_, v_toBind_2321_, v___f_2322_, v___x_2323_, v_next_2324_, v___x_2325_, v_next_2326_, v_acc_2327_, v_h_2328_, v_G_2329_);
lean_dec(v_next_2324_);
lean_dec(v___x_2319_);
lean_dec_ref(v___x_2317_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2331_, lean_object* v_toPure_2332_, lean_object* v___x_2333_, lean_object* v_resOrders_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v_toBind_2337_, lean_object* v___f_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v___f_2341_, lean_object* v___f_2342_, lean_object* v_next_2343_, lean_object* v_acc_2344_, lean_object* v_h_2345_, lean_object* v_G_2346_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_nat_dec_lt(v_next_2343_, v___x_2331_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_G_2346_);
lean_dec(v_next_2343_);
lean_dec(v___f_2342_);
lean_dec(v___f_2341_);
lean_dec_ref(v___x_2339_);
lean_dec(v___f_2338_);
lean_dec(v_toBind_2337_);
lean_dec(v___x_2336_);
lean_dec(v___x_2335_);
lean_dec_ref(v_resOrders_2334_);
lean_dec_ref(v___x_2333_);
v___x_2348_ = lean_apply_2(v_toPure_2332_, lean_box(0), v_acc_2344_);
return v___x_2348_;
}
else
{
lean_object* v___f_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec_ref(v_acc_2344_);
lean_inc(v_next_2343_);
lean_inc(v_toPure_2332_);
v___f_2349_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2349_, 0, v_toPure_2332_);
lean_closure_set(v___f_2349_, 1, v_next_2343_);
lean_closure_set(v___f_2349_, 2, v_G_2346_);
v___x_2350_ = lean_nat_sub(v___x_2331_, v_next_2343_);
lean_inc_ref(v___x_2339_);
lean_inc_n(v_toBind_2337_, 3);
lean_inc(v___x_2336_);
v___f_2351_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2351_, 0, v___x_2350_);
lean_closure_set(v___f_2351_, 1, v_toPure_2332_);
lean_closure_set(v___f_2351_, 2, v___x_2333_);
lean_closure_set(v___f_2351_, 3, v_resOrders_2334_);
lean_closure_set(v___f_2351_, 4, v___x_2335_);
lean_closure_set(v___f_2351_, 5, v___x_2336_);
lean_closure_set(v___f_2351_, 6, v_toBind_2337_);
lean_closure_set(v___f_2351_, 7, v___f_2338_);
lean_closure_set(v___f_2351_, 8, v___x_2339_);
lean_closure_set(v___f_2351_, 9, v_next_2343_);
lean_closure_set(v___f_2351_, 10, v___x_2340_);
v___x_2352_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2351_, v___x_2336_, v___x_2339_, lean_box(0));
v___x_2353_ = lean_apply_4(v_toBind_2337_, lean_box(0), lean_box(0), v___x_2352_, v___f_2341_);
v___x_2354_ = lean_apply_4(v_toBind_2337_, lean_box(0), lean_box(0), v___x_2353_, v___f_2342_);
v___x_2355_ = lean_apply_4(v_toBind_2337_, lean_box(0), lean_box(0), v___x_2354_, v___f_2349_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2356_, lean_object* v_toPure_2357_, lean_object* v___x_2358_, lean_object* v_resOrders_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v_toBind_2362_, lean_object* v___f_2363_, lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v___f_2366_, lean_object* v___f_2367_, lean_object* v_next_2368_, lean_object* v_acc_2369_, lean_object* v_h_2370_, lean_object* v_G_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2356_, v_toPure_2357_, v___x_2358_, v_resOrders_2359_, v___x_2360_, v___x_2361_, v_toBind_2362_, v___f_2363_, v___x_2364_, v___x_2365_, v___f_2366_, v___f_2367_, v_next_2368_, v_acc_2369_, v_h_2370_, v_G_2371_);
lean_dec(v___x_2356_);
return v_res_2372_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Array_instInhabited(lean_box(0));
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2377_, lean_object* v_resOrders_2378_){
_start:
{
lean_object* v_toApplicative_2379_; lean_object* v_toBind_2380_; lean_object* v_toPure_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_toApplicative_2379_ = lean_ctor_get(v_inst_2377_, 0);
lean_inc_ref(v_toApplicative_2379_);
v_toBind_2380_ = lean_ctor_get(v_inst_2377_, 1);
lean_inc_n(v_toBind_2380_, 2);
lean_dec_ref(v_inst_2377_);
v_toPure_2381_ = lean_ctor_get(v_toApplicative_2379_, 1);
lean_inc_n(v_toPure_2381_, 4);
lean_dec_ref(v_toApplicative_2379_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2384_ = lean_array_get_size(v_resOrders_2378_);
lean_inc_ref(v_resOrders_2378_);
v___f_2385_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2385_, 0, v___x_2383_);
lean_closure_set(v___f_2385_, 1, v_resOrders_2378_);
lean_closure_set(v___f_2385_, 2, v___x_2382_);
lean_closure_set(v___f_2385_, 3, v_toPure_2381_);
v___f_2386_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2386_, 0, v_toPure_2381_);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_box(0);
v___x_2389_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2390_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2390_, 0, v___x_2389_);
lean_closure_set(v___f_2390_, 1, v_toPure_2381_);
lean_closure_set(v___f_2390_, 2, v___x_2388_);
lean_inc_ref(v___f_2386_);
v___f_2391_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2391_, 0, v___x_2384_);
lean_closure_set(v___f_2391_, 1, v_toPure_2381_);
lean_closure_set(v___f_2391_, 2, v___x_2383_);
lean_closure_set(v___f_2391_, 3, v_resOrders_2378_);
lean_closure_set(v___f_2391_, 4, v___x_2382_);
lean_closure_set(v___f_2391_, 5, v___x_2387_);
lean_closure_set(v___f_2391_, 6, v_toBind_2380_);
lean_closure_set(v___f_2391_, 7, v___f_2386_);
lean_closure_set(v___f_2391_, 8, v___x_2389_);
lean_closure_set(v___f_2391_, 9, v___x_2388_);
lean_closure_set(v___f_2391_, 10, v___f_2390_);
lean_closure_set(v___f_2391_, 11, v___f_2386_);
v___x_2392_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2391_, v___x_2387_, v___x_2389_, lean_box(0));
v___x_2393_ = lean_apply_4(v_toBind_2380_, lean_box(0), lean_box(0), v___x_2392_, v___f_2385_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2394_, lean_object* v_inst_2395_, lean_object* v_resOrders_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2395_, v_resOrders_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2398_){
_start:
{
lean_object* v_structName_2399_; 
v_structName_2399_ = lean_ctor_get(v_x_2398_, 0);
lean_inc(v_structName_2399_);
return v_structName_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2400_);
lean_dec_ref(v_x_2400_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2402_, lean_object* v_result_2403_, lean_object* v_____r_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_apply_2(v_toPure_2402_, lean_box(0), v_result_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2406_, lean_object* v_inst_2407_, lean_object* v_structName_2408_, lean_object* v_toBind_2409_, lean_object* v_result_2410_){
_start:
{
lean_object* v_resolutionOrder_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_resolutionOrder_2411_ = lean_ctor_get(v_result_2410_, 0);
lean_inc_ref(v_resolutionOrder_2411_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2412_, 0, v_toPure_2406_);
lean_closure_set(v___f_2412_, 1, v_result_2410_);
v___x_2413_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2407_, v_structName_2408_, v_resolutionOrder_2411_);
v___x_2414_ = lean_apply_4(v_toBind_2409_, lean_box(0), lean_box(0), v___x_2413_, v___f_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v___x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_array_get_borrowed(v___x_2417_, v_x_2416_, v___x_2415_);
lean_inc(v___x_2418_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object* v___x_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__5(v___x_2419_, v_x_2420_);
lean_dec_ref(v_x_2420_);
lean_dec(v___x_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_snd_2422_, lean_object* v_x1_2423_, lean_object* v_x2_2424_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_name_eq(v_x2_2424_, v_snd_2422_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_array_push(v_x1_2423_, v_x2_2424_);
return v___x_2426_;
}
else
{
lean_dec(v_x2_2424_);
return v_x1_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v_snd_2427_, lean_object* v_x1_2428_, lean_object* v_x2_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v_snd_2427_, v_x1_2428_, v_x2_2429_);
lean_dec(v_snd_2427_);
return v_res_2430_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v_snd_2431_, lean_object* v_x_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_name_eq(v_x_2432_, v_snd_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v_snd_2434_, lean_object* v_x_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v_snd_2434_, v_x_2435_);
lean_dec(v_x_2435_);
lean_dec(v_snd_2434_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2438_, lean_object* v_parentNames_2439_, lean_object* v_x_2440_){
_start:
{
uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_inc(v_x_2440_);
v___x_2441_ = l_Array_contains___redArg(v___x_2438_, v_parentNames_2439_, v_x_2440_);
v___x_2442_ = lean_box(v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v_x_2440_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2444_, lean_object* v___f_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2447_ = lean_array_get_size(v_x_2446_);
v___x_2448_ = lean_mk_empty_array_with_capacity(v___x_2444_);
v___x_2449_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2450_ = lean_nat_dec_lt(v___x_2444_, v___x_2447_);
if (v___x_2450_ == 0)
{
lean_dec_ref(v_x_2446_);
lean_dec_ref(v___f_2445_);
return v___x_2448_;
}
else
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_le(v___x_2447_, v___x_2447_);
if (v___x_2451_ == 0)
{
if (v___x_2450_ == 0)
{
lean_dec_ref(v_x_2446_);
lean_dec_ref(v___f_2445_);
return v___x_2448_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2447_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2449_, v___f_2445_, v_x_2446_, v___x_2452_, v___x_2453_, v___x_2448_);
return v___x_2454_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2447_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2449_, v___f_2445_, v_x_2446_, v___x_2455_, v___x_2456_, v___x_2448_);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2458_, lean_object* v___f_2459_, lean_object* v_x_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2458_, v___f_2459_, v_x_2460_);
lean_dec(v___x_2458_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v___f_2462_, lean_object* v_x1_2463_, lean_object* v_x2_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_array_2469_; lean_object* v_start_2470_; lean_object* v_stop_2471_; lean_object* v___y_2473_; uint8_t v___x_2480_; 
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_array_get_size(v_x2_2464_);
lean_inc_ref(v_x2_2464_);
v___x_2467_ = l_Array_toSubarray___redArg(v_x2_2464_, v___x_2465_, v___x_2466_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2469_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_array_2469_);
v_start_2470_ = lean_ctor_get(v___x_2467_, 1);
lean_inc(v_start_2470_);
v_stop_2471_ = lean_ctor_get(v___x_2467_, 2);
lean_inc(v_stop_2471_);
lean_dec_ref(v___x_2467_);
v___x_2480_ = lean_nat_dec_lt(v_start_2470_, v_stop_2471_);
if (v___x_2480_ == 0)
{
lean_dec(v_stop_2471_);
lean_dec(v_start_2470_);
lean_dec_ref(v_array_2469_);
lean_dec_ref(v_x2_2464_);
lean_dec_ref(v___f_2462_);
return v_x1_2463_;
}
else
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = lean_array_get_size(v_array_2469_);
v___x_2482_ = lean_nat_dec_le(v_stop_2471_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_dec(v_stop_2471_);
v___y_2473_ = v___x_2481_;
goto v___jp_2472_;
}
else
{
v___y_2473_ = v_stop_2471_;
goto v___jp_2472_;
}
}
v___jp_2472_:
{
uint8_t v___x_2474_; 
v___x_2474_ = lean_nat_dec_lt(v_start_2470_, v___y_2473_);
if (v___x_2474_ == 0)
{
lean_dec(v___y_2473_);
lean_dec(v_start_2470_);
lean_dec_ref(v_array_2469_);
lean_dec_ref(v_x2_2464_);
lean_dec_ref(v___f_2462_);
return v_x1_2463_;
}
else
{
size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2475_ = lean_usize_of_nat(v_start_2470_);
lean_dec(v_start_2470_);
v___x_2476_ = lean_usize_of_nat(v___y_2473_);
lean_dec(v___y_2473_);
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2468_, v___f_2462_, v_array_2469_, v___x_2475_, v___x_2476_);
v___x_2478_ = lean_unbox(v___x_2477_);
lean_dec(v___x_2477_);
if (v___x_2478_ == 0)
{
lean_dec_ref(v_x2_2464_);
return v_x1_2463_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_array_push(v_x1_2463_, v_x2_2464_);
return v___x_2479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v_toPure_2484_, lean_object* v___x_2485_, lean_object* v_fst_2486_, lean_object* v_fst_2487_, lean_object* v___f_2488_, uint8_t v_relaxed_2489_, lean_object* v_parentNames_2490_, lean_object* v_snd_2491_, lean_object* v___f_2492_, lean_object* v_____x_2493_){
_start:
{
lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v_defects_2507_; uint8_t v___x_2521_; 
v_fst_2502_ = lean_ctor_get(v_____x_2493_, 0);
lean_inc(v_fst_2502_);
v_snd_2503_ = lean_ctor_get(v_____x_2493_, 1);
lean_inc_n(v_snd_2503_, 2);
lean_dec_ref(v_____x_2493_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2504_, 0, v_snd_2503_);
lean_inc(v___x_2485_);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2505_, 0, v___x_2485_);
lean_closure_set(v___f_2505_, 1, v___f_2504_);
v___x_2521_ = lean_unbox(v_fst_2502_);
lean_dec(v_fst_2502_);
if (v___x_2521_ == 0)
{
if (v_relaxed_2489_ == 0)
{
lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___y_2525_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2549_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2522_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2490_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2523_, 0, v___x_2522_);
lean_closure_set(v___f_2523_, 1, v_parentNames_2490_);
v___x_2560_ = lean_array_get_size(v_fst_2487_);
v___x_2561_ = lean_mk_empty_array_with_capacity(v___x_2485_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2563_ = lean_nat_dec_lt(v___x_2485_, v___x_2560_);
if (v___x_2563_ == 0)
{
v___y_2549_ = v___x_2561_;
goto v___jp_2548_;
}
else
{
lean_object* v___f_2564_; lean_object* v___f_2565_; uint8_t v___x_2566_; 
lean_inc(v_snd_2503_);
v___f_2564_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_2564_, 0, v_snd_2503_);
v___f_2565_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10), 3, 1);
lean_closure_set(v___f_2565_, 0, v___f_2564_);
v___x_2566_ = lean_nat_dec_le(v___x_2560_, v___x_2560_);
if (v___x_2566_ == 0)
{
if (v___x_2563_ == 0)
{
lean_dec_ref(v___f_2565_);
v___y_2549_ = v___x_2561_;
goto v___jp_2548_;
}
else
{
size_t v___x_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = lean_usize_of_nat(v___x_2560_);
lean_inc(v_fst_2487_);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2562_, v___f_2565_, v_fst_2487_, v___x_2567_, v___x_2568_, v___x_2561_);
v___y_2549_ = v___x_2569_;
goto v___jp_2548_;
}
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = lean_usize_of_nat(v___x_2560_);
lean_inc(v_fst_2487_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2562_, v___f_2565_, v_fst_2487_, v___x_2570_, v___x_2571_, v___x_2561_);
v___y_2549_ = v___x_2572_;
goto v___jp_2548_;
}
}
v___jp_2524_:
{
lean_object* v_conflicts_2526_; uint8_t v___x_2527_; lean_object* v___x_2528_; size_t v_sz_2529_; size_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_defects_2533_; 
v_conflicts_2526_ = l_Array_eraseReps___redArg(v___x_2522_, v___y_2525_);
lean_inc_n(v_snd_2503_, 2);
v___x_2527_ = l_Array_contains___redArg(v___x_2522_, v_parentNames_2490_, v_snd_2503_);
v___x_2528_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2529_ = lean_array_size(v_conflicts_2526_);
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2528_, v___f_2523_, v_sz_2529_, v___x_2530_, v_conflicts_2526_);
v___x_2532_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2532_, 0, v_snd_2503_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*2, v___x_2527_);
v_defects_2533_ = lean_array_push(v_snd_2491_, v___x_2532_);
v_defects_2507_ = v_defects_2533_;
goto v___jp_2506_;
}
v___jp_2534_:
{
lean_object* v___x_2540_; 
lean_inc_ref(v___y_2535_);
v___x_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2535_, v___y_2538_, v___y_2537_, v___y_2536_, v___y_2539_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2539_);
lean_dec(v___y_2538_);
v___y_2525_ = v___x_2540_;
goto v___jp_2524_;
}
v___jp_2541_:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_nat_dec_le(v___y_2546_, v___y_2543_);
if (v___x_2547_ == 0)
{
lean_dec(v___y_2543_);
lean_inc(v___y_2546_);
v___y_2535_ = v___y_2542_;
v___y_2536_ = v___y_2546_;
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2545_;
v___y_2539_ = v___y_2546_;
goto v___jp_2534_;
}
else
{
v___y_2535_ = v___y_2542_;
v___y_2536_ = v___y_2546_;
v___y_2537_ = v___y_2544_;
v___y_2538_ = v___y_2545_;
v___y_2539_ = v___y_2543_;
goto v___jp_2534_;
}
}
v___jp_2548_:
{
lean_object* v___x_2550_; size_t v_sz_2551_; size_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2551_ = lean_array_size(v___y_2549_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2550_, v___f_2492_, v_sz_2551_, v___x_2552_, v___y_2549_);
v___x_2554_ = lean_array_get_size(v___x_2553_);
v___x_2555_ = lean_nat_dec_eq(v___x_2554_, v___x_2485_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2556_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0));
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_nat_sub(v___x_2554_, v___x_2557_);
v___x_2559_ = lean_nat_dec_le(v___x_2485_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_inc(v___x_2558_);
v___y_2542_ = v___x_2556_;
v___y_2543_ = v___x_2558_;
v___y_2544_ = v___x_2553_;
v___y_2545_ = v___x_2554_;
v___y_2546_ = v___x_2558_;
goto v___jp_2541_;
}
else
{
lean_inc(v___x_2485_);
v___y_2542_ = v___x_2556_;
v___y_2543_ = v___x_2558_;
v___y_2544_ = v___x_2553_;
v___y_2545_ = v___x_2554_;
v___y_2546_ = v___x_2485_;
goto v___jp_2541_;
}
}
else
{
v___y_2525_ = v___x_2553_;
goto v___jp_2524_;
}
}
}
else
{
lean_dec_ref(v___f_2492_);
lean_dec_ref(v_parentNames_2490_);
v_defects_2507_ = v_snd_2491_;
goto v___jp_2506_;
}
}
else
{
lean_dec_ref(v___f_2492_);
lean_dec_ref(v_parentNames_2490_);
v_defects_2507_ = v_snd_2491_;
goto v___jp_2506_;
}
v___jp_2494_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___y_2496_);
lean_ctor_set(v___x_2498_, 1, v___y_2495_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
v___x_2501_ = lean_apply_2(v_toPure_2484_, lean_box(0), v___x_2500_);
return v___x_2501_;
}
v___jp_2506_:
{
lean_object* v_resOrder_2508_; lean_object* v___x_2509_; size_t v_sz_2510_; size_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_resOrder_2508_ = lean_array_push(v_fst_2486_, v_snd_2503_);
v___x_2509_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2510_ = lean_array_size(v_fst_2487_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2509_, v___f_2505_, v_sz_2510_, v___x_2511_, v_fst_2487_);
v___x_2513_ = lean_array_get_size(v___x_2512_);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2485_);
v___x_2515_ = lean_nat_dec_lt(v___x_2485_, v___x_2513_);
lean_dec(v___x_2485_);
if (v___x_2515_ == 0)
{
lean_dec(v___x_2512_);
lean_dec_ref(v___f_2488_);
v___y_2495_ = v_defects_2507_;
v___y_2496_ = v_resOrder_2508_;
v___y_2497_ = v___x_2514_;
goto v___jp_2494_;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_le(v___x_2513_, v___x_2513_);
if (v___x_2516_ == 0)
{
if (v___x_2515_ == 0)
{
lean_dec(v___x_2512_);
lean_dec_ref(v___f_2488_);
v___y_2495_ = v_defects_2507_;
v___y_2496_ = v_resOrder_2508_;
v___y_2497_ = v___x_2514_;
goto v___jp_2494_;
}
else
{
size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_usize_of_nat(v___x_2513_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2509_, v___f_2488_, v___x_2512_, v___x_2511_, v___x_2517_, v___x_2514_);
v___y_2495_ = v_defects_2507_;
v___y_2496_ = v_resOrder_2508_;
v___y_2497_ = v___x_2518_;
goto v___jp_2494_;
}
}
else
{
size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_usize_of_nat(v___x_2513_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2509_, v___f_2488_, v___x_2512_, v___x_2511_, v___x_2519_, v___x_2514_);
v___y_2495_ = v_defects_2507_;
v___y_2496_ = v_resOrder_2508_;
v___y_2497_ = v___x_2520_;
goto v___jp_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object* v_toPure_2573_, lean_object* v___x_2574_, lean_object* v_fst_2575_, lean_object* v_fst_2576_, lean_object* v___f_2577_, lean_object* v_relaxed_2578_, lean_object* v_parentNames_2579_, lean_object* v_snd_2580_, lean_object* v___f_2581_, lean_object* v_____x_2582_){
_start:
{
uint8_t v_relaxed_boxed_2583_; lean_object* v_res_2584_; 
v_relaxed_boxed_2583_ = lean_unbox(v_relaxed_2578_);
v_res_2584_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__11(v_toPure_2573_, v___x_2574_, v_fst_2575_, v_fst_2576_, v___f_2577_, v_relaxed_boxed_2583_, v_parentNames_2579_, v_snd_2580_, v___f_2581_, v_____x_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v___x_2585_, lean_object* v_toPure_2586_, lean_object* v___f_2587_, uint8_t v_relaxed_2588_, lean_object* v_parentNames_2589_, lean_object* v___f_2590_, lean_object* v_inst_2591_, lean_object* v_toBind_2592_, lean_object* v_x_2593_, lean_object* v_____s_2594_){
_start:
{
lean_object* v_snd_2595_; lean_object* v_fst_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2620_; 
v_snd_2595_ = lean_ctor_get(v_____s_2594_, 1);
v_fst_2596_ = lean_ctor_get(v_____s_2594_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_____s_2594_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2598_ = v_____s_2594_;
v_isShared_2599_ = v_isSharedCheck_2620_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snd_2595_);
lean_inc(v_fst_2596_);
lean_dec(v_____s_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2620_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2619_; 
v_fst_2600_ = lean_ctor_get(v_snd_2595_, 0);
v_snd_2601_ = lean_ctor_get(v_snd_2595_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_snd_2595_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2603_ = v_snd_2595_;
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_inc(v_fst_2600_);
lean_dec(v_snd_2595_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = lean_array_get_size(v_fst_2596_);
v___x_2606_ = lean_nat_dec_eq(v___x_2605_, v___x_2585_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_del_object(v___x_2603_);
lean_del_object(v___x_2598_);
v___x_2607_ = lean_box(v_relaxed_2588_);
lean_inc(v_fst_2596_);
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_2608_, 0, v_toPure_2586_);
lean_closure_set(v___f_2608_, 1, v___x_2585_);
lean_closure_set(v___f_2608_, 2, v_fst_2600_);
lean_closure_set(v___f_2608_, 3, v_fst_2596_);
lean_closure_set(v___f_2608_, 4, v___f_2587_);
lean_closure_set(v___f_2608_, 5, v___x_2607_);
lean_closure_set(v___f_2608_, 6, v_parentNames_2589_);
lean_closure_set(v___f_2608_, 7, v_snd_2601_);
lean_closure_set(v___f_2608_, 8, v___f_2590_);
v___x_2609_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2591_, v_fst_2596_);
v___x_2610_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2609_, v___f_2608_);
return v___x_2610_;
}
else
{
lean_object* v___x_2612_; 
lean_dec(v_toBind_2592_);
lean_dec_ref(v_inst_2591_);
lean_dec_ref(v___f_2590_);
lean_dec_ref(v_parentNames_2589_);
lean_dec_ref(v___f_2587_);
lean_dec(v___x_2585_);
if (v_isShared_2604_ == 0)
{
v___x_2612_ = v___x_2603_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_fst_2600_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_snd_2601_);
v___x_2612_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2612_);
v___x_2614_ = v___x_2598_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fst_2596_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v___x_2616_ = lean_apply_2(v_toPure_2586_, lean_box(0), v___x_2615_);
return v___x_2616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v___x_2621_, lean_object* v_toPure_2622_, lean_object* v___f_2623_, lean_object* v_relaxed_2624_, lean_object* v_parentNames_2625_, lean_object* v___f_2626_, lean_object* v_inst_2627_, lean_object* v_toBind_2628_, lean_object* v_x_2629_, lean_object* v_____s_2630_){
_start:
{
uint8_t v_relaxed_boxed_2631_; lean_object* v_res_2632_; 
v_relaxed_boxed_2631_ = lean_unbox(v_relaxed_2624_);
v_res_2632_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v___x_2621_, v_toPure_2622_, v___f_2623_, v_relaxed_boxed_2631_, v_parentNames_2625_, v___f_2626_, v_inst_2627_, v_toBind_2628_, v_x_2629_, v_____s_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v_toPure_2637_, lean_object* v___f_2638_, uint8_t v_relaxed_2639_, lean_object* v_parentNames_2640_, lean_object* v_inst_2641_, lean_object* v_toBind_2642_, lean_object* v_structName_2643_, lean_object* v___f_2644_, lean_object* v___f_2645_, lean_object* v_parentResOrders_2646_){
_start:
{
lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; lean_object* v___f_2650_; lean_object* v___y_2652_; lean_object* v_j_2661_; lean_object* v_as_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2647_ = lean_unsigned_to_nat(0u);
v___f_2648_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0));
v___x_2649_ = lean_box(v_relaxed_2639_);
lean_inc(v_toBind_2642_);
lean_inc_ref(v_inst_2641_);
lean_inc_ref(v_parentNames_2640_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2650_, 0, v___x_2647_);
lean_closure_set(v___f_2650_, 1, v_toPure_2637_);
lean_closure_set(v___f_2650_, 2, v___f_2638_);
lean_closure_set(v___f_2650_, 3, v___x_2649_);
lean_closure_set(v___f_2650_, 4, v_parentNames_2640_);
lean_closure_set(v___f_2650_, 5, v___f_2648_);
lean_closure_set(v___f_2650_, 6, v_inst_2641_);
lean_closure_set(v___f_2650_, 7, v_toBind_2642_);
v_j_2661_ = lean_array_get_size(v_parentResOrders_2646_);
v_as_2662_ = lean_array_push(v_parentResOrders_2646_, v_parentNames_2640_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2647_, v_as_2662_, v_j_2661_);
v___x_2664_ = lean_array_get_size(v___x_2663_);
v___x_2665_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2666_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2667_ = lean_nat_dec_lt(v___x_2647_, v___x_2664_);
if (v___x_2667_ == 0)
{
lean_dec_ref(v___x_2663_);
lean_dec_ref(v___f_2645_);
v___y_2652_ = v___x_2665_;
goto v___jp_2651_;
}
else
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_le(v___x_2664_, v___x_2664_);
if (v___x_2668_ == 0)
{
if (v___x_2667_ == 0)
{
lean_dec_ref(v___x_2663_);
lean_dec_ref(v___f_2645_);
v___y_2652_ = v___x_2665_;
goto v___jp_2651_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2664_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2666_, v___f_2645_, v___x_2663_, v___x_2669_, v___x_2670_, v___x_2665_);
v___y_2652_ = v___x_2671_;
goto v___jp_2651_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2664_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2666_, v___f_2645_, v___x_2663_, v___x_2672_, v___x_2673_, v___x_2665_);
v___y_2652_ = v___x_2674_;
goto v___jp_2651_;
}
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v_resOrder_2655_; lean_object* v_defects_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2653_ = lean_unsigned_to_nat(1u);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2653_);
v_resOrder_2655_ = lean_array_push(v___x_2654_, v_structName_2643_);
v_defects_2656_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_resOrder_2655_);
lean_ctor_set(v___x_2657_, 1, v_defects_2656_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___y_2652_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_2641_, v___f_2650_, v___x_2658_);
v___x_2660_ = lean_apply_4(v_toBind_2642_, lean_box(0), lean_box(0), v___x_2659_, v___f_2644_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v_toPure_2675_, lean_object* v___f_2676_, lean_object* v_relaxed_2677_, lean_object* v_parentNames_2678_, lean_object* v_inst_2679_, lean_object* v_toBind_2680_, lean_object* v_structName_2681_, lean_object* v___f_2682_, lean_object* v___f_2683_, lean_object* v_parentResOrders_2684_){
_start:
{
uint8_t v_relaxed_boxed_2685_; lean_object* v_res_2686_; 
v_relaxed_boxed_2685_ = lean_unbox(v_relaxed_2677_);
v_res_2686_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v_toPure_2675_, v___f_2676_, v_relaxed_boxed_2685_, v_parentNames_2678_, v_inst_2679_, v_toBind_2680_, v_structName_2681_, v___f_2682_, v___f_2683_, v_parentResOrders_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2688_ = lean_array_get_size(v_x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_nat_dec_eq(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = 1;
return v___x_2691_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2693_);
lean_dec_ref(v_x_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2696_, lean_object* v_x1_2697_, lean_object* v_x2_2698_){
_start:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
lean_inc_ref(v_x2_2698_);
v___x_2699_ = lean_apply_1(v___f_2696_, v_x2_2698_);
v___x_2700_ = lean_unbox(v___x_2699_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v_x2_2698_);
return v_x1_2697_;
}
else
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_array_push(v_x1_2697_, v_x2_2698_);
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2702_, lean_object* v_____s_2703_){
_start:
{
lean_object* v_snd_2704_; lean_object* v_fst_2705_; lean_object* v_snd_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2714_; 
v_snd_2704_ = lean_ctor_get(v_____s_2703_, 1);
lean_inc(v_snd_2704_);
lean_dec_ref(v_____s_2703_);
v_fst_2705_ = lean_ctor_get(v_snd_2704_, 0);
v_snd_2706_ = lean_ctor_get(v_snd_2704_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_snd_2704_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2708_ = v_snd_2704_;
v_isShared_2709_ = v_isSharedCheck_2714_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_snd_2706_);
lean_inc(v_fst_2705_);
lean_dec(v_snd_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2714_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_fst_2705_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_snd_2706_);
v___x_2711_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_apply_2(v_toPure_2702_, lean_box(0), v___x_2711_);
return v___x_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2715_, lean_object* v_____do__lift_2716_){
_start:
{
lean_object* v_resolutionOrder_2717_; lean_object* v___x_2718_; 
v_resolutionOrder_2717_ = lean_ctor_get(v_____do__lift_2716_, 0);
lean_inc_ref(v_resolutionOrder_2717_);
lean_dec_ref(v_____do__lift_2716_);
v___x_2718_ = lean_apply_2(v_toPure_2715_, lean_box(0), v_resolutionOrder_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_structName_2725_, lean_object* v_parentNames_2726_, uint8_t v_relaxed_2727_){
_start:
{
lean_object* v_toApplicative_2728_; lean_object* v_toBind_2729_; lean_object* v_toPure_2730_; lean_object* v___f_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___f_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_toApplicative_2728_ = lean_ctor_get(v_inst_2723_, 0);
v_toBind_2729_ = lean_ctor_get(v_inst_2723_, 1);
lean_inc_n(v_toBind_2729_, 3);
v_toPure_2730_ = lean_ctor_get(v_toApplicative_2728_, 1);
v___f_2731_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc_n(v_toPure_2730_, 3);
v___f_2732_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2732_, 0, v_toPure_2730_);
lean_inc_ref_n(v_inst_2723_, 2);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2733_, 0, v_inst_2723_);
lean_closure_set(v___f_2733_, 1, v_inst_2724_);
lean_closure_set(v___f_2733_, 2, v_toBind_2729_);
lean_closure_set(v___f_2733_, 3, v___f_2732_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2734_, 0, v_toPure_2730_);
v___x_2735_ = lean_box(v_relaxed_2727_);
lean_inc_ref(v_parentNames_2726_);
v___f_2736_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 10, 9);
lean_closure_set(v___f_2736_, 0, v_toPure_2730_);
lean_closure_set(v___f_2736_, 1, v___f_2731_);
lean_closure_set(v___f_2736_, 2, v___x_2735_);
lean_closure_set(v___f_2736_, 3, v_parentNames_2726_);
lean_closure_set(v___f_2736_, 4, v_inst_2723_);
lean_closure_set(v___f_2736_, 5, v_toBind_2729_);
lean_closure_set(v___f_2736_, 6, v_structName_2725_);
lean_closure_set(v___f_2736_, 7, v___f_2734_);
lean_closure_set(v___f_2736_, 8, v___f_2731_);
v_sz_2737_ = lean_array_size(v_parentNames_2726_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2723_, v___f_2733_, v_sz_2737_, v___x_2738_, v_parentNames_2726_);
v___x_2740_ = lean_apply_4(v_toBind_2729_, lean_box(0), lean_box(0), v___x_2739_, v___f_2736_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2741_, lean_object* v_toPure_2742_, lean_object* v___f_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, uint8_t v_relaxed_2746_, lean_object* v_toBind_2747_, lean_object* v___f_2748_, lean_object* v_env_2749_){
_start:
{
lean_object* v___x_2750_; 
lean_inc_ref(v_env_2749_);
v___x_2750_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2749_, v_structName_2741_);
if (lean_obj_tag(v___x_2750_) == 1)
{
lean_object* v_val_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref(v_env_2749_);
lean_dec(v___f_2748_);
lean_dec(v_toBind_2747_);
lean_dec_ref(v_inst_2745_);
lean_dec_ref(v_inst_2744_);
lean_dec_ref(v___f_2743_);
lean_dec(v_structName_2741_);
v_val_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_val_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_val_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_apply_2(v_toPure_2742_, lean_box(0), v___x_2753_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v_parentNames_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec(v___x_2750_);
lean_dec(v_toPure_2742_);
lean_inc(v_structName_2741_);
v___x_2755_ = l_Lean_getStructureParentInfo(v_env_2749_, v_structName_2741_);
v___x_2756_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2757_ = lean_array_size(v___x_2755_);
v___x_2758_ = ((size_t)0ULL);
v_parentNames_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2756_, v___f_2743_, v_sz_2757_, v___x_2758_, v___x_2755_);
v___x_2760_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2744_, v_inst_2745_, v_structName_2741_, v_parentNames_2759_, v_relaxed_2746_);
v___x_2761_ = lean_apply_4(v_toBind_2747_, lean_box(0), lean_box(0), v___x_2760_, v___f_2748_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2762_, lean_object* v_toPure_2763_, lean_object* v___f_2764_, lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_relaxed_2767_, lean_object* v_toBind_2768_, lean_object* v___f_2769_, lean_object* v_env_2770_){
_start:
{
uint8_t v_relaxed_boxed_2771_; lean_object* v_res_2772_; 
v_relaxed_boxed_2771_ = lean_unbox(v_relaxed_2767_);
v_res_2772_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2762_, v_toPure_2763_, v___f_2764_, v_inst_2765_, v_inst_2766_, v_relaxed_boxed_2771_, v_toBind_2768_, v___f_2769_, v_env_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_structName_2775_, uint8_t v_relaxed_2776_){
_start:
{
lean_object* v_toApplicative_2777_; lean_object* v_toBind_2778_; lean_object* v_getEnv_2779_; lean_object* v_toPure_2780_; lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; 
v_toApplicative_2777_ = lean_ctor_get(v_inst_2773_, 0);
v_toBind_2778_ = lean_ctor_get(v_inst_2773_, 1);
lean_inc_n(v_toBind_2778_, 3);
v_getEnv_2779_ = lean_ctor_get(v_inst_2774_, 0);
lean_inc(v_getEnv_2779_);
v_toPure_2780_ = lean_ctor_get(v_toApplicative_2777_, 1);
lean_inc_n(v_toPure_2780_, 2);
v___f_2781_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2775_);
lean_inc_ref(v_inst_2774_);
v___f_2782_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2782_, 0, v_toPure_2780_);
lean_closure_set(v___f_2782_, 1, v_inst_2774_);
lean_closure_set(v___f_2782_, 2, v_structName_2775_);
lean_closure_set(v___f_2782_, 3, v_toBind_2778_);
v___x_2783_ = lean_box(v_relaxed_2776_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2784_, 0, v_structName_2775_);
lean_closure_set(v___f_2784_, 1, v_toPure_2780_);
lean_closure_set(v___f_2784_, 2, v___f_2781_);
lean_closure_set(v___f_2784_, 3, v_inst_2773_);
lean_closure_set(v___f_2784_, 4, v_inst_2774_);
lean_closure_set(v___f_2784_, 5, v___x_2783_);
lean_closure_set(v___f_2784_, 6, v_toBind_2778_);
lean_closure_set(v___f_2784_, 7, v___f_2782_);
v___x_2785_ = lean_apply_4(v_toBind_2778_, lean_box(0), lean_box(0), v_getEnv_2779_, v___f_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2786_, lean_object* v_inst_2787_, lean_object* v_toBind_2788_, lean_object* v___f_2789_, lean_object* v_parentName_2790_){
_start:
{
uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = 1;
v___x_2792_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2786_, v_inst_2787_, v_parentName_2790_, v___x_2791_);
v___x_2793_ = lean_apply_4(v_toBind_2788_, lean_box(0), lean_box(0), v___x_2792_, v___f_2789_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_structName_2796_, lean_object* v_relaxed_2797_){
_start:
{
uint8_t v_relaxed_boxed_2798_; lean_object* v_res_2799_; 
v_relaxed_boxed_2798_ = lean_unbox(v_relaxed_2797_);
v_res_2799_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2794_, v_inst_2795_, v_structName_2796_, v_relaxed_boxed_2798_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_structName_2802_, lean_object* v_parentNames_2803_, lean_object* v_relaxed_2804_){
_start:
{
uint8_t v_relaxed_boxed_2805_; lean_object* v_res_2806_; 
v_relaxed_boxed_2805_ = lean_unbox(v_relaxed_2804_);
v_res_2806_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2800_, v_inst_2801_, v_structName_2802_, v_parentNames_2803_, v_relaxed_boxed_2805_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_structName_2810_, uint8_t v_relaxed_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2808_, v_inst_2809_, v_structName_2810_, v_relaxed_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_structName_2816_, lean_object* v_relaxed_2817_){
_start:
{
uint8_t v_relaxed_boxed_2818_; lean_object* v_res_2819_; 
v_relaxed_boxed_2818_ = lean_unbox(v_relaxed_2817_);
v_res_2819_ = l_Lean_computeStructureResolutionOrder(v_m_2813_, v_inst_2814_, v_inst_2815_, v_structName_2816_, v_relaxed_boxed_2818_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2820_, lean_object* v_inst_2821_, lean_object* v_inst_2822_, lean_object* v_structName_2823_, lean_object* v_parentNames_2824_, uint8_t v_relaxed_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2821_, v_inst_2822_, v_structName_2823_, v_parentNames_2824_, v_relaxed_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_structName_2830_, lean_object* v_parentNames_2831_, lean_object* v_relaxed_2832_){
_start:
{
uint8_t v_relaxed_boxed_2833_; lean_object* v_res_2834_; 
v_relaxed_boxed_2833_ = lean_unbox(v_relaxed_2832_);
v_res_2834_ = l_Lean_mergeStructureResolutionOrders(v_m_2827_, v_inst_2828_, v_inst_2829_, v_structName_2830_, v_parentNames_2831_, v_relaxed_boxed_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2835_){
_start:
{
lean_object* v_resolutionOrder_2836_; 
v_resolutionOrder_2836_ = lean_ctor_get(v_x_2835_, 0);
lean_inc_ref(v_resolutionOrder_2836_);
return v_resolutionOrder_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2837_);
lean_dec_ref(v_x_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_structName_2842_){
_start:
{
lean_object* v_toApplicative_2843_; lean_object* v_toFunctor_2844_; lean_object* v_map_2845_; lean_object* v___f_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_toApplicative_2843_ = lean_ctor_get(v_inst_2840_, 0);
v_toFunctor_2844_ = lean_ctor_get(v_toApplicative_2843_, 0);
v_map_2845_ = lean_ctor_get(v_toFunctor_2844_, 0);
lean_inc(v_map_2845_);
v___f_2846_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2847_ = 1;
v___x_2848_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2840_, v_inst_2841_, v_structName_2842_, v___x_2847_);
v___x_2849_ = lean_apply_4(v_map_2845_, lean_box(0), lean_box(0), v___f_2846_, v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_structName_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2851_, v_inst_2852_, v_structName_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2855_, lean_object* v_structName_2856_, lean_object* v_x_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Array_erase___redArg(v___x_2855_, v_x_2857_, v_structName_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_structName_2861_){
_start:
{
lean_object* v_toApplicative_2862_; lean_object* v_toFunctor_2863_; lean_object* v_map_2864_; lean_object* v___x_2865_; lean_object* v___f_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_toApplicative_2862_ = lean_ctor_get(v_inst_2859_, 0);
v_toFunctor_2863_ = lean_ctor_get(v_toApplicative_2862_, 0);
v_map_2864_ = lean_ctor_get(v_toFunctor_2863_, 0);
lean_inc(v_map_2864_);
v___x_2865_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2861_);
v___f_2866_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2866_, 0, v___x_2865_);
lean_closure_set(v___f_2866_, 1, v_structName_2861_);
v___x_2867_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2859_, v_inst_2860_, v_structName_2861_);
v___x_2868_ = lean_apply_4(v_map_2864_, lean_box(0), lean_box(0), v___f_2866_, v___x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_structName_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_getAllParentStructures___redArg(v_inst_2870_, v_inst_2871_, v_structName_2872_);
return v___x_2873_;
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
