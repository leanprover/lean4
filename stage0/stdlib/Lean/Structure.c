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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedStructureInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureInfo_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureInfo;
LEAN_EXPORT uint8_t l_Lean_StructureInfo_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_StructureInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_structureExt;
static const lean_array_object l_Lean_instInhabitedStructureDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureDescr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr_default = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_StructureFieldInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_registerStructure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerStructure___closed__0 = (const lean_object*)&l_Lean_registerStructure___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_getStructureInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getStructureInfo_x3f___closed__0 = (const lean_object*)&l_Lean_getStructureInfo_x3f___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionOrderResult;
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
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2_value;
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
static lean_object* _init_l_Lean_instInhabitedStructureInfo_default___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureInfo_default(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_instInhabitedStructureInfo_default___closed__1, &l_Lean_instInhabitedStructureInfo_default___closed__1_once, _init_l_Lean_instInhabitedStructureInfo_default___closed__1);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureInfo(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_instInhabitedStructureInfo_default;
return v___x_172_;
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
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_acc_289_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_298_, v_keys_299_, v_vals_300_, v_i_301_, v_acc_302_);
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
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_304_, v_es_307_, v___x_312_, v___x_313_, v_x_306_);
return v___x_314_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_309_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_304_, v_es_307_, v___x_315_, v___x_316_, v_x_306_);
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
v___x_321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_304_, v_ks_318_, v_vs_319_, v___x_320_, v_x_306_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object* v_f_322_, lean_object* v_as_323_, size_t v_i_324_, size_t v_stop_325_, lean_object* v_b_326_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_f_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_339_, v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_375_, lean_object* v_lo_376_, lean_object* v_hi_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_lt(v_lo_376_, v_hi_377_);
if (v___x_378_ == 0)
{
lean_dec(v_lo_376_);
return v_as_375_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; uint8_t v___x_383_; 
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_376_);
v___x_380_ = l_Array_qpartition___redArg(v_as_375_, v___x_379_, v_lo_376_, v_hi_377_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_nat_dec_le(v_hi_377_, v_fst_381_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_snd_382_, v_lo_376_, v_fst_381_);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_fst_381_, v___x_385_);
lean_dec(v_fst_381_);
v_as_375_ = v___x_384_;
v_lo_376_ = v___x_386_;
goto _start;
}
else
{
lean_dec(v_fst_381_);
lean_dec(v_lo_376_);
return v_snd_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_388_, lean_object* v_lo_389_, lean_object* v_hi_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_as_388_, v_lo_389_, v_hi_390_);
lean_dec(v_hi_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_392_, lean_object* v_x_393_, lean_object* v_s_394_, uint8_t v_x_395_){
_start:
{
lean_object* v_snd_396_; lean_object* v___x_397_; size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_snd_396_ = lean_ctor_get(v_s_394_, 1);
v___x_397_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_396_);
v_sz_398_ = lean_array_size(v___x_397_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_398_, v___x_399_, v___x_397_);
v___x_401_ = lean_array_get_size(v___x_400_);
v___x_402_ = lean_nat_dec_eq(v___x_401_, v___x_392_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___y_406_; uint8_t v___x_410_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_sub(v___x_401_, v___x_403_);
v___x_410_ = lean_nat_dec_le(v___x_392_, v___x_404_);
if (v___x_410_ == 0)
{
lean_dec(v___x_392_);
lean_inc(v___x_404_);
v___y_406_ = v___x_404_;
goto v___jp_405_;
}
else
{
v___y_406_ = v___x_392_;
goto v___jp_405_;
}
v___jp_405_:
{
uint8_t v___x_407_; 
v___x_407_ = lean_nat_dec_le(v___y_406_, v___x_404_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec(v___x_404_);
lean_inc(v___y_406_);
v___x_408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_400_, v___y_406_, v___y_406_);
lean_dec(v___y_406_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_400_, v___y_406_, v___x_404_);
lean_dec(v___x_404_);
return v___x_409_;
}
}
}
else
{
lean_dec(v___x_392_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_411_, lean_object* v_x_412_, lean_object* v_s_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_x_1506__boxed_415_; lean_object* v_res_416_; 
v_x_1506__boxed_415_ = lean_unbox(v_x_414_);
v_res_416_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_411_, v_x_412_, v_s_413_, v_x_1506__boxed_415_);
lean_dec_ref(v_s_413_);
lean_dec_ref(v_x_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_snd_419_; lean_object* v___x_420_; size_t v_sz_421_; size_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_snd_419_ = lean_ctor_get(v_x_418_, 1);
v___x_420_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_419_);
v_sz_421_ = lean_array_size(v___x_420_);
v___x_422_ = ((size_t)0ULL);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_421_, v___x_422_, v___x_420_);
v___x_424_ = lean_array_get_size(v___x_423_);
v___x_425_ = lean_nat_dec_eq(v___x_424_, v___x_417_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___y_429_; uint8_t v___x_433_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_sub(v___x_424_, v___x_426_);
v___x_433_ = lean_nat_dec_le(v___x_417_, v___x_427_);
if (v___x_433_ == 0)
{
lean_dec(v___x_417_);
lean_inc(v___x_427_);
v___y_429_ = v___x_427_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___x_417_;
goto v___jp_428_;
}
v___jp_428_:
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_le(v___y_429_, v___x_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v___x_427_);
lean_inc(v___y_429_);
v___x_431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_423_, v___y_429_, v___y_429_);
lean_dec(v___y_429_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_423_, v___y_429_, v___x_427_);
lean_dec(v___x_427_);
return v___x_432_;
}
}
}
else
{
lean_dec(v___x_417_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_434_, v_x_435_);
lean_dec_ref(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_ks_441_; lean_object* v_vs_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_466_; 
v_ks_441_ = lean_ctor_get(v_x_437_, 0);
v_vs_442_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_466_ == 0)
{
v___x_444_ = v_x_437_;
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_vs_442_);
lean_inc(v_ks_441_);
lean_dec(v_x_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_array_get_size(v_ks_441_);
v___x_447_ = lean_nat_dec_lt(v_x_438_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec(v_x_438_);
v___x_448_ = lean_array_push(v_ks_441_, v_x_439_);
v___x_449_ = lean_array_push(v_vs_442_, v_x_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_449_);
lean_ctor_set(v___x_444_, 0, v___x_448_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v_k_x27_453_; uint8_t v___x_454_; 
v_k_x27_453_ = lean_array_fget_borrowed(v_ks_441_, v_x_438_);
v___x_454_ = lean_name_eq(v_x_439_, v_k_x27_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
if (v_isShared_445_ == 0)
{
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_ks_441_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_vs_442_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_x_438_, v___x_457_);
lean_dec(v_x_438_);
v_x_437_ = v___x_456_;
v_x_438_ = v___x_458_;
goto _start;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_array_fset(v_ks_441_, v_x_438_, v_x_439_);
v___x_462_ = lean_array_fset(v_vs_442_, v_x_438_, v_x_440_);
lean_dec(v_x_438_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_462_);
lean_ctor_set(v___x_444_, 0, v___x_461_);
v___x_464_ = v___x_444_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(lean_object* v_n_467_, lean_object* v_k_468_, lean_object* v_v_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_n_467_, v___x_470_, v_k_468_, v_v_469_);
return v___x_471_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_472_; uint64_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1723u);
v___x_473_ = lean_uint64_of_nat(v___x_472_);
return v___x_473_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; 
v___x_474_ = ((size_t)5ULL);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_shift_left(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; 
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_479_ = lean_usize_sub(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_es_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v_j_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_es_486_ = lean_ctor_get(v_x_481_, 0);
v___x_487_ = ((size_t)5ULL);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_490_ = lean_usize_land(v_x_482_, v___x_489_);
v_j_491_ = lean_usize_to_nat(v___x_490_);
v___x_492_ = lean_array_get_size(v_es_486_);
v___x_493_ = lean_nat_dec_lt(v_j_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v_j_491_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
return v_x_481_;
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_es_486_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_x_481_, 0);
lean_dec(v_unused_531_);
v___x_495_ = v_x_481_;
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_481_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_v_497_; lean_object* v___x_498_; lean_object* v_xs_x27_499_; lean_object* v___y_501_; 
v_v_497_ = lean_array_fget(v_es_486_, v_j_491_);
v___x_498_ = lean_box(0);
v_xs_x27_499_ = lean_array_fset(v_es_486_, v_j_491_, v___x_498_);
switch(lean_obj_tag(v_v_497_))
{
case 0:
{
lean_object* v_key_506_; lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_key_506_ = lean_ctor_get(v_v_497_, 0);
v_val_507_ = lean_ctor_get(v_v_497_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_509_ = v_v_497_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_inc(v_key_506_);
lean_dec(v_v_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_name_eq(v_x_484_, v_key_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_509_);
v___x_512_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_506_, v_val_507_, v_x_484_, v_x_485_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___y_501_ = v___x_513_;
goto v___jp_500_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_val_507_);
lean_dec(v_key_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_x_485_);
lean_ctor_set(v___x_509_, 0, v_x_484_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_x_484_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_x_485_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_501_ = v___x_515_;
goto v___jp_500_;
}
}
}
}
case 1:
{
lean_object* v_node_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_node_518_ = lean_ctor_get(v_v_497_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_528_ == 0)
{
v___x_520_ = v_v_497_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_node_518_);
lean_dec(v_v_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_usize_shift_right(v_x_482_, v___x_487_);
v___x_523_ = lean_usize_add(v_x_483_, v___x_488_);
v___x_524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_node_518_, v___x_522_, v___x_523_, v_x_484_, v_x_485_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_501_ = v___x_526_;
goto v___jp_500_;
}
}
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_x_484_);
lean_ctor_set(v___x_529_, 1, v_x_485_);
v___y_501_ = v___x_529_;
goto v___jp_500_;
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_array_fset(v_xs_x27_499_, v_j_491_, v___y_501_);
lean_dec(v_j_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_553_; 
v_ks_532_ = lean_ctor_get(v_x_481_, 0);
v_vs_533_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_553_ == 0)
{
v___x_535_ = v_x_481_;
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_481_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_vs_533_);
v___x_538_ = v_reuseFailAlloc_552_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v_newNode_539_; uint8_t v___y_541_; size_t v___x_547_; uint8_t v___x_548_; 
v_newNode_539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v___x_538_, v_x_484_, v_x_485_);
v___x_547_ = ((size_t)7ULL);
v___x_548_ = lean_usize_dec_le(v___x_547_, v_x_483_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_539_);
v___x_550_ = lean_unsigned_to_nat(4u);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___x_548_;
goto v___jp_540_;
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v_ks_542_; lean_object* v_vs_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_ks_542_ = lean_ctor_get(v_newNode_539_, 0);
lean_inc_ref(v_ks_542_);
v_vs_543_ = lean_ctor_get(v_newNode_539_, 1);
lean_inc_ref(v_vs_543_);
lean_dec_ref(v_newNode_539_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2);
v___x_546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_x_483_, v_ks_542_, v_vs_543_, v___x_544_, v___x_545_);
lean_dec_ref(v_vs_543_);
lean_dec_ref(v_ks_542_);
return v___x_546_;
}
else
{
return v_newNode_539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(size_t v_depth_554_, lean_object* v_keys_555_, lean_object* v_vals_556_, lean_object* v_i_557_, lean_object* v_entries_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_keys_555_);
v___x_560_ = lean_nat_dec_lt(v_i_557_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_i_557_);
return v_entries_558_;
}
else
{
lean_object* v_k_561_; lean_object* v_v_562_; uint64_t v___y_564_; 
v_k_561_ = lean_array_fget_borrowed(v_keys_555_, v_i_557_);
v_v_562_ = lean_array_fget_borrowed(v_vals_556_, v_i_557_);
if (lean_obj_tag(v_k_561_) == 0)
{
uint64_t v___x_575_; 
v___x_575_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_564_ = v___x_575_;
goto v___jp_563_;
}
else
{
uint64_t v_hash_576_; 
v_hash_576_ = lean_ctor_get_uint64(v_k_561_, sizeof(void*)*2);
v___y_564_ = v_hash_576_;
goto v___jp_563_;
}
v___jp_563_:
{
size_t v_h_565_; size_t v___x_566_; lean_object* v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v_h_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_h_565_ = lean_uint64_to_usize(v___y_564_);
v___x_566_ = ((size_t)5ULL);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_sub(v_depth_554_, v___x_568_);
v___x_570_ = lean_usize_mul(v___x_566_, v___x_569_);
v_h_571_ = lean_usize_shift_right(v_h_565_, v___x_570_);
v___x_572_ = lean_nat_add(v_i_557_, v___x_567_);
lean_dec(v_i_557_);
lean_inc(v_v_562_);
lean_inc(v_k_561_);
v___x_573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_entries_558_, v_h_571_, v_depth_554_, v_k_561_, v_v_562_);
v_i_557_ = v___x_572_;
v_entries_558_ = v___x_573_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_depth_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_entries_581_){
_start:
{
size_t v_depth_boxed_582_; lean_object* v_res_583_; 
v_depth_boxed_582_ = lean_unbox_usize(v_depth_577_);
lean_dec(v_depth_577_);
v_res_583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_boxed_582_, v_keys_578_, v_vals_579_, v_i_580_, v_entries_581_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
size_t v_x_1672__boxed_589_; size_t v_x_1673__boxed_590_; lean_object* v_res_591_; 
v_x_1672__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_x_1673__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_584_, v_x_1672__boxed_589_, v_x_1673__boxed_590_, v_x_587_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint64_t v___y_596_; 
if (lean_obj_tag(v_x_593_) == 0)
{
uint64_t v___x_600_; 
v___x_600_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_596_ = v___x_600_;
goto v___jp_595_;
}
else
{
uint64_t v_hash_601_; 
v_hash_601_ = lean_ctor_get_uint64(v_x_593_, sizeof(void*)*2);
v___y_596_ = v_hash_601_;
goto v___jp_595_;
}
v___jp_595_:
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_uint64_to_usize(v___y_596_);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_592_, v___x_597_, v___x_598_, v_x_593_, v_x_594_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_602_, lean_object* v_x_603_, lean_object* v_e_604_){
_start:
{
lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v_snd_605_ = lean_ctor_get(v_x_603_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_x_603_, 0);
lean_dec(v_unused_615_);
v___x_607_ = v_x_603_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_dec(v_x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_structName_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v_structName_609_ = lean_ctor_get(v_e_604_, 0);
lean_inc(v_structName_609_);
v___x_610_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_605_, v_structName_609_, v_e_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_610_);
lean_ctor_set(v___x_607_, 0, v___x_602_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_622_, lean_object* v_x_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_627_, v_x_628_, v___y_629_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_x_628_);
return v_res_631_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_664_; lean_object* v___f_665_; 
v___x_664_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_665_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_665_, 0, v___x_664_);
return v___f_665_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_666_; lean_object* v___f_667_; 
v___x_666_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_667_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_667_, 0, v___x_666_);
return v___f_667_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_668_ = lean_box(0);
v___x_669_ = lean_box(2);
v___f_670_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_671_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_672_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_673_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_674_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_675_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_676_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___f_674_);
lean_ctor_set(v___x_676_, 2, v___f_673_);
lean_ctor_set(v___x_676_, 3, v___f_672_);
lean_ctor_set(v___x_676_, 4, v___f_671_);
lean_ctor_set(v___x_676_, 5, v___f_670_);
lean_ctor_set(v___x_676_, 6, v___x_669_);
lean_ctor_set(v___x_676_, 7, v___x_668_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___f_677_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_678_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___f_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_682_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_685_, lean_object* v_m_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_688_, lean_object* v_m_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_688_, v_m_689_);
lean_dec_ref(v_m_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_691_, lean_object* v_as_692_, lean_object* v_lo_693_, lean_object* v_hi_694_, lean_object* v_w_695_, lean_object* v_hlo_696_, lean_object* v_hhi_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_as_692_, v_lo_693_, v_hi_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_699_, lean_object* v_as_700_, lean_object* v_lo_701_, lean_object* v_hi_702_, lean_object* v_w_703_, lean_object* v_hlo_704_, lean_object* v_hhi_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_699_, v_as_700_, v_lo_701_, v_hi_702_, v_w_703_, v_hlo_704_, v_hhi_705_);
lean_dec(v_hi_702_);
lean_dec(v_n_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_708_, v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_712_, lean_object* v_00_u03b2_713_, lean_object* v_map_714_, lean_object* v_f_715_, lean_object* v_init_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_714_, v_f_715_, v_init_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_718_, lean_object* v_00_u03b2_719_, lean_object* v_map_720_, lean_object* v_f_721_, lean_object* v_init_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_718_, v_00_u03b2_719_, v_map_720_, v_f_721_, v_init_722_);
lean_dec_ref(v_map_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, size_t v_x_726_, size_t v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_725_, v_x_726_, v_x_727_, v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
size_t v_x_2073__boxed_737_; size_t v_x_2074__boxed_738_; lean_object* v_res_739_; 
v_x_2073__boxed_737_ = lean_unbox_usize(v_x_733_);
lean_dec(v_x_733_);
v_x_2074__boxed_738_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_res_739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_731_, v_x_732_, v_x_2073__boxed_737_, v_x_2074__boxed_738_, v_x_735_, v_x_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_740_, lean_object* v_f_741_, lean_object* v_init_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_741_, v_map_740_, v_init_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_744_, lean_object* v_f_745_, lean_object* v_init_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_744_, v_f_745_, v_init_746_);
lean_dec_ref(v_map_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_748_, lean_object* v_00_u03b2_749_, lean_object* v_map_750_, lean_object* v_f_751_, lean_object* v_init_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_751_, v_map_750_, v_init_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_754_, lean_object* v_00_u03b2_755_, lean_object* v_map_756_, lean_object* v_f_757_, lean_object* v_init_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_754_, v_00_u03b2_755_, v_map_756_, v_f_757_, v_init_758_);
lean_dec_ref(v_map_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object* v_00_u03b2_760_, lean_object* v_n_761_, lean_object* v_k_762_, lean_object* v_v_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v_n_761_, v_k_762_, v_v_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(lean_object* v_00_u03b2_765_, size_t v_depth_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_heq_769_, lean_object* v_i_770_, lean_object* v_entries_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_766_, v_keys_767_, v_vals_768_, v_i_770_, v_entries_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_773_, lean_object* v_depth_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_heq_777_, lean_object* v_i_778_, lean_object* v_entries_779_){
_start:
{
size_t v_depth_boxed_780_; lean_object* v_res_781_; 
v_depth_boxed_780_ = lean_unbox_usize(v_depth_774_);
lean_dec(v_depth_774_);
v_res_781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(v_00_u03b2_773_, v_depth_boxed_780_, v_keys_775_, v_vals_776_, v_heq_777_, v_i_778_, v_entries_779_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_782_, lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_f_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_785_, v_x_786_, v_x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_789_, lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_f_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_789_, v_00_u03b1_790_, v_00_u03b2_791_, v_f_792_, v_x_793_, v_x_794_);
lean_dec_ref(v_x_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_00_u03c3_804_, lean_object* v_f_805_, lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_805_, v_as_806_, v_i_807_, v_stop_808_, v_b_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_00_u03c3_813_, lean_object* v_f_814_, lean_object* v_as_815_, lean_object* v_i_816_, lean_object* v_stop_817_, lean_object* v_b_818_){
_start:
{
size_t v_i_boxed_819_; size_t v_stop_boxed_820_; lean_object* v_res_821_; 
v_i_boxed_819_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_stop_boxed_820_ = lean_unbox_usize(v_stop_817_);
lean_dec(v_stop_817_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_811_, v_00_u03b2_812_, v_00_u03c3_813_, v_f_814_, v_as_815_, v_i_boxed_819_, v_stop_boxed_820_, v_b_818_);
lean_dec_ref(v_as_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03c3_822_, lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_f_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_acc_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_825_, v_keys_826_, v_vals_827_, v_i_829_, v_acc_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03c3_832_, lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_f_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_acc_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03c3_832_, v_00_u03b1_833_, v_00_u03b2_834_, v_f_835_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_acc_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_849_, size_t v_i_850_, lean_object* v_bs_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_852_ == 0)
{
return v_bs_851_;
}
else
{
lean_object* v_v_853_; lean_object* v_fieldName_854_; lean_object* v___x_855_; lean_object* v_bs_x27_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v_v_853_ = lean_array_uget_borrowed(v_bs_851_, v_i_850_);
v_fieldName_854_ = lean_ctor_get(v_v_853_, 0);
lean_inc(v_fieldName_854_);
v___x_855_ = lean_unsigned_to_nat(0u);
v_bs_x27_856_ = lean_array_uset(v_bs_851_, v_i_850_, v___x_855_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_850_, v___x_857_);
v___x_859_ = lean_array_uset(v_bs_x27_856_, v_i_850_, v_fieldName_854_);
v_i_850_ = v___x_858_;
v_bs_851_ = v___x_859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_861_, lean_object* v_i_862_, lean_object* v_bs_863_){
_start:
{
size_t v_sz_boxed_864_; size_t v_i_boxed_865_; lean_object* v_res_866_; 
v_sz_boxed_864_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v_i_boxed_865_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_864_, v_i_boxed_865_, v_bs_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_as_868_, lean_object* v_lo_869_, lean_object* v_hi_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_lt(v_lo_869_, v_hi_870_);
if (v___x_871_ == 0)
{
lean_dec(v_lo_869_);
return v_as_868_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; uint8_t v___x_876_; 
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0));
lean_inc(v_lo_869_);
v___x_873_ = l_Array_qpartition___redArg(v_as_868_, v___x_872_, v_lo_869_, v_hi_870_);
v_fst_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_875_);
lean_dec_ref(v___x_873_);
v___x_876_ = lean_nat_dec_le(v_hi_870_, v_fst_874_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_snd_875_, v_lo_869_, v_fst_874_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_fst_874_, v___x_878_);
lean_dec(v_fst_874_);
v_as_868_ = v___x_877_;
v_lo_869_ = v___x_879_;
goto _start;
}
else
{
lean_dec(v_fst_874_);
lean_dec(v_lo_869_);
return v_snd_875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_as_881_, lean_object* v_lo_882_, lean_object* v_hi_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_881_, v_lo_882_, v_hi_883_);
lean_dec(v_hi_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_887_, lean_object* v_e_888_){
_start:
{
lean_object* v_structName_889_; lean_object* v_fields_890_; lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___y_896_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_structName_889_ = lean_ctor_get(v_e_888_, 0);
lean_inc(v_structName_889_);
v_fields_890_ = lean_ctor_get(v_e_888_, 1);
lean_inc_ref(v_fields_890_);
lean_dec_ref(v_e_888_);
v___x_891_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_892_ = lean_array_size(v_fields_890_);
v___x_893_ = ((size_t)0ULL);
lean_inc_ref(v_fields_890_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_892_, v___x_893_, v_fields_890_);
v___x_916_ = lean_array_get_size(v_fields_890_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_nat_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___y_922_; uint8_t v___x_924_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_sub(v___x_916_, v___x_919_);
v___x_924_ = lean_nat_dec_le(v___x_917_, v___x_920_);
if (v___x_924_ == 0)
{
lean_inc(v___x_920_);
v___y_922_ = v___x_920_;
goto v___jp_921_;
}
else
{
v___y_922_ = v___x_917_;
goto v___jp_921_;
}
v___jp_921_:
{
uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_le(v___y_922_, v___x_920_);
if (v___x_923_ == 0)
{
lean_dec(v___x_920_);
lean_inc(v___y_922_);
v___y_913_ = v___y_922_;
v___y_914_ = v___y_922_;
goto v___jp_912_;
}
else
{
v___y_913_ = v___y_922_;
v___y_914_ = v___x_920_;
goto v___jp_912_;
}
}
}
else
{
v___y_896_ = v_fields_890_;
goto v___jp_895_;
}
v___jp_895_:
{
lean_object* v_toEnvExtension_897_; lean_object* v_asyncMode_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_908_; 
v_toEnvExtension_897_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_toEnvExtension_897_);
v_asyncMode_898_ = lean_ctor_get(v_toEnvExtension_897_, 2);
v_isSharedCheck_908_ = !lean_is_exclusive(v_toEnvExtension_897_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; 
v_unused_909_ = lean_ctor_get(v_toEnvExtension_897_, 3);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_toEnvExtension_897_, 1);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_toEnvExtension_897_, 0);
lean_dec(v_unused_911_);
v___x_900_ = v_toEnvExtension_897_;
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_asyncMode_898_);
lean_dec(v_toEnvExtension_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 3, v___x_902_);
lean_ctor_set(v___x_900_, 2, v___y_896_);
lean_ctor_set(v___x_900_, 1, v___x_894_);
lean_ctor_set(v___x_900_, 0, v_structName_889_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_structName_889_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___y_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v___x_902_);
v___x_904_ = v_reuseFailAlloc_907_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_box(0);
v___x_906_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_891_, v_env_887_, v___x_904_, v_asyncMode_898_, v___x_905_);
lean_dec(v_asyncMode_898_);
return v___x_906_;
}
}
}
v___jp_912_:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_fields_890_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
v___y_896_ = v___x_915_;
goto v___jp_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_925_, lean_object* v_as_926_, lean_object* v_lo_927_, lean_object* v_hi_928_, lean_object* v_w_929_, lean_object* v_hlo_930_, lean_object* v_hhi_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_926_, v_lo_927_, v_hi_928_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_933_, lean_object* v_as_934_, lean_object* v_lo_935_, lean_object* v_hi_936_, lean_object* v_w_937_, lean_object* v_hlo_938_, lean_object* v_hhi_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_933_, v_as_934_, v_lo_935_, v_hi_936_, v_w_937_, v_hlo_938_, v_hhi_939_);
lean_dec(v_hi_936_);
lean_dec(v_n_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_941_, lean_object* v_parentInfo_942_, lean_object* v___x_943_, lean_object* v_asyncMode_944_, lean_object* v___x_945_, lean_object* v_env_946_){
_start:
{
lean_object* v_structName_947_; lean_object* v_fieldNames_948_; lean_object* v_fieldInfo_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_structName_947_ = lean_ctor_get(v_val_941_, 0);
v_fieldNames_948_ = lean_ctor_get(v_val_941_, 1);
v_fieldInfo_949_ = lean_ctor_get(v_val_941_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_val_941_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v_val_941_, 3);
lean_dec(v_unused_958_);
v___x_951_ = v_val_941_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_fieldInfo_949_);
lean_inc(v_fieldNames_948_);
lean_inc(v_structName_947_);
lean_dec(v_val_941_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 3, v_parentInfo_942_);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_structName_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_fieldNames_948_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_fieldInfo_949_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_parentInfo_942_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_943_, v_env_946_, v___x_954_, v_asyncMode_944_, v___x_945_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_959_, lean_object* v_parentInfo_960_, lean_object* v___x_961_, lean_object* v_asyncMode_962_, lean_object* v___x_963_, lean_object* v_env_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_setStructureParents___redArg___lam__0(v_val_959_, v_parentInfo_960_, v___x_961_, v_asyncMode_962_, v___x_963_, v_env_964_);
lean_dec(v_asyncMode_962_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v_structName_975_, lean_object* v_parentInfo_976_, lean_object* v_modifyEnv_977_, lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_____do__lift_980_){
_start:
{
lean_object* v___x_981_; lean_object* v_toEnvExtension_982_; lean_object* v_asyncMode_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1002_; 
v___x_981_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_toEnvExtension_982_);
v_asyncMode_983_ = lean_ctor_get(v_toEnvExtension_982_, 2);
lean_inc(v_asyncMode_983_);
lean_dec_ref(v_toEnvExtension_982_);
v___x_984_ = lean_box(0);
v___x_985_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_972_, v___x_981_, v_____do__lift_980_, v_asyncMode_983_, v___x_984_);
v_snd_986_ = lean_ctor_get(v___x_985_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_1003_);
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; 
lean_inc(v_structName_975_);
v___x_990_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_973_, v___x_974_, v_snd_986_, v_structName_975_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___f_992_; lean_object* v___x_993_; 
lean_del_object(v___x_988_);
lean_dec_ref(v_inst_979_);
lean_dec_ref(v_inst_978_);
lean_dec(v_structName_975_);
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref(v___x_990_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_992_, 0, v_val_991_);
lean_closure_set(v___f_992_, 1, v_parentInfo_976_);
lean_closure_set(v___f_992_, 2, v___x_981_);
lean_closure_set(v___f_992_, 3, v_asyncMode_983_);
lean_closure_set(v___f_992_, 4, v___x_984_);
v___x_993_ = lean_apply_1(v_modifyEnv_977_, v___f_992_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_dec(v___x_990_);
lean_dec(v_asyncMode_983_);
lean_dec(v_modifyEnv_977_);
lean_dec_ref(v_parentInfo_976_);
v___x_994_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_995_ = l_Lean_MessageData_ofName(v_structName_975_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 7);
lean_ctor_set(v___x_988_, 1, v___x_995_);
lean_ctor_set(v___x_988_, 0, v___x_994_);
v___x_997_ = v___x_988_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_throwError___redArg(v_inst_978_, v_inst_979_, v___x_999_);
return v___x_1000_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_structName_1012_, lean_object* v_parentInfo_1013_){
_start:
{
lean_object* v_toBind_1014_; lean_object* v_getEnv_1015_; lean_object* v_modifyEnv_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; 
v_toBind_1014_ = lean_ctor_get(v_inst_1009_, 1);
lean_inc(v_toBind_1014_);
v_getEnv_1015_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc(v_getEnv_1015_);
v_modifyEnv_1016_ = lean_ctor_get(v_inst_1010_, 1);
lean_inc(v_modifyEnv_1016_);
lean_dec_ref(v_inst_1010_);
v___x_1017_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1018_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1019_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1020_, 0, v___x_1019_);
lean_closure_set(v___f_1020_, 1, v___x_1017_);
lean_closure_set(v___f_1020_, 2, v___x_1018_);
lean_closure_set(v___f_1020_, 3, v_structName_1012_);
lean_closure_set(v___f_1020_, 4, v_parentInfo_1013_);
lean_closure_set(v___f_1020_, 5, v_modifyEnv_1016_);
lean_closure_set(v___f_1020_, 6, v_inst_1009_);
lean_closure_set(v___f_1020_, 7, v_inst_1011_);
v___x_1021_ = lean_apply_4(v_toBind_1014_, lean_box(0), lean_box(0), v_getEnv_1015_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_structName_1026_, lean_object* v_parentInfo_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_setStructureParents___redArg(v_inst_1023_, v_inst_1024_, v_inst_1025_, v_structName_1026_, v_parentInfo_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1029_, lean_object* v_k_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_m_1035_; lean_object* v_a_1036_; uint8_t v___x_1037_; 
v___x_1033_ = lean_nat_add(v_x_1031_, v_x_1032_);
v___x_1034_ = lean_unsigned_to_nat(1u);
v_m_1035_ = lean_nat_shiftr(v___x_1033_, v___x_1034_);
lean_dec(v___x_1033_);
v_a_1036_ = lean_array_fget_borrowed(v_as_1029_, v_m_1035_);
v___x_1037_ = l_Lean_StructureInfo_lt(v_a_1036_, v_k_1030_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; 
lean_dec(v_x_1032_);
v___x_1038_ = l_Lean_StructureInfo_lt(v_k_1030_, v_a_1036_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec(v_m_1035_);
lean_dec(v_x_1031_);
lean_inc(v_a_1036_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1036_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_nat_dec_eq(v_m_1035_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_nat_sub(v_m_1035_, v___x_1034_);
lean_dec(v_m_1035_);
v___x_1043_ = lean_nat_dec_lt(v___x_1042_, v_x_1031_);
if (v___x_1043_ == 0)
{
v_x_1032_ = v___x_1042_;
goto _start;
}
else
{
lean_object* v___x_1045_; 
lean_dec(v___x_1042_);
lean_dec(v_x_1031_);
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
}
else
{
lean_object* v___x_1046_; 
lean_dec(v_m_1035_);
lean_dec(v_x_1031_);
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
}
}
else
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
lean_dec(v_x_1031_);
v___x_1047_ = lean_nat_add(v_m_1035_, v___x_1034_);
lean_dec(v_m_1035_);
v___x_1048_ = lean_nat_dec_le(v___x_1047_, v_x_1032_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v___x_1047_);
lean_dec(v_x_1032_);
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
else
{
v_x_1031_ = v___x_1047_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1051_, lean_object* v_k_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1051_, v_k_1052_, v_x_1053_, v_x_1054_);
lean_dec_ref(v_k_1052_);
lean_dec_ref(v_as_1051_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1056_, lean_object* v_vals_1057_, lean_object* v_i_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_keys_1056_);
v___x_1061_ = lean_nat_dec_lt(v_i_1058_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_dec(v_i_1058_);
v___x_1062_ = lean_box(0);
return v___x_1062_;
}
else
{
lean_object* v_k_x27_1063_; uint8_t v___x_1064_; 
v_k_x27_1063_ = lean_array_fget_borrowed(v_keys_1056_, v_i_1058_);
v___x_1064_ = lean_name_eq(v_k_1059_, v_k_x27_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_add(v_i_1058_, v___x_1065_);
lean_dec(v_i_1058_);
v_i_1058_ = v___x_1066_;
goto _start;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_array_fget_borrowed(v_vals_1057_, v_i_1058_);
lean_dec(v_i_1058_);
lean_inc(v___x_1068_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1070_, v_vals_1071_, v_i_1072_, v_k_1073_);
lean_dec(v_k_1073_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1075_, size_t v_x_1076_, lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v_es_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1099_; 
v_es_1078_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1080_ = v_x_1075_;
v_isShared_1081_ = v_isSharedCheck_1099_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_es_1078_);
lean_dec(v_x_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1099_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; lean_object* v_j_1086_; lean_object* v___x_1087_; 
v___x_1082_ = lean_box(2);
v___x_1083_ = ((size_t)5ULL);
v___x_1084_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1085_ = lean_usize_land(v_x_1076_, v___x_1084_);
v_j_1086_ = lean_usize_to_nat(v___x_1085_);
v___x_1087_ = lean_array_get(v___x_1082_, v_es_1078_, v_j_1086_);
lean_dec(v_j_1086_);
lean_dec_ref(v_es_1078_);
switch(lean_obj_tag(v___x_1087_))
{
case 0:
{
lean_object* v_key_1088_; lean_object* v_val_1089_; uint8_t v___x_1090_; 
v_key_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_key_1088_);
v_val_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_val_1089_);
lean_dec_ref(v___x_1087_);
v___x_1090_ = lean_name_eq(v_x_1077_, v_key_1088_);
lean_dec(v_key_1088_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec(v_val_1089_);
lean_del_object(v___x_1080_);
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
else
{
lean_object* v___x_1093_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 1);
lean_ctor_set(v___x_1080_, 0, v_val_1089_);
v___x_1093_ = v___x_1080_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_val_1089_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
case 1:
{
lean_object* v_node_1095_; size_t v___x_1096_; 
lean_del_object(v___x_1080_);
v_node_1095_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_node_1095_);
lean_dec_ref(v___x_1087_);
v___x_1096_ = lean_usize_shift_right(v_x_1076_, v___x_1083_);
v_x_1075_ = v_node_1095_;
v_x_1076_ = v___x_1096_;
goto _start;
}
default: 
{
lean_object* v___x_1098_; 
lean_del_object(v___x_1080_);
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_ks_1100_; lean_object* v_vs_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_ks_1100_ = lean_ctor_get(v_x_1075_, 0);
lean_inc_ref(v_ks_1100_);
v_vs_1101_ = lean_ctor_get(v_x_1075_, 1);
lean_inc_ref(v_vs_1101_);
lean_dec_ref(v_x_1075_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1100_, v_vs_1101_, v___x_1102_, v_x_1077_);
lean_dec_ref(v_vs_1101_);
lean_dec_ref(v_ks_1100_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
size_t v_x_395__boxed_1107_; lean_object* v_res_1108_; 
v_x_395__boxed_1107_ = lean_unbox_usize(v_x_1105_);
lean_dec(v_x_1105_);
v_res_1108_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1104_, v_x_395__boxed_1107_, v_x_1106_);
lean_dec(v_x_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint64_t v___y_1112_; 
if (lean_obj_tag(v_x_1110_) == 0)
{
uint64_t v___x_1115_; 
v___x_1115_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_1112_ = v___x_1115_;
goto v___jp_1111_;
}
else
{
uint64_t v_hash_1116_; 
v_hash_1116_ = lean_ctor_get_uint64(v_x_1110_, sizeof(void*)*2);
v___y_1112_ = v_hash_1116_;
goto v___jp_1111_;
}
v___jp_1111_:
{
size_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_uint64_to_usize(v___y_1112_);
v___x_1114_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1109_, v___x_1113_, v_x_1110_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1117_, v_x_1118_);
lean_dec(v_x_1118_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1122_, lean_object* v_structName_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1125_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1122_, v_structName_1123_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v_toEnvExtension_1127_; lean_object* v_asyncMode_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_snd_1131_; lean_object* v___x_1132_; 
v___x_1126_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_toEnvExtension_1127_);
v_asyncMode_1128_ = lean_ctor_get(v_toEnvExtension_1127_, 2);
lean_inc(v_asyncMode_1128_);
lean_dec_ref(v_toEnvExtension_1127_);
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1124_, v___x_1126_, v_env_1122_, v_asyncMode_1128_, v___x_1129_);
lean_dec(v_asyncMode_1128_);
v_snd_1131_ = lean_ctor_get(v___x_1130_, 1);
lean_inc(v_snd_1131_);
lean_dec(v___x_1130_);
v___x_1132_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1131_, v_structName_1123_);
lean_dec(v_structName_1123_);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_val_1133_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_val_1133_);
lean_dec_ref(v___x_1125_);
v___x_1134_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1135_ = 0;
v___x_1136_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1124_, v___x_1134_, v_env_1122_, v_val_1133_, v___x_1135_);
lean_dec(v_val_1133_);
lean_dec_ref(v_env_1122_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_array_get_size(v___x_1136_);
v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v___x_1136_);
lean_dec(v_structName_1123_);
v___x_1140_ = lean_box(0);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_sub(v___x_1138_, v___x_1141_);
v___x_1143_ = lean_nat_dec_le(v___x_1137_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec(v___x_1142_);
lean_dec_ref(v___x_1136_);
lean_dec(v_structName_1123_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1146_, 0, v_structName_1123_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
lean_ctor_set(v___x_1146_, 3, v___x_1145_);
v___x_1147_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1136_, v___x_1146_, v___x_1137_, v___x_1142_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1136_);
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1149_, v_x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1152_, v_x_1153_, v_x_1154_);
lean_dec(v_x_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1156_, lean_object* v_k_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1156_, v_k_1157_, v_x_1158_, v_x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1162_, lean_object* v_k_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1162_, v_k_1163_, v_x_1164_, v_x_1165_, v_x_1166_);
lean_dec_ref(v_k_1163_);
lean_dec_ref(v_as_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1168_, lean_object* v_x_1169_, size_t v_x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1169_, v_x_1170_, v_x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
size_t v_x_545__boxed_1177_; lean_object* v_res_1178_; 
v_x_545__boxed_1177_ = lean_unbox_usize(v_x_1175_);
lean_dec(v_x_1175_);
v_res_1178_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1173_, v_x_1174_, v_x_545__boxed_1177_, v_x_1176_);
lean_dec(v_x_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1179_, lean_object* v_keys_1180_, lean_object* v_vals_1181_, lean_object* v_heq_1182_, lean_object* v_i_1183_, lean_object* v_k_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1180_, v_vals_1181_, v_i_1183_, v_k_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1186_, lean_object* v_keys_1187_, lean_object* v_vals_1188_, lean_object* v_heq_1189_, lean_object* v_i_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1186_, v_keys_1187_, v_vals_1188_, v_heq_1189_, v_i_1190_, v_k_1191_);
lean_dec(v_k_1191_);
lean_dec_ref(v_vals_1188_);
lean_dec_ref(v_keys_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = l_Lean_instInhabitedStructureInfo_default;
v___x_1195_ = lean_panic_fn(v___x_1194_, v_msg_1193_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1200_ = lean_unsigned_to_nat(4u);
v___x_1201_ = lean_unsigned_to_nat(139u);
v___x_1202_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1203_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1205_, lean_object* v_structName_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_getStructureInfo_x3f(v_env_1205_, v_structName_1206_);
if (lean_obj_tag(v___x_1207_) == 1)
{
lean_object* v_val_1208_; 
v_val_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_val_1208_);
lean_dec_ref(v___x_1207_);
return v_val_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v___x_1207_);
v___x_1209_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1210_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1209_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1213_ = lean_panic_fn(v___x_1212_, v_msg_1211_);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1215_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1216_ = lean_unsigned_to_nat(9u);
v___x_1217_ = lean_unsigned_to_nat(154u);
v___x_1218_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1219_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1220_ = l_mkPanicMessageWithDecl(v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1223_ = lean_unsigned_to_nat(11u);
v___x_1224_ = lean_unsigned_to_nat(153u);
v___x_1225_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1226_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1227_ = l_mkPanicMessageWithDecl(v___x_1226_, v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1228_, lean_object* v_constName_1229_){
_start:
{
uint8_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = 0;
lean_inc_ref(v_env_1228_);
v___x_1237_ = l_Lean_Environment_find_x3f(v_env_1228_, v_constName_1229_, v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref(v___x_1237_);
if (lean_obj_tag(v_val_1238_) == 5)
{
lean_object* v_val_1239_; lean_object* v_ctors_1240_; 
v_val_1239_ = lean_ctor_get(v_val_1238_, 0);
lean_inc_ref(v_val_1239_);
lean_dec_ref(v_val_1238_);
v_ctors_1240_ = lean_ctor_get(v_val_1239_, 4);
lean_inc(v_ctors_1240_);
lean_dec_ref(v_val_1239_);
if (lean_obj_tag(v_ctors_1240_) == 1)
{
lean_object* v_tail_1241_; 
v_tail_1241_ = lean_ctor_get(v_ctors_1240_, 1);
if (lean_obj_tag(v_tail_1241_) == 0)
{
lean_object* v_head_1242_; lean_object* v___x_1243_; 
v_head_1242_ = lean_ctor_get(v_ctors_1240_, 0);
lean_inc(v_head_1242_);
lean_dec_ref(v_ctors_1240_);
v___x_1243_ = l_Lean_Environment_find_x3f(v_env_1228_, v_head_1242_, v___x_1236_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1243_);
if (lean_obj_tag(v_val_1244_) == 6)
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v_val_1244_, 0);
lean_inc_ref(v_val_1245_);
lean_dec_ref(v_val_1244_);
return v_val_1245_;
}
else
{
lean_dec(v_val_1244_);
goto v___jp_1233_;
}
}
else
{
lean_dec(v___x_1243_);
goto v___jp_1233_;
}
}
else
{
lean_dec_ref(v_ctors_1240_);
lean_dec_ref(v_env_1228_);
goto v___jp_1230_;
}
}
else
{
lean_dec(v_ctors_1240_);
lean_dec_ref(v_env_1228_);
goto v___jp_1230_;
}
}
else
{
lean_dec(v_val_1238_);
lean_dec_ref(v_env_1228_);
goto v___jp_1230_;
}
}
else
{
lean_dec(v___x_1237_);
lean_dec_ref(v_env_1228_);
goto v___jp_1230_;
}
v___jp_1230_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1232_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1231_);
return v___x_1232_;
}
v___jp_1233_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1235_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1234_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1246_, lean_object* v_structName_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v_fieldNames_1249_; 
v___x_1248_ = l_Lean_getStructureInfo(v_env_1246_, v_structName_1247_);
v_fieldNames_1249_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_fieldNames_1249_);
lean_dec_ref(v___x_1248_);
return v_fieldNames_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1250_, lean_object* v_structName_1251_, lean_object* v_fieldName_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_getStructureInfo_x3f(v_env_1250_, v_structName_1251_);
if (lean_obj_tag(v___x_1253_) == 1)
{
lean_object* v_val_1254_; lean_object* v_fieldInfo_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v___x_1253_);
v_fieldInfo_1255_ = lean_ctor_get(v_val_1254_, 2);
lean_inc_ref(v_fieldInfo_1255_);
lean_dec(v_val_1254_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v_fieldInfo_1255_);
v___x_1258_ = lean_nat_dec_lt(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref(v_fieldInfo_1255_);
lean_dec(v_fieldName_1252_);
v___x_1259_ = lean_box(0);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_sub(v___x_1257_, v___x_1260_);
v___x_1262_ = lean_nat_dec_le(v___x_1256_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec(v___x_1261_);
lean_dec_ref(v_fieldInfo_1255_);
lean_dec(v_fieldName_1252_);
v___x_1263_ = lean_box(0);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_box(0);
v___x_1266_ = 0;
v___x_1267_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1267_, 0, v_fieldName_1252_);
lean_ctor_set(v___x_1267_, 1, v___x_1264_);
lean_ctor_set(v___x_1267_, 2, v___x_1265_);
lean_ctor_set(v___x_1267_, 3, v___x_1265_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*4, v___x_1266_);
v___x_1268_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1255_, v___x_1267_, v___x_1256_, v___x_1261_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v_fieldInfo_1255_);
return v___x_1268_;
}
}
}
else
{
lean_object* v___x_1269_; 
lean_dec(v___x_1253_);
lean_dec(v_fieldName_1252_);
v___x_1269_ = lean_box(0);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1270_, lean_object* v_structName_1271_, lean_object* v_fieldName_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_getFieldInfo_x3f(v_env_1270_, v_structName_1271_, v_fieldName_1272_);
if (lean_obj_tag(v___x_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v_subobject_x3f_1275_; 
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref(v___x_1273_);
v_subobject_x3f_1275_ = lean_ctor_get(v_val_1274_, 2);
lean_inc(v_subobject_x3f_1275_);
lean_dec(v_val_1274_);
return v_subobject_x3f_1275_;
}
else
{
lean_object* v___x_1276_; 
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1277_, lean_object* v_structName_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v_parentInfo_1280_; 
v___x_1279_ = l_Lean_getStructureInfo(v_env_1277_, v_structName_1278_);
v_parentInfo_1280_ = lean_ctor_get(v___x_1279_, 3);
lean_inc_ref(v_parentInfo_1280_);
lean_dec_ref(v___x_1279_);
return v_parentInfo_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1281_, lean_object* v_structName_1282_, lean_object* v_as_1283_, size_t v_i_1284_, size_t v_stop_1285_, lean_object* v_b_1286_){
_start:
{
lean_object* v___y_1288_; uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_eq(v_i_1284_, v_stop_1285_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_array_uget_borrowed(v_as_1283_, v_i_1284_);
lean_inc(v___x_1293_);
lean_inc(v_structName_1282_);
lean_inc_ref(v_env_1281_);
v___x_1294_ = l_Lean_isSubobjectField_x3f(v_env_1281_, v_structName_1282_, v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
v___y_1288_ = v_b_1286_;
goto v___jp_1287_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1296_; 
v_val_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1295_);
lean_dec_ref(v___x_1294_);
v___x_1296_ = lean_array_push(v_b_1286_, v_val_1295_);
v___y_1288_ = v___x_1296_;
goto v___jp_1287_;
}
}
else
{
lean_dec(v_structName_1282_);
lean_dec_ref(v_env_1281_);
return v_b_1286_;
}
v___jp_1287_:
{
size_t v___x_1289_; size_t v___x_1290_; 
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1284_, v___x_1289_);
v_i_1284_ = v___x_1290_;
v_b_1286_ = v___y_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1297_, lean_object* v_structName_1298_, lean_object* v_as_1299_, lean_object* v_i_1300_, lean_object* v_stop_1301_, lean_object* v_b_1302_){
_start:
{
size_t v_i_boxed_1303_; size_t v_stop_boxed_1304_; lean_object* v_res_1305_; 
v_i_boxed_1303_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_stop_boxed_1304_ = lean_unbox_usize(v_stop_1301_);
lean_dec(v_stop_1301_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1297_, v_structName_1298_, v_as_1299_, v_i_boxed_1303_, v_stop_boxed_1304_, v_b_1302_);
lean_dec_ref(v_as_1299_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1306_, lean_object* v_structName_1307_, lean_object* v_as_1308_, lean_object* v_start_1309_, lean_object* v_stop_1310_){
_start:
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1312_ = lean_nat_dec_lt(v_start_1309_, v_stop_1310_);
if (v___x_1312_ == 0)
{
lean_dec(v_structName_1307_);
lean_dec_ref(v_env_1306_);
return v___x_1311_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_array_get_size(v_as_1308_);
v___x_1314_ = lean_nat_dec_le(v_stop_1310_, v___x_1313_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_lt(v_start_1309_, v___x_1313_);
if (v___x_1315_ == 0)
{
lean_dec(v_structName_1307_);
lean_dec_ref(v_env_1306_);
return v___x_1311_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_usize_of_nat(v_start_1309_);
v___x_1317_ = lean_usize_of_nat(v___x_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1306_, v_structName_1307_, v_as_1308_, v___x_1316_, v___x_1317_, v___x_1311_);
return v___x_1318_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_usize_of_nat(v_start_1309_);
v___x_1320_ = lean_usize_of_nat(v_stop_1310_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1306_, v_structName_1307_, v_as_1308_, v___x_1319_, v___x_1320_, v___x_1311_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1322_, lean_object* v_structName_1323_, lean_object* v_as_1324_, lean_object* v_start_1325_, lean_object* v_stop_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1322_, v_structName_1323_, v_as_1324_, v_start_1325_, v_stop_1326_);
lean_dec(v_stop_1326_);
lean_dec(v_start_1325_);
lean_dec_ref(v_as_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1328_, lean_object* v_structName_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_structName_1329_);
lean_inc_ref(v_env_1328_);
v___x_1330_ = l_Lean_getStructureFields(v_env_1328_, v_structName_1329_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_array_get_size(v___x_1330_);
v___x_1333_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1328_, v_structName_1329_, v___x_1330_, v___x_1331_, v___x_1332_);
lean_dec_ref(v___x_1330_);
return v___x_1333_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1334_, lean_object* v_as_1335_, size_t v_i_1336_, size_t v_stop_1337_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_eq(v_i_1336_, v_stop_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = lean_array_uget_borrowed(v_as_1335_, v_i_1336_);
v___x_1340_ = lean_name_eq(v_a_1334_, v___x_1339_);
if (v___x_1340_ == 0)
{
size_t v___x_1341_; size_t v___x_1342_; 
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1336_, v___x_1341_);
v_i_1336_ = v___x_1342_;
goto _start;
}
else
{
return v___x_1340_;
}
}
else
{
uint8_t v___x_1344_; 
v___x_1344_ = 0;
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1345_, lean_object* v_as_1346_, lean_object* v_i_1347_, lean_object* v_stop_1348_){
_start:
{
size_t v_i_boxed_1349_; size_t v_stop_boxed_1350_; uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_i_boxed_1349_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_stop_boxed_1350_ = lean_unbox_usize(v_stop_1348_);
lean_dec(v_stop_1348_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1345_, v_as_1346_, v_i_boxed_1349_, v_stop_boxed_1350_);
lean_dec_ref(v_as_1346_);
lean_dec(v_a_1345_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_array_get_size(v_as_1353_);
v___x_1357_ = lean_nat_dec_lt(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
return v___x_1357_;
}
else
{
if (v___x_1357_ == 0)
{
return v___x_1357_;
}
else
{
size_t v___x_1358_; size_t v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_of_nat(v___x_1356_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1354_, v_as_1353_, v___x_1358_, v___x_1359_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_res_1363_; lean_object* v_r_1364_; 
v_res_1363_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_as_1361_);
v_r_1364_ = lean_box(v_res_1363_);
return v_r_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1368_, lean_object* v_structName_1369_, lean_object* v_fieldName_1370_){
_start:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
lean_inc(v_structName_1369_);
lean_inc_ref(v_env_1368_);
v___x_1371_ = l_Lean_getStructureFields(v_env_1368_, v_structName_1369_);
v___x_1372_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1371_, v_fieldName_1370_);
lean_dec_ref(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; lean_object* v_fst_1379_; 
lean_inc_ref(v_env_1368_);
v___x_1373_ = l_Lean_getStructureSubobjects(v_env_1368_, v_structName_1369_);
v___x_1374_ = lean_box(0);
v___x_1375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1376_ = lean_array_size(v___x_1373_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1368_, v_fieldName_1370_, v___x_1373_, v_sz_1376_, v___x_1377_, v___x_1375_);
lean_dec_ref(v___x_1373_);
v_fst_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fst_1379_);
lean_dec_ref(v___x_1378_);
if (lean_obj_tag(v_fst_1379_) == 0)
{
return v___x_1374_;
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v_fst_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref(v_fst_1379_);
return v_val_1380_;
}
}
else
{
lean_object* v___x_1381_; 
lean_dec_ref(v_env_1368_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_structName_1369_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1382_, lean_object* v_fieldName_1383_, lean_object* v_as_1384_, size_t v_sz_1385_, size_t v_i_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1386_, v_sz_1385_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v_env_1382_);
return v_b_1387_;
}
else
{
lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_b_1387_);
v___x_1389_ = lean_box(0);
v_a_1390_ = lean_array_uget_borrowed(v_as_1384_, v_i_1386_);
lean_inc(v_a_1390_);
lean_inc_ref(v_env_1382_);
v___x_1391_ = l_Lean_findField_x3f(v_env_1382_, v_a_1390_, v_fieldName_1383_);
if (lean_obj_tag(v___x_1391_) == 1)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_env_1382_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1389_);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; 
lean_dec(v___x_1391_);
v___x_1394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1386_, v___x_1395_);
v_i_1386_ = v___x_1396_;
v_b_1387_ = v___x_1394_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1398_, lean_object* v_fieldName_1399_, lean_object* v_as_1400_, lean_object* v_sz_1401_, lean_object* v_i_1402_, lean_object* v_b_1403_){
_start:
{
size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1401_);
lean_dec(v_sz_1401_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1398_, v_fieldName_1399_, v_as_1400_, v_sz_boxed_1404_, v_i_boxed_1405_, v_b_1403_);
lean_dec_ref(v_as_1400_);
lean_dec(v_fieldName_1399_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1407_, lean_object* v_structName_1408_, lean_object* v_fieldName_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_findField_x3f(v_env_1407_, v_structName_1408_, v_fieldName_1409_);
lean_dec(v_fieldName_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1414_, lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1419_ == 0)
{
return v_b_1418_;
}
else
{
lean_object* v_a_1420_; lean_object* v_projFn_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
lean_dec_ref(v_b_1418_);
v_a_1420_ = lean_array_uget_borrowed(v_as_1415_, v_i_1417_);
v_projFn_1421_ = lean_ctor_get(v_a_1420_, 1);
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Lean_Name_isSuffixOf(v_projName_1414_, v_projFn_1421_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; 
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_i_1417_, v___x_1425_);
v_i_1417_ = v___x_1426_;
v_b_1418_ = v___x_1424_;
goto _start;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_inc(v_a_1420_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1420_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1422_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1431_, lean_object* v_as_1432_, lean_object* v_sz_1433_, lean_object* v_i_1434_, lean_object* v_b_1435_){
_start:
{
size_t v_sz_boxed_1436_; size_t v_i_boxed_1437_; lean_object* v_res_1438_; 
v_sz_boxed_1436_ = lean_unbox_usize(v_sz_1433_);
lean_dec(v_sz_1433_);
v_i_boxed_1437_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1431_, v_as_1432_, v_sz_boxed_1436_, v_i_boxed_1437_, v_b_1435_);
lean_dec_ref(v_as_1432_);
lean_dec(v_projName_1431_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1439_, lean_object* v_projName_1440_, lean_object* v_structName_1441_, lean_object* v_a_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_NameSet_contains(v_a_1442_, v_structName_1441_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1468_; size_t v_sz_1469_; size_t v___x_1470_; lean_object* v___x_1471_; lean_object* v_fst_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1489_; 
lean_inc(v_structName_1441_);
lean_inc_ref(v_env_1439_);
v___x_1444_ = l_Lean_getStructureParentInfo(v_env_1439_, v_structName_1441_);
v___x_1468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1469_ = lean_array_size(v___x_1444_);
v___x_1470_ = ((size_t)0ULL);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1440_, v___x_1444_, v_sz_1469_, v___x_1470_, v___x_1468_);
v_fst_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v___x_1471_, 1);
lean_dec(v_unused_1490_);
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1489_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_fst_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1489_;
goto v_resetjp_1473_;
}
v___jp_1445_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; size_t v_sz_1449_; size_t v___x_1450_; lean_object* v___x_1451_; lean_object* v_fst_1452_; lean_object* v_fst_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1466_; 
v___x_1446_ = l_Lean_NameSet_insert(v_a_1442_, v_structName_1441_);
v___x_1447_ = lean_box(0);
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1449_ = lean_array_size(v___x_1444_);
v___x_1450_ = ((size_t)0ULL);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1439_, v_projName_1440_, v___x_1444_, v_sz_1449_, v___x_1450_, v___x_1448_, v___x_1446_);
lean_dec_ref(v___x_1444_);
v_fst_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_fst_1452_);
v_fst_1453_ = lean_ctor_get(v_fst_1452_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_fst_1452_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_fst_1452_, 1);
lean_dec(v_unused_1467_);
v___x_1455_ = v_fst_1452_;
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_fst_1453_);
lean_dec(v_fst_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
if (lean_obj_tag(v_fst_1453_) == 0)
{
lean_object* v_snd_1457_; lean_object* v___x_1459_; 
v_snd_1457_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_snd_1457_);
lean_dec_ref(v___x_1451_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_snd_1457_);
lean_ctor_set(v___x_1455_, 0, v___x_1447_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_snd_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
else
{
lean_object* v_snd_1461_; lean_object* v_val_1462_; lean_object* v___x_1464_; 
v_snd_1461_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_snd_1461_);
lean_dec_ref(v___x_1451_);
v_val_1462_ = lean_ctor_get(v_fst_1453_, 0);
lean_inc(v_val_1462_);
lean_dec_ref(v_fst_1453_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_snd_1461_);
lean_ctor_set(v___x_1455_, 0, v_val_1462_);
v___x_1464_ = v___x_1455_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_val_1462_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_snd_1461_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
v_resetjp_1473_:
{
if (lean_obj_tag(v_fst_1472_) == 0)
{
lean_del_object(v___x_1474_);
goto v___jp_1445_;
}
else
{
lean_object* v_val_1476_; 
v_val_1476_ = lean_ctor_get(v_fst_1472_, 0);
lean_inc(v_val_1476_);
lean_dec_ref(v_fst_1472_);
if (lean_obj_tag(v_val_1476_) == 1)
{
lean_object* v_val_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1444_);
lean_dec(v_structName_1441_);
lean_dec_ref(v_env_1439_);
v_val_1477_ = lean_ctor_get(v_val_1476_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1479_ = v_val_1476_;
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_val_1477_);
lean_dec(v_val_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_structName_1481_; lean_object* v___x_1483_; 
v_structName_1481_ = lean_ctor_get(v_val_1477_, 0);
lean_inc(v_structName_1481_);
lean_dec(v_val_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v_structName_1481_);
v___x_1483_ = v___x_1479_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_structName_1481_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v_a_1442_);
lean_ctor_set(v___x_1474_, 0, v___x_1483_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1442_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_dec(v_val_1476_);
lean_del_object(v___x_1474_);
goto v___jp_1445_;
}
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_structName_1441_);
lean_dec_ref(v_env_1439_);
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v_a_1442_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1493_, lean_object* v_projName_1494_, lean_object* v_as_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref(v_env_1493_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1498_);
lean_ctor_set(v___x_1501_, 1, v___y_1499_);
return v___x_1501_;
}
else
{
lean_object* v_a_1502_; lean_object* v_structName_1503_; lean_object* v___x_1504_; lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v_b_1498_);
v_a_1502_ = lean_array_uget_borrowed(v_as_1495_, v_i_1497_);
v_structName_1503_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_structName_1503_);
lean_inc_ref(v_env_1493_);
v___x_1504_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1493_, v_projName_1494_, v_structName_1503_, v___y_1499_);
v_fst_1505_ = lean_ctor_get(v___x_1504_, 0);
v_snd_1506_ = lean_ctor_get(v___x_1504_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1508_ = v___x_1504_;
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1505_);
lean_dec(v___x_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_box(0);
if (lean_obj_tag(v_fst_1505_) == 1)
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_dec_ref(v_env_1493_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_fst_1505_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v___x_1510_);
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1510_);
v___x_1513_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_snd_1506_);
return v___x_1514_;
}
}
else
{
lean_object* v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; 
lean_del_object(v___x_1508_);
lean_dec(v_fst_1505_);
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1497_, v___x_1517_);
v_i_1497_ = v___x_1518_;
v_b_1498_ = v___x_1516_;
v___y_1499_ = v_snd_1506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1521_, lean_object* v_projName_1522_, lean_object* v_as_1523_, lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1521_, v_projName_1522_, v_as_1523_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1526_, v___y_1527_);
lean_dec_ref(v_as_1523_);
lean_dec(v_projName_1522_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1531_, lean_object* v_projName_1532_, lean_object* v_structName_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1531_, v_projName_1532_, v_structName_1533_, v_a_1534_);
lean_dec(v_projName_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1536_, lean_object* v_structName_1537_, lean_object* v_projName_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_fst_1541_; 
v___x_1539_ = l_Lean_NameSet_empty;
v___x_1540_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1536_, v_projName_1538_, v_structName_1537_, v___x_1539_);
v_fst_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_fst_1541_);
lean_dec_ref(v___x_1540_);
return v_fst_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1542_, lean_object* v_structName_1543_, lean_object* v_projName_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_findParentProjStruct_x3f(v_env_1542_, v_structName_1543_, v_projName_1544_);
lean_dec(v_projName_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1551_ = l_Lean_Name_append(v_structCtorName_1549_, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1552_, lean_object* v_structName_1553_, uint8_t v_includeSubobjectFields_1554_, lean_object* v_as_1555_, size_t v_i_1556_, size_t v_stop_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v___y_1560_; uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_eq(v_i_1556_, v_stop_1557_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_array_uget_borrowed(v_as_1555_, v_i_1556_);
lean_inc(v___x_1565_);
lean_inc(v_structName_1553_);
lean_inc_ref(v_env_1552_);
v___x_1566_ = l_Lean_isSubobjectField_x3f(v_env_1552_, v_structName_1553_, v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1567_; 
lean_inc(v___x_1565_);
v___x_1567_ = lean_array_push(v_b_1558_, v___x_1565_);
v___y_1560_ = v___x_1567_;
goto v___jp_1559_;
}
else
{
if (v_includeSubobjectFields_1554_ == 0)
{
lean_object* v_val_1568_; lean_object* v___x_1569_; 
v_val_1568_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1568_);
lean_dec_ref(v___x_1566_);
lean_inc_ref(v_env_1552_);
v___x_1569_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1552_, v_val_1568_, v_b_1558_, v_includeSubobjectFields_1554_);
v___y_1560_ = v___x_1569_;
goto v___jp_1559_;
}
else
{
lean_object* v_val_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_val_1570_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1566_);
lean_inc(v___x_1565_);
v___x_1571_ = lean_array_push(v_b_1558_, v___x_1565_);
lean_inc_ref(v_env_1552_);
v___x_1572_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1552_, v_val_1570_, v___x_1571_, v_includeSubobjectFields_1554_);
v___y_1560_ = v___x_1572_;
goto v___jp_1559_;
}
}
}
else
{
lean_dec(v_structName_1553_);
lean_dec_ref(v_env_1552_);
return v_b_1558_;
}
v___jp_1559_:
{
size_t v___x_1561_; size_t v___x_1562_; 
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_add(v_i_1556_, v___x_1561_);
v_i_1556_ = v___x_1562_;
v_b_1558_ = v___y_1560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1573_, lean_object* v_structName_1574_, lean_object* v_fullNames_1575_, uint8_t v_includeSubobjectFields_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
lean_inc(v_structName_1574_);
lean_inc_ref(v_env_1573_);
v___x_1577_ = l_Lean_getStructureFields(v_env_1573_, v_structName_1574_);
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = lean_array_get_size(v___x_1577_);
v___x_1580_ = lean_nat_dec_lt(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1577_);
lean_dec(v_structName_1574_);
lean_dec_ref(v_env_1573_);
return v_fullNames_1575_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_le(v___x_1579_, v___x_1579_);
if (v___x_1581_ == 0)
{
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1577_);
lean_dec(v_structName_1574_);
lean_dec_ref(v_env_1573_);
return v_fullNames_1575_;
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1579_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1573_, v_structName_1574_, v_includeSubobjectFields_1576_, v___x_1577_, v___x_1582_, v___x_1583_, v_fullNames_1575_);
lean_dec_ref(v___x_1577_);
return v___x_1584_;
}
}
else
{
size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = lean_usize_of_nat(v___x_1579_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1573_, v_structName_1574_, v_includeSubobjectFields_1576_, v___x_1577_, v___x_1585_, v___x_1586_, v_fullNames_1575_);
lean_dec_ref(v___x_1577_);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1588_, lean_object* v_structName_1589_, lean_object* v_fullNames_1590_, lean_object* v_includeSubobjectFields_1591_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1592_; lean_object* v_res_1593_; 
v_includeSubobjectFields_boxed_1592_ = lean_unbox(v_includeSubobjectFields_1591_);
v_res_1593_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1588_, v_structName_1589_, v_fullNames_1590_, v_includeSubobjectFields_boxed_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1594_, lean_object* v_structName_1595_, lean_object* v_includeSubobjectFields_1596_, lean_object* v_as_1597_, lean_object* v_i_1598_, lean_object* v_stop_1599_, lean_object* v_b_1600_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1601_; size_t v_i_boxed_1602_; size_t v_stop_boxed_1603_; lean_object* v_res_1604_; 
v_includeSubobjectFields_boxed_1601_ = lean_unbox(v_includeSubobjectFields_1596_);
v_i_boxed_1602_ = lean_unbox_usize(v_i_1598_);
lean_dec(v_i_1598_);
v_stop_boxed_1603_ = lean_unbox_usize(v_stop_1599_);
lean_dec(v_stop_1599_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1594_, v_structName_1595_, v_includeSubobjectFields_boxed_1601_, v_as_1597_, v_i_boxed_1602_, v_stop_boxed_1603_, v_b_1600_);
lean_dec_ref(v_as_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1605_, lean_object* v_structName_1606_, uint8_t v_includeSubobjectFields_1607_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1609_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1605_, v_structName_1606_, v___x_1608_, v_includeSubobjectFields_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1610_, lean_object* v_structName_1611_, lean_object* v_includeSubobjectFields_1612_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1613_; lean_object* v_res_1614_; 
v_includeSubobjectFields_boxed_1613_ = lean_unbox(v_includeSubobjectFields_1612_);
v_res_1614_ = l_Lean_getStructureFieldsFlattened(v_env_1610_, v_structName_1611_, v_includeSubobjectFields_boxed_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1615_, lean_object* v_constName_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_getStructureInfo_x3f(v_env_1615_, v_constName_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
else
{
uint8_t v___x_1619_; 
lean_dec_ref(v___x_1617_);
v___x_1619_ = 1;
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1620_, lean_object* v_constName_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l_Lean_isStructure(v_env_1620_, v_constName_1621_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1624_, lean_object* v_structName_1625_, lean_object* v_fieldName_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_getFieldInfo_x3f(v_env_1624_, v_structName_1625_, v_fieldName_1626_);
if (lean_obj_tag(v___x_1627_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_projFn_1632_; lean_object* v___x_1634_; 
v_projFn_1632_ = lean_ctor_get(v_val_1628_, 1);
lean_inc(v_projFn_1632_);
lean_dec(v_val_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_projFn_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_projFn_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec(v___x_1627_);
v___x_1637_ = lean_box(0);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1638_, lean_object* v_structName_1639_, lean_object* v_fieldName_1640_){
_start:
{
lean_object* v___x_1641_; 
lean_inc_ref(v_env_1638_);
v___x_1641_ = l_Lean_getProjFnForField_x3f(v_env_1638_, v_structName_1639_, v_fieldName_1640_);
if (lean_obj_tag(v___x_1641_) == 1)
{
lean_object* v_val_1642_; lean_object* v___x_1643_; 
v_val_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_val_1642_);
lean_dec_ref(v___x_1641_);
lean_inc(v_val_1642_);
v___x_1643_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1638_, v_val_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec(v_val_1642_);
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1653_; 
v_val_1645_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1647_ = v___x_1643_;
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_val_1645_);
lean_dec(v___x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_val_1642_);
lean_ctor_set(v___x_1649_, 1, v_val_1645_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1649_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v___x_1654_; 
lean_dec(v___x_1641_);
lean_dec_ref(v_env_1638_);
v___x_1654_ = lean_box(0);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1660_ = l_Lean_Name_append(v_projFn_1658_, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1666_ = l_Lean_Name_append(v_projFn_1664_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1667_, lean_object* v_env_1668_, lean_object* v_structName_1669_, lean_object* v_fieldName_1670_){
_start:
{
lean_object* v___x_1671_; 
lean_inc(v_fieldName_1670_);
lean_inc(v_structName_1669_);
lean_inc_ref(v_env_1668_);
v___x_1671_ = l_Lean_getProjFnForField_x3f(v_env_1668_, v_structName_1669_, v_fieldName_1670_);
if (lean_obj_tag(v___x_1671_) == 1)
{
lean_object* v_val_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_fieldName_1670_);
lean_dec(v_structName_1669_);
v_val_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_val_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_defFn_1676_; uint8_t v___x_1677_; uint8_t v___x_1678_; 
v_defFn_1676_ = lean_apply_1(v_mkName_1667_, v_val_1672_);
v___x_1677_ = 1;
lean_inc(v_defFn_1676_);
v___x_1678_ = l_Lean_Environment_contains(v_env_1668_, v_defFn_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_defFn_1676_);
lean_del_object(v___x_1674_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v___x_1681_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v_defFn_1676_);
v___x_1681_ = v___x_1674_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_defFn_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v_defFn_1685_; uint8_t v___x_1686_; uint8_t v___x_1687_; 
lean_dec(v___x_1671_);
v___x_1684_ = l_Lean_Name_append(v_structName_1669_, v_fieldName_1670_);
v_defFn_1685_ = lean_apply_1(v_mkName_1667_, v___x_1684_);
v___x_1686_ = 1;
lean_inc(v_defFn_1685_);
v___x_1687_ = l_Lean_Environment_contains(v_env_1668_, v_defFn_1685_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_dec(v_defFn_1685_);
v___x_1688_ = lean_box(0);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_defFn_1685_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1691_, lean_object* v_structName_1692_, lean_object* v_fieldName_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1695_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1694_, v_env_1691_, v_structName_1692_, v_fieldName_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1697_, lean_object* v_structName_1698_, lean_object* v_fieldName_1699_){
_start:
{
lean_object* v___x_1700_; 
lean_inc(v_fieldName_1699_);
lean_inc(v_structName_1698_);
lean_inc_ref(v_env_1697_);
v___x_1700_ = l_Lean_getDefaultFnForField_x3f(v_env_1697_, v_structName_1698_, v_fieldName_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1702_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1701_, v_env_1697_, v_structName_1698_, v_fieldName_1699_);
return v___x_1702_;
}
else
{
lean_dec(v_fieldName_1699_);
lean_dec(v_structName_1698_);
lean_dec_ref(v_env_1697_);
return v___x_1700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1708_ = l_Lean_Name_append(v_projFn_1706_, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1710_, lean_object* v_structName_1711_, lean_object* v_fieldName_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1714_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1713_, v_env_1710_, v_structName_1711_, v_fieldName_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(lean_object* v_f_1715_, lean_object* v_as_1716_, lean_object* v_i_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = lean_array_get_size(v_as_1716_);
v___x_1720_ = lean_nat_dec_lt(v_i_1717_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_i_1717_);
lean_dec_ref(v_f_1715_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___y_1718_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_fst_1725_; 
v___x_1723_ = lean_array_fget_borrowed(v_as_1716_, v_i_1717_);
lean_inc_ref(v_f_1715_);
lean_inc(v___x_1723_);
v___x_1724_ = lean_apply_2(v_f_1715_, v___x_1723_, v___y_1718_);
v_fst_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_fst_1725_);
if (lean_obj_tag(v_fst_1725_) == 0)
{
lean_object* v_snd_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_snd_1726_ = lean_ctor_get(v___x_1724_, 1);
lean_inc(v_snd_1726_);
lean_dec_ref(v___x_1724_);
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_i_1717_, v___x_1727_);
lean_dec(v_i_1717_);
v_i_1717_ = v___x_1728_;
v___y_1718_ = v_snd_1726_;
goto _start;
}
else
{
lean_dec_ref(v_fst_1725_);
lean_dec(v_i_1717_);
lean_dec_ref(v_f_1715_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg___boxed(lean_object* v_f_1730_, lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1730_, v_as_1731_, v_i_1732_, v___y_1733_);
lean_dec_ref(v_as_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1(lean_object* v_path_1735_, lean_object* v_env_1736_, lean_object* v_baseStructName_1737_, lean_object* v_field_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_subobject_x3f_1740_; 
v_subobject_x3f_1740_ = lean_ctor_get(v_field_1738_, 2);
lean_inc(v_subobject_x3f_1740_);
if (lean_obj_tag(v_subobject_x3f_1740_) == 1)
{
lean_object* v_projFn_1741_; lean_object* v_val_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_projFn_1741_ = lean_ctor_get(v_field_1738_, 1);
lean_inc(v_projFn_1741_);
lean_dec_ref(v_field_1738_);
v_val_1742_ = lean_ctor_get(v_subobject_x3f_1740_, 0);
lean_inc(v_val_1742_);
lean_dec_ref(v_subobject_x3f_1740_);
v___x_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_projFn_1741_);
lean_ctor_set(v___x_1743_, 1, v_path_1735_);
v___x_1744_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1736_, v_baseStructName_1737_, v_val_1742_, v___x_1743_, v___y_1739_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_subobject_x3f_1740_);
lean_dec_ref(v_field_1738_);
lean_dec(v_baseStructName_1737_);
lean_dec_ref(v_env_1736_);
lean_dec(v_path_1735_);
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___y_1739_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1747_, lean_object* v_baseStructName_1748_, lean_object* v_structName_1749_, lean_object* v_path_1750_, lean_object* v_a_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_name_eq(v_baseStructName_1748_, v_structName_1749_);
if (v___x_1752_ == 0)
{
lean_object* v___f_1753_; lean_object* v___f_1754_; uint8_t v___x_1768_; 
lean_inc(v_baseStructName_1748_);
lean_inc_ref(v_env_1747_);
lean_inc(v_path_1750_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0), 5, 3);
lean_closure_set(v___f_1753_, 0, v_path_1750_);
lean_closure_set(v___f_1753_, 1, v_env_1747_);
lean_closure_set(v___f_1753_, 2, v_baseStructName_1748_);
lean_inc_ref(v_env_1747_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1), 5, 3);
lean_closure_set(v___f_1754_, 0, v_path_1750_);
lean_closure_set(v___f_1754_, 1, v_env_1747_);
lean_closure_set(v___f_1754_, 2, v_baseStructName_1748_);
v___x_1768_ = l_Lean_NameSet_contains(v_a_1751_, v_structName_1749_);
if (v___x_1768_ == 0)
{
goto v___jp_1755_;
}
else
{
if (v___x_1752_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v___f_1754_);
lean_dec_ref(v___f_1753_);
lean_dec(v_structName_1749_);
lean_dec_ref(v_env_1747_);
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1751_);
return v___x_1770_;
}
else
{
goto v___jp_1755_;
}
}
v___jp_1755_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v_structName_1749_);
v___x_1756_ = l_Lean_NameSet_insert(v_a_1751_, v_structName_1749_);
v___x_1757_ = l_Lean_getStructureInfo_x3f(v_env_1747_, v_structName_1749_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; lean_object* v_fieldInfo_1759_; lean_object* v_parentInfo_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_fst_1763_; 
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_val_1758_);
lean_dec_ref(v___x_1757_);
v_fieldInfo_1759_ = lean_ctor_get(v_val_1758_, 2);
lean_inc_ref(v_fieldInfo_1759_);
v_parentInfo_1760_ = lean_ctor_get(v_val_1758_, 3);
lean_inc_ref(v_parentInfo_1760_);
lean_dec(v_val_1758_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1754_, v_fieldInfo_1759_, v___x_1761_, v___x_1756_);
lean_dec_ref(v_fieldInfo_1759_);
v_fst_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_fst_1763_);
if (lean_obj_tag(v_fst_1763_) == 0)
{
lean_object* v_snd_1764_; lean_object* v___x_1765_; 
v_snd_1764_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___x_1762_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1753_, v_parentInfo_1760_, v___x_1761_, v_snd_1764_);
lean_dec_ref(v_parentInfo_1760_);
return v___x_1765_;
}
else
{
lean_dec_ref(v_fst_1763_);
lean_dec_ref(v_parentInfo_1760_);
lean_dec_ref(v___f_1753_);
return v___x_1762_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v___x_1757_);
lean_dec_ref(v___f_1754_);
lean_dec_ref(v___f_1753_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___x_1756_);
return v___x_1767_;
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_structName_1749_);
lean_dec(v_baseStructName_1748_);
lean_dec_ref(v_env_1747_);
v___x_1771_ = l_List_reverse___redArg(v_path_1750_);
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v_a_1751_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0(lean_object* v_path_1774_, lean_object* v_env_1775_, lean_object* v_baseStructName_1776_, lean_object* v_parent_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_structName_1779_; lean_object* v_projFn_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_structName_1779_ = lean_ctor_get(v_parent_1777_, 0);
lean_inc(v_structName_1779_);
v_projFn_1780_ = lean_ctor_get(v_parent_1777_, 1);
lean_inc(v_projFn_1780_);
lean_dec_ref(v_parent_1777_);
v___x_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_projFn_1780_);
lean_ctor_set(v___x_1781_, 1, v_path_1774_);
v___x_1782_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1775_, v_baseStructName_1776_, v_structName_1779_, v___x_1781_, v___y_1778_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_00_u03b2_1783_, lean_object* v_00_u03b1_1784_, lean_object* v_f_1785_, lean_object* v_as_1786_, lean_object* v_i_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1785_, v_as_1786_, v_i_1787_, v___y_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_1790_, lean_object* v_00_u03b1_1791_, lean_object* v_f_1792_, lean_object* v_as_1793_, lean_object* v_i_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_00_u03b2_1790_, v_00_u03b1_1791_, v_f_1792_, v_as_1793_, v_i_1794_, v___y_1795_);
lean_dec_ref(v_as_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1797_, lean_object* v_baseStructName_1798_, lean_object* v_structName_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_fst_1803_; 
v___x_1800_ = lean_box(0);
v___x_1801_ = l_Lean_NameSet_empty;
v___x_1802_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1797_, v_baseStructName_1798_, v_structName_1799_, v___x_1800_, v___x_1801_);
v_fst_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_fst_1803_);
lean_dec_ref(v___x_1802_);
return v_fst_1803_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1804_, lean_object* v_constName_1805_){
_start:
{
uint8_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = 0;
v___x_1807_ = l_Lean_Environment_find_x3f(v_env_1804_, v_constName_1805_, v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 1)
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v___x_1807_);
if (lean_obj_tag(v_val_1808_) == 5)
{
lean_object* v_val_1809_; lean_object* v_numIndices_1810_; lean_object* v_ctors_1811_; uint8_t v_isRec_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_val_1809_ = lean_ctor_get(v_val_1808_, 0);
lean_inc_ref(v_val_1809_);
lean_dec_ref(v_val_1808_);
v_numIndices_1810_ = lean_ctor_get(v_val_1809_, 2);
lean_inc(v_numIndices_1810_);
v_ctors_1811_ = lean_ctor_get(v_val_1809_, 4);
lean_inc(v_ctors_1811_);
v_isRec_1812_ = lean_ctor_get_uint8(v_val_1809_, sizeof(void*)*6);
lean_dec_ref(v_val_1809_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_nat_dec_eq(v_numIndices_1810_, v___x_1813_);
lean_dec(v_numIndices_1810_);
if (v___x_1814_ == 0)
{
lean_dec(v_ctors_1811_);
return v___x_1806_;
}
else
{
if (lean_obj_tag(v_ctors_1811_) == 1)
{
lean_object* v_tail_1815_; 
v_tail_1815_ = lean_ctor_get(v_ctors_1811_, 1);
lean_inc(v_tail_1815_);
lean_dec_ref(v_ctors_1811_);
if (lean_obj_tag(v_tail_1815_) == 0)
{
if (v_isRec_1812_ == 0)
{
return v___x_1814_;
}
else
{
return v___x_1806_;
}
}
else
{
lean_dec(v_tail_1815_);
return v___x_1806_;
}
}
else
{
lean_dec(v_ctors_1811_);
return v___x_1806_;
}
}
}
else
{
lean_dec(v_val_1808_);
return v___x_1806_;
}
}
else
{
lean_dec(v___x_1807_);
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1816_, lean_object* v_constName_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Lean_isNonRecStructure(v_env_1816_, v_constName_1817_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_panic_fn(v___x_1821_, v_msg_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1824_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1825_ = lean_unsigned_to_nat(11u);
v___x_1826_ = lean_unsigned_to_nat(374u);
v___x_1827_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1828_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1829_ = l_mkPanicMessageWithDecl(v___x_1828_, v___x_1827_, v___x_1826_, v___x_1825_, v___x_1824_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1830_, lean_object* v_constName_1831_){
_start:
{
uint8_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = 0;
lean_inc_ref(v_env_1830_);
v___x_1836_ = l_Lean_Environment_find_x3f(v_env_1830_, v_constName_1831_, v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 1)
{
lean_object* v_val_1837_; 
v_val_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1837_);
lean_dec_ref(v___x_1836_);
if (lean_obj_tag(v_val_1837_) == 5)
{
lean_object* v_val_1838_; lean_object* v_numIndices_1839_; lean_object* v_ctors_1840_; uint8_t v_isRec_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_val_1838_ = lean_ctor_get(v_val_1837_, 0);
lean_inc_ref(v_val_1838_);
lean_dec_ref(v_val_1837_);
v_numIndices_1839_ = lean_ctor_get(v_val_1838_, 2);
lean_inc(v_numIndices_1839_);
v_ctors_1840_ = lean_ctor_get(v_val_1838_, 4);
lean_inc(v_ctors_1840_);
v_isRec_1841_ = lean_ctor_get_uint8(v_val_1838_, sizeof(void*)*6);
lean_dec_ref(v_val_1838_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_eq(v_numIndices_1839_, v___x_1842_);
lean_dec(v_numIndices_1839_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec(v_ctors_1840_);
lean_dec_ref(v_env_1830_);
v___x_1844_ = lean_box(0);
return v___x_1844_;
}
else
{
if (lean_obj_tag(v_ctors_1840_) == 1)
{
lean_object* v_tail_1845_; 
v_tail_1845_ = lean_ctor_get(v_ctors_1840_, 1);
if (lean_obj_tag(v_tail_1845_) == 0)
{
if (v_isRec_1841_ == 0)
{
lean_object* v_head_1846_; lean_object* v___x_1847_; 
v_head_1846_ = lean_ctor_get(v_ctors_1840_, 0);
lean_inc(v_head_1846_);
lean_dec_ref(v_ctors_1840_);
v___x_1847_ = l_Lean_Environment_find_x3f(v_env_1830_, v_head_1846_, v_isRec_1841_);
if (lean_obj_tag(v___x_1847_) == 1)
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_val_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
if (lean_obj_tag(v_val_1848_) == 6)
{
lean_object* v_val_1852_; lean_object* v___x_1854_; 
v_val_1852_ = lean_ctor_get(v_val_1848_, 0);
lean_inc_ref(v_val_1852_);
lean_dec_ref(v_val_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_val_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_val_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
goto v___jp_1832_;
}
}
}
else
{
lean_dec(v___x_1847_);
goto v___jp_1832_;
}
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v_ctors_1840_);
lean_dec_ref(v_env_1830_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref(v_ctors_1840_);
lean_dec_ref(v_env_1830_);
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1859_; 
lean_dec(v_ctors_1840_);
lean_dec_ref(v_env_1830_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_val_1837_);
lean_dec_ref(v_env_1830_);
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
}
else
{
lean_object* v___x_1861_; 
lean_dec(v___x_1836_);
lean_dec_ref(v_env_1830_);
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
v___jp_1832_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1834_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1833_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1862_, lean_object* v_constName_1863_){
_start:
{
uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = 0;
lean_inc_ref(v_env_1862_);
v___x_1865_ = l_Lean_Environment_find_x3f(v_env_1862_, v_constName_1863_, v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v___x_1865_);
if (lean_obj_tag(v_val_1866_) == 5)
{
lean_object* v_val_1867_; lean_object* v_numIndices_1868_; lean_object* v_ctors_1869_; uint8_t v_isRec_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_val_1867_ = lean_ctor_get(v_val_1866_, 0);
lean_inc_ref(v_val_1867_);
lean_dec_ref(v_val_1866_);
v_numIndices_1868_ = lean_ctor_get(v_val_1867_, 2);
lean_inc(v_numIndices_1868_);
v_ctors_1869_ = lean_ctor_get(v_val_1867_, 4);
lean_inc(v_ctors_1869_);
v_isRec_1870_ = lean_ctor_get_uint8(v_val_1867_, sizeof(void*)*6);
lean_dec_ref(v_val_1867_);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_nat_dec_eq(v_numIndices_1868_, v___x_1871_);
lean_dec(v_numIndices_1868_);
if (v___x_1872_ == 0)
{
lean_dec(v_ctors_1869_);
lean_dec_ref(v_env_1862_);
return v___x_1871_;
}
else
{
if (lean_obj_tag(v_ctors_1869_) == 1)
{
lean_object* v_tail_1873_; 
v_tail_1873_ = lean_ctor_get(v_ctors_1869_, 1);
if (lean_obj_tag(v_tail_1873_) == 0)
{
if (v_isRec_1870_ == 0)
{
lean_object* v_head_1874_; lean_object* v___x_1875_; 
v_head_1874_ = lean_ctor_get(v_ctors_1869_, 0);
lean_inc(v_head_1874_);
lean_dec_ref(v_ctors_1869_);
v___x_1875_ = l_Lean_Environment_find_x3f(v_env_1862_, v_head_1874_, v_isRec_1870_);
if (lean_obj_tag(v___x_1875_) == 1)
{
lean_object* v_val_1876_; 
v_val_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_val_1876_);
lean_dec_ref(v___x_1875_);
if (lean_obj_tag(v_val_1876_) == 6)
{
lean_object* v_val_1877_; lean_object* v_numFields_1878_; 
v_val_1877_ = lean_ctor_get(v_val_1876_, 0);
lean_inc_ref(v_val_1877_);
lean_dec_ref(v_val_1876_);
v_numFields_1878_ = lean_ctor_get(v_val_1877_, 4);
lean_inc(v_numFields_1878_);
lean_dec_ref(v_val_1877_);
return v_numFields_1878_;
}
else
{
lean_dec(v_val_1876_);
return v___x_1871_;
}
}
else
{
lean_dec(v___x_1875_);
return v___x_1871_;
}
}
else
{
lean_dec_ref(v_ctors_1869_);
lean_dec_ref(v_env_1862_);
return v___x_1871_;
}
}
else
{
lean_dec_ref(v_ctors_1869_);
lean_dec_ref(v_env_1862_);
return v___x_1871_;
}
}
else
{
lean_dec(v_ctors_1869_);
lean_dec_ref(v_env_1862_);
return v___x_1871_;
}
}
}
else
{
lean_object* v___x_1879_; 
lean_dec(v_val_1866_);
lean_dec_ref(v_env_1862_);
v___x_1879_ = lean_unsigned_to_nat(0u);
return v___x_1879_;
}
}
else
{
lean_object* v___x_1880_; 
lean_dec(v___x_1865_);
lean_dec_ref(v_env_1862_);
v___x_1880_ = lean_unsigned_to_nat(0u);
return v___x_1880_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_1889_);
return v_res_1891_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___f_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1893_, 0, v___x_1892_);
return v___f_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___f_1895_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_box(1);
v___x_1898_ = l_Lean_registerEnvExtension___redArg(v___f_1895_, v___x_1896_, v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_1901_, lean_object* v_structName_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v_asyncMode_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1903_ = l_Lean_structureResolutionExt;
v_asyncMode_1904_ = lean_ctor_get(v___x_1903_, 2);
lean_inc(v_asyncMode_1904_);
v___x_1905_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_1906_ = lean_box(0);
v___x_1907_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1905_, v___x_1903_, v_env_1901_, v_asyncMode_1904_, v___x_1906_);
lean_dec(v_asyncMode_1904_);
v___x_1908_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_1907_, v_structName_1902_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_1909_, lean_object* v_structName_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_1909_, v_structName_1910_);
lean_dec(v_structName_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_1912_, lean_object* v___x_1913_, lean_object* v_structName_1914_, lean_object* v_resolutionOrder_1915_, lean_object* v_s_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1912_, v___x_1913_, v_s_1916_, v_structName_1914_, v_resolutionOrder_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_1918_, lean_object* v_env_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v_asyncMode_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = l_Lean_structureResolutionExt;
v_asyncMode_1921_ = lean_ctor_get(v___x_1920_, 2);
lean_inc(v_asyncMode_1921_);
v___x_1922_ = lean_box(0);
v___x_1923_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1920_, v_env_1919_, v___f_1918_, v_asyncMode_1921_, v___x_1922_);
lean_dec(v_asyncMode_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_1924_, lean_object* v_structName_1925_, lean_object* v_resolutionOrder_1926_){
_start:
{
lean_object* v_modifyEnv_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v_modifyEnv_1927_ = lean_ctor_get(v_inst_1924_, 1);
lean_inc(v_modifyEnv_1927_);
lean_dec_ref(v_inst_1924_);
v___x_1928_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1929_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_1930_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1930_, 0, v___x_1928_);
lean_closure_set(v___f_1930_, 1, v___x_1929_);
lean_closure_set(v___f_1930_, 2, v_structName_1925_);
lean_closure_set(v___f_1930_, 3, v_resolutionOrder_1926_);
v___f_1931_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1931_, 0, v___f_1930_);
v___x_1932_ = lean_apply_1(v_modifyEnv_1927_, v___f_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_1933_, lean_object* v_inst_1934_, lean_object* v_structName_1935_, lean_object* v_resolutionOrder_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_1934_, v_structName_1935_, v_resolutionOrder_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult_default(void){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0, &l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult(void){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_instInhabitedStructureResolutionOrderResult_default;
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_1950_, lean_object* v_resOrders_1951_, lean_object* v___x_1952_, lean_object* v_toPure_1953_, lean_object* v_____s_1954_){
_start:
{
lean_object* v_fst_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1970_; 
v_fst_1955_ = lean_ctor_get(v_____s_1954_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_____s_1954_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_____s_1954_, 1);
lean_dec(v_unused_1971_);
v___x_1957_ = v_____s_1954_;
v_isShared_1958_ = v_isSharedCheck_1970_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_fst_1955_);
lean_dec(v_____s_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1970_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
if (lean_obj_tag(v_fst_1955_) == 0)
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1959_ = 0;
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_borrowed(v___x_1950_, v_resOrders_1951_, v___x_1960_);
v___x_1962_ = lean_array_get_borrowed(v___x_1952_, v___x_1961_, v___x_1960_);
v___x_1963_ = lean_box(v___x_1959_);
lean_inc(v___x_1962_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1962_);
lean_ctor_set(v___x_1957_, 0, v___x_1963_);
v___x_1965_ = v___x_1957_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1962_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_apply_2(v_toPure_1953_, lean_box(0), v___x_1965_);
return v___x_1966_;
}
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1957_);
lean_dec(v___x_1952_);
lean_dec_ref(v___x_1950_);
v_val_1968_ = lean_ctor_get(v_fst_1955_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_fst_1955_);
v___x_1969_ = lean_apply_2(v_toPure_1953_, lean_box(0), v_val_1968_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_1972_, lean_object* v_resOrders_1973_, lean_object* v___x_1974_, lean_object* v_toPure_1975_, lean_object* v_____s_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_1972_, v_resOrders_1973_, v___x_1974_, v_toPure_1975_, v_____s_1976_);
lean_dec_ref(v_resOrders_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_1978_, lean_object* v_____do__lift_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_apply_2(v_toPure_1978_, lean_box(0), v_____do__lift_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_1981_, lean_object* v_toPure_1982_, lean_object* v___x_1983_, lean_object* v_____s_1984_){
_start:
{
lean_object* v_fst_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2003_; 
v_fst_1985_ = lean_ctor_get(v_____s_1984_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_____s_1984_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_____s_1984_, 1);
lean_dec(v_unused_2004_);
v___x_1987_ = v_____s_1984_;
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_fst_1985_);
lean_dec(v_____s_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2003_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
if (lean_obj_tag(v_fst_1985_) == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_del_object(v___x_1987_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1981_);
v___x_1990_ = lean_apply_2(v_toPure_1982_, lean_box(0), v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v___x_1992_; 
lean_dec_ref(v___x_1981_);
lean_inc_ref(v_fst_1985_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_1983_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_fst_1985_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1983_);
v___x_1992_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
v_isSharedCheck_2000_ = !lean_is_exclusive(v_fst_1985_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_fst_1985_, 0);
lean_dec(v_unused_2001_);
v___x_1994_ = v_fst_1985_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v_fst_1985_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1992_);
v___x_1997_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_apply_2(v_toPure_1982_, lean_box(0), v___x_1997_);
return v___x_1998_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2005_, lean_object* v_next_2006_, lean_object* v_G_2007_, lean_object* v_____do__lift_2008_){
_start:
{
if (lean_obj_tag(v_____do__lift_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
lean_dec(v_G_2007_);
v_a_2009_ = lean_ctor_get(v_____do__lift_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v_____do__lift_2008_);
v___x_2010_ = lean_apply_2(v_toPure_2005_, lean_box(0), v_a_2009_);
return v___x_2010_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_toPure_2005_);
v_a_2011_ = lean_ctor_get(v_____do__lift_2008_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v_____do__lift_2008_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_next_2006_, v___x_2012_);
v___x_2014_ = lean_apply_4(v_G_2007_, v___x_2013_, v_a_2011_, lean_box(0), lean_box(0));
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2015_, lean_object* v_next_2016_, lean_object* v_G_2017_, lean_object* v_____do__lift_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2015_, v_next_2016_, v_G_2017_, v_____do__lift_2018_);
lean_dec(v_next_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2020_, lean_object* v_v_2021_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_name_eq(v_v_2021_, v___x_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2023_, lean_object* v_v_2024_){
_start:
{
uint8_t v_res_2025_; lean_object* v_r_2026_; 
v_res_2025_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2023_, v_v_2024_);
lean_dec(v_v_2024_);
lean_dec(v___x_2023_);
v_r_2026_ = lean_box(v_res_2025_);
return v_r_2026_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2046_, lean_object* v___f_2047_, lean_object* v_resOrder_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v_array_2053_; lean_object* v_start_2054_; lean_object* v_stop_2055_; uint8_t v___x_2056_; lean_object* v___y_2058_; 
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_array_get_size(v_resOrder_2048_);
v___x_2051_ = l_Array_toSubarray___redArg(v_resOrder_2048_, v___x_2049_, v___x_2050_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2053_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_array_2053_);
v_start_2054_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_start_2054_);
v_stop_2055_ = lean_ctor_get(v___x_2051_, 2);
lean_inc(v_stop_2055_);
lean_dec_ref(v___x_2051_);
v___x_2056_ = lean_nat_dec_lt(v_start_2054_, v_stop_2055_);
if (v___x_2056_ == 0)
{
lean_dec(v_stop_2055_);
lean_dec(v_start_2054_);
lean_dec_ref(v_array_2053_);
lean_dec_ref(v___f_2047_);
return v___x_2046_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = lean_array_get_size(v_array_2053_);
v___x_2066_ = lean_nat_dec_le(v_stop_2055_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_dec(v_stop_2055_);
v___y_2058_ = v___x_2065_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v_stop_2055_;
goto v___jp_2057_;
}
}
v___jp_2057_:
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_nat_dec_lt(v_start_2054_, v___y_2058_);
if (v___x_2059_ == 0)
{
lean_dec(v___y_2058_);
lean_dec(v_start_2054_);
lean_dec_ref(v_array_2053_);
lean_dec_ref(v___f_2047_);
return v___x_2056_;
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2060_ = lean_usize_of_nat(v_start_2054_);
lean_dec(v_start_2054_);
v___x_2061_ = lean_usize_of_nat(v___y_2058_);
lean_dec(v___y_2058_);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2052_, v___f_2047_, v_array_2053_, v___x_2060_, v___x_2061_);
v___x_2063_ = lean_unbox(v___x_2062_);
lean_dec(v___x_2062_);
if (v___x_2063_ == 0)
{
return v___x_2059_;
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = 0;
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2067_, lean_object* v___f_2068_, lean_object* v_resOrder_2069_){
_start:
{
uint8_t v___x_1715__boxed_2070_; uint8_t v_res_2071_; lean_object* v_r_2072_; 
v___x_1715__boxed_2070_ = lean_unbox(v___x_2067_);
v_res_2071_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2070_, v___f_2068_, v_resOrder_2069_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2073_, uint8_t v___y_2074_, lean_object* v_v_2075_){
_start:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_apply_1(v___f_2073_, v_v_2075_);
v___x_2077_ = lean_unbox(v___x_2076_);
if (v___x_2077_ == 0)
{
return v___y_2074_;
}
else
{
uint8_t v___x_2078_; 
v___x_2078_ = 0;
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2079_, lean_object* v___y_2080_, lean_object* v_v_2081_){
_start:
{
uint8_t v___y_1771__boxed_2082_; uint8_t v_res_2083_; lean_object* v_r_2084_; 
v___y_1771__boxed_2082_ = lean_unbox(v___y_2080_);
v_res_2083_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2079_, v___y_1771__boxed_2082_, v_v_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2085_, uint8_t v___x_2086_, lean_object* v_v_2087_){
_start:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_apply_1(v___f_2085_, v_v_2087_);
v___x_2089_ = lean_unbox(v___x_2088_);
if (v___x_2089_ == 0)
{
return v___x_2086_;
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2091_, lean_object* v___x_2092_, lean_object* v_v_2093_){
_start:
{
uint8_t v___x_1783__boxed_2094_; uint8_t v_res_2095_; lean_object* v_r_2096_; 
v___x_1783__boxed_2094_ = lean_unbox(v___x_2092_);
v_res_2095_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2091_, v___x_1783__boxed_2094_, v_v_2093_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2097_, lean_object* v_toPure_2098_, lean_object* v___x_2099_, lean_object* v_resOrders_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v_toBind_2103_, lean_object* v___f_2104_, lean_object* v___x_2105_, lean_object* v_next_2106_, lean_object* v___x_2107_, lean_object* v_next_2108_, lean_object* v_acc_2109_, lean_object* v_h_2110_, lean_object* v_G_2111_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_lt(v_next_2108_, v___x_2097_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec(v_G_2111_);
lean_dec(v_next_2108_);
lean_dec_ref(v___x_2105_);
lean_dec(v___f_2104_);
lean_dec(v_toBind_2103_);
lean_dec(v___x_2102_);
lean_dec(v___x_2101_);
lean_dec_ref(v_resOrders_2100_);
lean_dec_ref(v___x_2099_);
lean_dec(v___x_2097_);
v___x_2113_ = lean_apply_2(v_toPure_2098_, lean_box(0), v_acc_2109_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v_array_2118_; lean_object* v_start_2119_; lean_object* v_stop_2120_; lean_object* v___f_2121_; lean_object* v___y_2123_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___f_2150_; uint8_t v___y_2152_; uint8_t v___x_2164_; 
lean_dec_ref(v_acc_2109_);
v___x_2114_ = lean_array_get_borrowed(v___x_2099_, v_resOrders_2100_, v_next_2108_);
v___x_2115_ = lean_array_get(v___x_2101_, v___x_2114_, v___x_2102_);
lean_inc(v_next_2108_);
lean_inc(v___x_2102_);
lean_inc_ref(v_resOrders_2100_);
v___x_2116_ = l_Array_toSubarray___redArg(v_resOrders_2100_, v___x_2102_, v_next_2108_);
v___x_2117_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2118_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_ref(v_array_2118_);
v_start_2119_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_start_2119_);
v_stop_2120_ = lean_ctor_get(v___x_2116_, 2);
lean_inc(v_stop_2120_);
lean_dec_ref(v___x_2116_);
lean_inc(v_next_2108_);
lean_inc(v_toPure_2098_);
v___f_2121_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2121_, 0, v_toPure_2098_);
lean_closure_set(v___f_2121_, 1, v_next_2108_);
lean_closure_set(v___f_2121_, 2, v_G_2111_);
lean_inc(v___x_2115_);
v___f_2148_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2148_, 0, v___x_2115_);
v___x_2149_ = lean_box(v___x_2112_);
v___f_2150_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2150_, 0, v___x_2149_);
lean_closure_set(v___f_2150_, 1, v___f_2148_);
v___x_2164_ = lean_nat_dec_lt(v_start_2119_, v_stop_2120_);
if (v___x_2164_ == 0)
{
lean_dec(v_stop_2120_);
lean_dec(v_start_2119_);
lean_dec_ref(v_array_2118_);
v___y_2152_ = v___x_2112_;
goto v___jp_2151_;
}
else
{
lean_object* v___x_2165_; lean_object* v___f_2166_; lean_object* v___y_2168_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2165_ = lean_box(v___x_2112_);
lean_inc_ref(v___f_2150_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2166_, 0, v___f_2150_);
lean_closure_set(v___f_2166_, 1, v___x_2165_);
v___x_2174_ = lean_array_get_size(v_array_2118_);
v___x_2175_ = lean_nat_dec_le(v_stop_2120_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec(v_stop_2120_);
v___y_2168_ = v___x_2174_;
goto v___jp_2167_;
}
else
{
v___y_2168_ = v_stop_2120_;
goto v___jp_2167_;
}
v___jp_2167_:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_nat_dec_lt(v_start_2119_, v___y_2168_);
if (v___x_2169_ == 0)
{
lean_dec(v___y_2168_);
lean_dec_ref(v___f_2166_);
lean_dec(v_start_2119_);
lean_dec_ref(v_array_2118_);
v___y_2152_ = v___x_2164_;
goto v___jp_2151_;
}
else
{
size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2170_ = lean_usize_of_nat(v_start_2119_);
lean_dec(v_start_2119_);
v___x_2171_ = lean_usize_of_nat(v___y_2168_);
lean_dec(v___y_2168_);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2117_, v___f_2166_, v_array_2118_, v___x_2170_, v___x_2171_);
v___x_2173_ = lean_unbox(v___x_2172_);
lean_dec(v___x_2172_);
if (v___x_2173_ == 0)
{
v___y_2152_ = v___x_2169_;
goto v___jp_2151_;
}
else
{
lean_dec_ref(v___f_2150_);
lean_dec(v___x_2115_);
lean_dec(v_next_2108_);
lean_dec(v___x_2102_);
lean_dec_ref(v_resOrders_2100_);
lean_dec(v___x_2097_);
goto v___jp_2126_;
}
}
}
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_inc(v_toBind_2103_);
v___x_2124_ = lean_apply_4(v_toBind_2103_, lean_box(0), lean_box(0), v___y_2123_, v___f_2104_);
v___x_2125_ = lean_apply_4(v_toBind_2103_, lean_box(0), lean_box(0), v___x_2124_, v___f_2121_);
return v___x_2125_;
}
v___jp_2126_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2105_);
v___x_2128_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2127_);
v___y_2123_ = v___x_2128_;
goto v___jp_2122_;
}
v___jp_2129_:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2130_ = lean_nat_dec_eq(v_next_2106_, v___x_2102_);
lean_dec(v___x_2102_);
v___x_2131_ = lean_box(v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2115_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2107_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2135_);
v___y_2123_ = v___x_2136_;
goto v___jp_2122_;
}
v___jp_2137_:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_lt(v___y_2139_, v___y_2142_);
if (v___x_2143_ == 0)
{
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v___x_2105_);
goto v___jp_2129_;
}
else
{
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2144_ = lean_usize_of_nat(v___y_2139_);
lean_dec(v___y_2139_);
v___x_2145_ = lean_usize_of_nat(v___y_2142_);
lean_dec(v___y_2142_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2138_, v___y_2140_, v___y_2141_, v___x_2144_, v___x_2145_);
v___x_2147_ = lean_unbox(v___x_2146_);
lean_dec(v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v___x_2105_);
goto v___jp_2129_;
}
else
{
lean_dec(v___x_2115_);
lean_dec(v___x_2102_);
goto v___jp_2126_;
}
}
}
v___jp_2151_:
{
if (v___y_2152_ == 0)
{
lean_dec_ref(v___f_2150_);
lean_dec(v___x_2115_);
lean_dec(v_next_2108_);
lean_dec(v___x_2102_);
lean_dec_ref(v_resOrders_2100_);
lean_dec(v___x_2097_);
goto v___jp_2126_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_array_2156_; lean_object* v_start_2157_; lean_object* v_stop_2158_; uint8_t v___x_2159_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_add(v_next_2108_, v___x_2153_);
lean_dec(v_next_2108_);
v___x_2155_ = l_Array_toSubarray___redArg(v_resOrders_2100_, v___x_2154_, v___x_2097_);
v_array_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc_ref(v_array_2156_);
v_start_2157_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_start_2157_);
v_stop_2158_ = lean_ctor_get(v___x_2155_, 2);
lean_inc(v_stop_2158_);
lean_dec_ref(v___x_2155_);
v___x_2159_ = lean_nat_dec_lt(v_start_2157_, v_stop_2158_);
if (v___x_2159_ == 0)
{
lean_dec(v_stop_2158_);
lean_dec(v_start_2157_);
lean_dec_ref(v_array_2156_);
lean_dec_ref(v___f_2150_);
lean_dec_ref(v___x_2105_);
goto v___jp_2129_;
}
else
{
lean_object* v___x_2160_; lean_object* v___f_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2160_ = lean_box(v___y_2152_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2161_, 0, v___f_2150_);
lean_closure_set(v___f_2161_, 1, v___x_2160_);
v___x_2162_ = lean_array_get_size(v_array_2156_);
v___x_2163_ = lean_nat_dec_le(v_stop_2158_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_dec(v_stop_2158_);
v___y_2138_ = v___x_2117_;
v___y_2139_ = v_start_2157_;
v___y_2140_ = v___f_2161_;
v___y_2141_ = v_array_2156_;
v___y_2142_ = v___x_2162_;
goto v___jp_2137_;
}
else
{
v___y_2138_ = v___x_2117_;
v___y_2139_ = v_start_2157_;
v___y_2140_ = v___f_2161_;
v___y_2141_ = v_array_2156_;
v___y_2142_ = v_stop_2158_;
goto v___jp_2137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2176_, lean_object* v_toPure_2177_, lean_object* v___x_2178_, lean_object* v_resOrders_2179_, lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v_toBind_2182_, lean_object* v___f_2183_, lean_object* v___x_2184_, lean_object* v_next_2185_, lean_object* v___x_2186_, lean_object* v_next_2187_, lean_object* v_acc_2188_, lean_object* v_h_2189_, lean_object* v_G_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2176_, v_toPure_2177_, v___x_2178_, v_resOrders_2179_, v___x_2180_, v___x_2181_, v_toBind_2182_, v___f_2183_, v___x_2184_, v_next_2185_, v___x_2186_, v_next_2187_, v_acc_2188_, v_h_2189_, v_G_2190_);
lean_dec(v_next_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2192_, lean_object* v_toPure_2193_, lean_object* v___x_2194_, lean_object* v_resOrders_2195_, lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v_toBind_2198_, lean_object* v___f_2199_, lean_object* v___x_2200_, lean_object* v___x_2201_, lean_object* v___f_2202_, lean_object* v___f_2203_, lean_object* v_next_2204_, lean_object* v_acc_2205_, lean_object* v_h_2206_, lean_object* v_G_2207_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = lean_nat_dec_lt(v_next_2204_, v___x_2192_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
lean_dec(v_G_2207_);
lean_dec(v_next_2204_);
lean_dec(v___f_2203_);
lean_dec(v___f_2202_);
lean_dec_ref(v___x_2200_);
lean_dec(v___f_2199_);
lean_dec(v_toBind_2198_);
lean_dec(v___x_2197_);
lean_dec(v___x_2196_);
lean_dec_ref(v_resOrders_2195_);
lean_dec_ref(v___x_2194_);
v___x_2209_ = lean_apply_2(v_toPure_2193_, lean_box(0), v_acc_2205_);
return v___x_2209_;
}
else
{
lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v_acc_2205_);
lean_inc(v_next_2204_);
lean_inc(v_toPure_2193_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2210_, 0, v_toPure_2193_);
lean_closure_set(v___f_2210_, 1, v_next_2204_);
lean_closure_set(v___f_2210_, 2, v_G_2207_);
v___x_2211_ = lean_nat_sub(v___x_2192_, v_next_2204_);
lean_inc_ref(v___x_2200_);
lean_inc(v_toBind_2198_);
lean_inc(v___x_2197_);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2212_, 0, v___x_2211_);
lean_closure_set(v___f_2212_, 1, v_toPure_2193_);
lean_closure_set(v___f_2212_, 2, v___x_2194_);
lean_closure_set(v___f_2212_, 3, v_resOrders_2195_);
lean_closure_set(v___f_2212_, 4, v___x_2196_);
lean_closure_set(v___f_2212_, 5, v___x_2197_);
lean_closure_set(v___f_2212_, 6, v_toBind_2198_);
lean_closure_set(v___f_2212_, 7, v___f_2199_);
lean_closure_set(v___f_2212_, 8, v___x_2200_);
lean_closure_set(v___f_2212_, 9, v_next_2204_);
lean_closure_set(v___f_2212_, 10, v___x_2201_);
v___x_2213_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2212_, v___x_2197_, v___x_2200_, lean_box(0));
lean_inc(v_toBind_2198_);
v___x_2214_ = lean_apply_4(v_toBind_2198_, lean_box(0), lean_box(0), v___x_2213_, v___f_2202_);
lean_inc(v_toBind_2198_);
v___x_2215_ = lean_apply_4(v_toBind_2198_, lean_box(0), lean_box(0), v___x_2214_, v___f_2203_);
v___x_2216_ = lean_apply_4(v_toBind_2198_, lean_box(0), lean_box(0), v___x_2215_, v___f_2210_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2217_, lean_object* v_toPure_2218_, lean_object* v___x_2219_, lean_object* v_resOrders_2220_, lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v_toBind_2223_, lean_object* v___f_2224_, lean_object* v___x_2225_, lean_object* v___x_2226_, lean_object* v___f_2227_, lean_object* v___f_2228_, lean_object* v_next_2229_, lean_object* v_acc_2230_, lean_object* v_h_2231_, lean_object* v_G_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2217_, v_toPure_2218_, v___x_2219_, v_resOrders_2220_, v___x_2221_, v___x_2222_, v_toBind_2223_, v___f_2224_, v___x_2225_, v___x_2226_, v___f_2227_, v___f_2228_, v_next_2229_, v_acc_2230_, v_h_2231_, v_G_2232_);
lean_dec(v___x_2217_);
return v_res_2233_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Array_instInhabited(lean_box(0));
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2238_, lean_object* v_resOrders_2239_){
_start:
{
lean_object* v_toApplicative_2240_; lean_object* v_toBind_2241_; lean_object* v_toPure_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___f_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_toApplicative_2240_ = lean_ctor_get(v_inst_2238_, 0);
lean_inc_ref(v_toApplicative_2240_);
v_toBind_2241_ = lean_ctor_get(v_inst_2238_, 1);
lean_inc(v_toBind_2241_);
lean_dec_ref(v_inst_2238_);
v_toPure_2242_ = lean_ctor_get(v_toApplicative_2240_, 1);
lean_inc(v_toPure_2242_);
lean_dec_ref(v_toApplicative_2240_);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2245_ = lean_array_get_size(v_resOrders_2239_);
lean_inc(v_toPure_2242_);
lean_inc_ref(v_resOrders_2239_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2246_, 0, v___x_2244_);
lean_closure_set(v___f_2246_, 1, v_resOrders_2239_);
lean_closure_set(v___f_2246_, 2, v___x_2243_);
lean_closure_set(v___f_2246_, 3, v_toPure_2242_);
lean_inc(v_toPure_2242_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2247_, 0, v_toPure_2242_);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_box(0);
v___x_2250_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
lean_inc(v_toPure_2242_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2251_, 0, v___x_2250_);
lean_closure_set(v___f_2251_, 1, v_toPure_2242_);
lean_closure_set(v___f_2251_, 2, v___x_2249_);
lean_inc_ref(v___f_2247_);
lean_inc(v_toBind_2241_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2252_, 0, v___x_2245_);
lean_closure_set(v___f_2252_, 1, v_toPure_2242_);
lean_closure_set(v___f_2252_, 2, v___x_2244_);
lean_closure_set(v___f_2252_, 3, v_resOrders_2239_);
lean_closure_set(v___f_2252_, 4, v___x_2243_);
lean_closure_set(v___f_2252_, 5, v___x_2248_);
lean_closure_set(v___f_2252_, 6, v_toBind_2241_);
lean_closure_set(v___f_2252_, 7, v___f_2247_);
lean_closure_set(v___f_2252_, 8, v___x_2250_);
lean_closure_set(v___f_2252_, 9, v___x_2249_);
lean_closure_set(v___f_2252_, 10, v___f_2251_);
lean_closure_set(v___f_2252_, 11, v___f_2247_);
v___x_2253_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2252_, v___x_2248_, v___x_2250_, lean_box(0));
v___x_2254_ = lean_apply_4(v_toBind_2241_, lean_box(0), lean_box(0), v___x_2253_, v___f_2246_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2255_, lean_object* v_inst_2256_, lean_object* v_resOrders_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2256_, v_resOrders_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2259_){
_start:
{
lean_object* v_structName_2260_; 
v_structName_2260_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_structName_2260_);
return v_structName_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2261_);
lean_dec_ref(v_x_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2263_, lean_object* v_result_2264_, lean_object* v_____r_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_apply_2(v_toPure_2263_, lean_box(0), v_result_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2267_, lean_object* v_inst_2268_, lean_object* v_structName_2269_, lean_object* v_toBind_2270_, lean_object* v_result_2271_){
_start:
{
lean_object* v_resolutionOrder_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_resolutionOrder_2272_ = lean_ctor_get(v_result_2271_, 0);
lean_inc_ref(v_resolutionOrder_2272_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2273_, 0, v_toPure_2267_);
lean_closure_set(v___f_2273_, 1, v_result_2271_);
v___x_2274_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2268_, v_structName_2269_, v_resolutionOrder_2272_);
v___x_2275_ = lean_apply_4(v_toBind_2270_, lean_box(0), lean_box(0), v___x_2274_, v___f_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v___x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_array_get_borrowed(v___x_2278_, v_x_2277_, v___x_2276_);
lean_inc(v___x_2279_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object* v___x_2280_, lean_object* v_x_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__5(v___x_2280_, v_x_2281_);
lean_dec_ref(v_x_2281_);
lean_dec(v___x_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_snd_2283_, lean_object* v_x1_2284_, lean_object* v_x2_2285_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_name_eq(v_x2_2285_, v_snd_2283_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_array_push(v_x1_2284_, v_x2_2285_);
return v___x_2287_;
}
else
{
lean_dec(v_x2_2285_);
return v_x1_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v_snd_2288_, lean_object* v_x1_2289_, lean_object* v_x2_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v_snd_2288_, v_x1_2289_, v_x2_2290_);
lean_dec(v_snd_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v_snd_2292_, lean_object* v_x_2293_){
_start:
{
uint8_t v___x_2294_; 
v___x_2294_ = lean_name_eq(v_x_2293_, v_snd_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v_snd_2295_, lean_object* v_x_2296_){
_start:
{
uint8_t v_res_2297_; lean_object* v_r_2298_; 
v_res_2297_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v_snd_2295_, v_x_2296_);
lean_dec(v_x_2296_);
lean_dec(v_snd_2295_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2299_, lean_object* v_parentNames_2300_, lean_object* v_x_2301_){
_start:
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_inc(v_x_2301_);
v___x_2302_ = l_Array_contains___redArg(v___x_2299_, v_parentNames_2300_, v_x_2301_);
v___x_2303_ = lean_box(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v_x_2301_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2305_, lean_object* v___f_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2308_ = lean_array_get_size(v_x_2307_);
v___x_2309_ = lean_mk_empty_array_with_capacity(v___x_2305_);
v___x_2310_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2311_ = lean_nat_dec_lt(v___x_2305_, v___x_2308_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v_x_2307_);
lean_dec_ref(v___f_2306_);
return v___x_2309_;
}
else
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_nat_dec_le(v___x_2308_, v___x_2308_);
if (v___x_2312_ == 0)
{
if (v___x_2311_ == 0)
{
lean_dec_ref(v_x_2307_);
lean_dec_ref(v___f_2306_);
return v___x_2309_;
}
else
{
size_t v___x_2313_; size_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = ((size_t)0ULL);
v___x_2314_ = lean_usize_of_nat(v___x_2308_);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2310_, v___f_2306_, v_x_2307_, v___x_2313_, v___x_2314_, v___x_2309_);
return v___x_2315_;
}
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2310_, v___f_2306_, v_x_2307_, v___x_2316_, v___x_2317_, v___x_2309_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2319_, lean_object* v___f_2320_, lean_object* v_x_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2319_, v___f_2320_, v_x_2321_);
lean_dec(v___x_2319_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v___f_2323_, lean_object* v_x1_2324_, lean_object* v_x2_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_array_2330_; lean_object* v_start_2331_; lean_object* v_stop_2332_; lean_object* v___y_2334_; uint8_t v___x_2341_; 
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_array_get_size(v_x2_2325_);
lean_inc_ref(v_x2_2325_);
v___x_2328_ = l_Array_toSubarray___redArg(v_x2_2325_, v___x_2326_, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2330_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_array_2330_);
v_start_2331_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_start_2331_);
v_stop_2332_ = lean_ctor_get(v___x_2328_, 2);
lean_inc(v_stop_2332_);
lean_dec_ref(v___x_2328_);
v___x_2341_ = lean_nat_dec_lt(v_start_2331_, v_stop_2332_);
if (v___x_2341_ == 0)
{
lean_dec(v_stop_2332_);
lean_dec(v_start_2331_);
lean_dec_ref(v_array_2330_);
lean_dec_ref(v_x2_2325_);
lean_dec_ref(v___f_2323_);
return v_x1_2324_;
}
else
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_array_get_size(v_array_2330_);
v___x_2343_ = lean_nat_dec_le(v_stop_2332_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec(v_stop_2332_);
v___y_2334_ = v___x_2342_;
goto v___jp_2333_;
}
else
{
v___y_2334_ = v_stop_2332_;
goto v___jp_2333_;
}
}
v___jp_2333_:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_nat_dec_lt(v_start_2331_, v___y_2334_);
if (v___x_2335_ == 0)
{
lean_dec(v___y_2334_);
lean_dec(v_start_2331_);
lean_dec_ref(v_array_2330_);
lean_dec_ref(v_x2_2325_);
lean_dec_ref(v___f_2323_);
return v_x1_2324_;
}
else
{
size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2336_ = lean_usize_of_nat(v_start_2331_);
lean_dec(v_start_2331_);
v___x_2337_ = lean_usize_of_nat(v___y_2334_);
lean_dec(v___y_2334_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2329_, v___f_2323_, v_array_2330_, v___x_2336_, v___x_2337_);
v___x_2339_ = lean_unbox(v___x_2338_);
lean_dec(v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec_ref(v_x2_2325_);
return v_x1_2324_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_array_push(v_x1_2324_, v_x2_2325_);
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v_toPure_2345_, lean_object* v___x_2346_, lean_object* v_fst_2347_, lean_object* v_fst_2348_, lean_object* v___f_2349_, uint8_t v_relaxed_2350_, lean_object* v_parentNames_2351_, lean_object* v_snd_2352_, lean_object* v___f_2353_, lean_object* v_____x_2354_){
_start:
{
lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v_fst_2363_; lean_object* v_snd_2364_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v_defects_2368_; uint8_t v___x_2382_; 
v_fst_2363_ = lean_ctor_get(v_____x_2354_, 0);
lean_inc(v_fst_2363_);
v_snd_2364_ = lean_ctor_get(v_____x_2354_, 1);
lean_inc(v_snd_2364_);
lean_dec_ref(v_____x_2354_);
lean_inc(v_snd_2364_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2365_, 0, v_snd_2364_);
lean_inc(v___x_2346_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2366_, 0, v___x_2346_);
lean_closure_set(v___f_2366_, 1, v___f_2365_);
v___x_2382_ = lean_unbox(v_fst_2363_);
lean_dec(v_fst_2363_);
if (v___x_2382_ == 0)
{
if (v_relaxed_2350_ == 0)
{
lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___y_2386_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2410_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2383_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2351_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2384_, 0, v___x_2383_);
lean_closure_set(v___f_2384_, 1, v_parentNames_2351_);
v___x_2421_ = lean_array_get_size(v_fst_2348_);
v___x_2422_ = lean_mk_empty_array_with_capacity(v___x_2346_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2424_ = lean_nat_dec_lt(v___x_2346_, v___x_2421_);
if (v___x_2424_ == 0)
{
v___y_2410_ = v___x_2422_;
goto v___jp_2409_;
}
else
{
lean_object* v___f_2425_; lean_object* v___f_2426_; uint8_t v___x_2427_; 
lean_inc(v_snd_2364_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_2425_, 0, v_snd_2364_);
v___f_2426_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10), 3, 1);
lean_closure_set(v___f_2426_, 0, v___f_2425_);
v___x_2427_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
if (v___x_2427_ == 0)
{
if (v___x_2424_ == 0)
{
lean_dec_ref(v___f_2426_);
v___y_2410_ = v___x_2422_;
goto v___jp_2409_;
}
else
{
size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = ((size_t)0ULL);
v___x_2429_ = lean_usize_of_nat(v___x_2421_);
lean_inc(v_fst_2348_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2423_, v___f_2426_, v_fst_2348_, v___x_2428_, v___x_2429_, v___x_2422_);
v___y_2410_ = v___x_2430_;
goto v___jp_2409_;
}
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((size_t)0ULL);
v___x_2432_ = lean_usize_of_nat(v___x_2421_);
lean_inc(v_fst_2348_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2423_, v___f_2426_, v_fst_2348_, v___x_2431_, v___x_2432_, v___x_2422_);
v___y_2410_ = v___x_2433_;
goto v___jp_2409_;
}
}
v___jp_2385_:
{
lean_object* v_conflicts_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_defects_2394_; 
v_conflicts_2387_ = l_Array_eraseReps___redArg(v___x_2383_, v___y_2386_);
lean_inc(v_snd_2364_);
v___x_2388_ = l_Array_contains___redArg(v___x_2383_, v_parentNames_2351_, v_snd_2364_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2390_ = lean_array_size(v_conflicts_2387_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2389_, v___f_2384_, v_sz_2390_, v___x_2391_, v_conflicts_2387_);
lean_inc(v_snd_2364_);
v___x_2393_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2393_, 0, v_snd_2364_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*2, v___x_2388_);
v_defects_2394_ = lean_array_push(v_snd_2352_, v___x_2393_);
v_defects_2368_ = v_defects_2394_;
goto v___jp_2367_;
}
v___jp_2395_:
{
lean_object* v___x_2401_; 
v___x_2401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2398_, v___y_2399_, v___y_2397_, v___y_2396_, v___y_2400_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2400_);
lean_dec(v___y_2399_);
v___y_2386_ = v___x_2401_;
goto v___jp_2385_;
}
v___jp_2402_:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_nat_dec_le(v___y_2407_, v___y_2403_);
if (v___x_2408_ == 0)
{
lean_dec(v___y_2403_);
lean_inc(v___y_2407_);
v___y_2396_ = v___y_2407_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v___y_2405_;
v___y_2399_ = v___y_2406_;
v___y_2400_ = v___y_2407_;
goto v___jp_2395_;
}
else
{
v___y_2396_ = v___y_2407_;
v___y_2397_ = v___y_2404_;
v___y_2398_ = v___y_2405_;
v___y_2399_ = v___y_2406_;
v___y_2400_ = v___y_2403_;
goto v___jp_2395_;
}
}
v___jp_2409_:
{
lean_object* v___x_2411_; size_t v_sz_2412_; size_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2412_ = lean_array_size(v___y_2410_);
v___x_2413_ = ((size_t)0ULL);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2411_, v___f_2353_, v_sz_2412_, v___x_2413_, v___y_2410_);
v___x_2415_ = lean_array_get_size(v___x_2414_);
v___x_2416_ = lean_nat_dec_eq(v___x_2415_, v___x_2346_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2417_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0));
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_sub(v___x_2415_, v___x_2418_);
v___x_2420_ = lean_nat_dec_le(v___x_2346_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_inc(v___x_2419_);
v___y_2403_ = v___x_2419_;
v___y_2404_ = v___x_2414_;
v___y_2405_ = v___x_2417_;
v___y_2406_ = v___x_2415_;
v___y_2407_ = v___x_2419_;
goto v___jp_2402_;
}
else
{
lean_inc(v___x_2346_);
v___y_2403_ = v___x_2419_;
v___y_2404_ = v___x_2414_;
v___y_2405_ = v___x_2417_;
v___y_2406_ = v___x_2415_;
v___y_2407_ = v___x_2346_;
goto v___jp_2402_;
}
}
else
{
v___y_2386_ = v___x_2414_;
goto v___jp_2385_;
}
}
}
else
{
lean_dec_ref(v___f_2353_);
lean_dec_ref(v_parentNames_2351_);
v_defects_2368_ = v_snd_2352_;
goto v___jp_2367_;
}
}
else
{
lean_dec_ref(v___f_2353_);
lean_dec_ref(v_parentNames_2351_);
v_defects_2368_ = v_snd_2352_;
goto v___jp_2367_;
}
v___jp_2355_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___y_2356_);
lean_ctor_set(v___x_2359_, 1, v___y_2357_);
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___y_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = lean_apply_2(v_toPure_2345_, lean_box(0), v___x_2361_);
return v___x_2362_;
}
v___jp_2367_:
{
lean_object* v_resOrder_2369_; lean_object* v___x_2370_; size_t v_sz_2371_; size_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_resOrder_2369_ = lean_array_push(v_fst_2347_, v_snd_2364_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2371_ = lean_array_size(v_fst_2348_);
v___x_2372_ = ((size_t)0ULL);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2370_, v___f_2366_, v_sz_2371_, v___x_2372_, v_fst_2348_);
v___x_2374_ = lean_array_get_size(v___x_2373_);
v___x_2375_ = lean_mk_empty_array_with_capacity(v___x_2346_);
v___x_2376_ = lean_nat_dec_lt(v___x_2346_, v___x_2374_);
lean_dec(v___x_2346_);
if (v___x_2376_ == 0)
{
lean_dec(v___x_2373_);
lean_dec_ref(v___f_2349_);
v___y_2356_ = v_resOrder_2369_;
v___y_2357_ = v_defects_2368_;
v___y_2358_ = v___x_2375_;
goto v___jp_2355_;
}
else
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_nat_dec_le(v___x_2374_, v___x_2374_);
if (v___x_2377_ == 0)
{
if (v___x_2376_ == 0)
{
lean_dec(v___x_2373_);
lean_dec_ref(v___f_2349_);
v___y_2356_ = v_resOrder_2369_;
v___y_2357_ = v_defects_2368_;
v___y_2358_ = v___x_2375_;
goto v___jp_2355_;
}
else
{
size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_usize_of_nat(v___x_2374_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2370_, v___f_2349_, v___x_2373_, v___x_2372_, v___x_2378_, v___x_2375_);
v___y_2356_ = v_resOrder_2369_;
v___y_2357_ = v_defects_2368_;
v___y_2358_ = v___x_2379_;
goto v___jp_2355_;
}
}
else
{
size_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_usize_of_nat(v___x_2374_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2370_, v___f_2349_, v___x_2373_, v___x_2372_, v___x_2380_, v___x_2375_);
v___y_2356_ = v_resOrder_2369_;
v___y_2357_ = v_defects_2368_;
v___y_2358_ = v___x_2381_;
goto v___jp_2355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object* v_toPure_2434_, lean_object* v___x_2435_, lean_object* v_fst_2436_, lean_object* v_fst_2437_, lean_object* v___f_2438_, lean_object* v_relaxed_2439_, lean_object* v_parentNames_2440_, lean_object* v_snd_2441_, lean_object* v___f_2442_, lean_object* v_____x_2443_){
_start:
{
uint8_t v_relaxed_boxed_2444_; lean_object* v_res_2445_; 
v_relaxed_boxed_2444_ = lean_unbox(v_relaxed_2439_);
v_res_2445_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__11(v_toPure_2434_, v___x_2435_, v_fst_2436_, v_fst_2437_, v___f_2438_, v_relaxed_boxed_2444_, v_parentNames_2440_, v_snd_2441_, v___f_2442_, v_____x_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v___x_2446_, lean_object* v_toPure_2447_, lean_object* v___f_2448_, uint8_t v_relaxed_2449_, lean_object* v_parentNames_2450_, lean_object* v___f_2451_, lean_object* v_inst_2452_, lean_object* v_toBind_2453_, lean_object* v_x_2454_, lean_object* v_____s_2455_){
_start:
{
lean_object* v_snd_2456_; lean_object* v_fst_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2481_; 
v_snd_2456_ = lean_ctor_get(v_____s_2455_, 1);
v_fst_2457_ = lean_ctor_get(v_____s_2455_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_____s_2455_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2459_ = v_____s_2455_;
v_isShared_2460_ = v_isSharedCheck_2481_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snd_2456_);
lean_inc(v_fst_2457_);
lean_dec(v_____s_2455_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2481_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2480_; 
v_fst_2461_ = lean_ctor_get(v_snd_2456_, 0);
v_snd_2462_ = lean_ctor_get(v_snd_2456_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_snd_2456_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2464_ = v_snd_2456_;
v_isShared_2465_ = v_isSharedCheck_2480_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_dec(v_snd_2456_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2480_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_array_get_size(v_fst_2457_);
v___x_2467_ = lean_nat_dec_eq(v___x_2466_, v___x_2446_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_del_object(v___x_2464_);
lean_del_object(v___x_2459_);
v___x_2468_ = lean_box(v_relaxed_2449_);
lean_inc(v_fst_2457_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_2469_, 0, v_toPure_2447_);
lean_closure_set(v___f_2469_, 1, v___x_2446_);
lean_closure_set(v___f_2469_, 2, v_fst_2461_);
lean_closure_set(v___f_2469_, 3, v_fst_2457_);
lean_closure_set(v___f_2469_, 4, v___f_2448_);
lean_closure_set(v___f_2469_, 5, v___x_2468_);
lean_closure_set(v___f_2469_, 6, v_parentNames_2450_);
lean_closure_set(v___f_2469_, 7, v_snd_2462_);
lean_closure_set(v___f_2469_, 8, v___f_2451_);
v___x_2470_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2452_, v_fst_2457_);
v___x_2471_ = lean_apply_4(v_toBind_2453_, lean_box(0), lean_box(0), v___x_2470_, v___f_2469_);
return v___x_2471_;
}
else
{
lean_object* v___x_2473_; 
lean_dec(v_toBind_2453_);
lean_dec_ref(v_inst_2452_);
lean_dec_ref(v___f_2451_);
lean_dec_ref(v_parentNames_2450_);
lean_dec_ref(v___f_2448_);
lean_dec(v___x_2446_);
if (v_isShared_2465_ == 0)
{
v___x_2473_ = v___x_2464_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_fst_2461_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_snd_2462_);
v___x_2473_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2473_);
v___x_2475_ = v___x_2459_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_fst_2457_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = lean_apply_2(v_toPure_2447_, lean_box(0), v___x_2476_);
return v___x_2477_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v___x_2482_, lean_object* v_toPure_2483_, lean_object* v___f_2484_, lean_object* v_relaxed_2485_, lean_object* v_parentNames_2486_, lean_object* v___f_2487_, lean_object* v_inst_2488_, lean_object* v_toBind_2489_, lean_object* v_x_2490_, lean_object* v_____s_2491_){
_start:
{
uint8_t v_relaxed_boxed_2492_; lean_object* v_res_2493_; 
v_relaxed_boxed_2492_ = lean_unbox(v_relaxed_2485_);
v_res_2493_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v___x_2482_, v_toPure_2483_, v___f_2484_, v_relaxed_boxed_2492_, v_parentNames_2486_, v___f_2487_, v_inst_2488_, v_toBind_2489_, v_x_2490_, v_____s_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v_toPure_2500_, lean_object* v___f_2501_, uint8_t v_relaxed_2502_, lean_object* v_parentNames_2503_, lean_object* v_inst_2504_, lean_object* v_toBind_2505_, lean_object* v_structName_2506_, lean_object* v___f_2507_, lean_object* v___f_2508_, lean_object* v_parentResOrders_2509_){
_start:
{
lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___y_2515_; lean_object* v_j_2524_; lean_object* v_as_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2510_ = lean_unsigned_to_nat(0u);
v___f_2511_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0));
v___x_2512_ = lean_box(v_relaxed_2502_);
lean_inc(v_toBind_2505_);
lean_inc_ref(v_inst_2504_);
lean_inc_ref(v_parentNames_2503_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2513_, 0, v___x_2510_);
lean_closure_set(v___f_2513_, 1, v_toPure_2500_);
lean_closure_set(v___f_2513_, 2, v___f_2501_);
lean_closure_set(v___f_2513_, 3, v___x_2512_);
lean_closure_set(v___f_2513_, 4, v_parentNames_2503_);
lean_closure_set(v___f_2513_, 5, v___f_2511_);
lean_closure_set(v___f_2513_, 6, v_inst_2504_);
lean_closure_set(v___f_2513_, 7, v_toBind_2505_);
v_j_2524_ = lean_array_get_size(v_parentResOrders_2509_);
v_as_2525_ = lean_array_push(v_parentResOrders_2509_, v_parentNames_2503_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2510_, v_as_2525_, v_j_2524_);
v___x_2527_ = lean_array_get_size(v___x_2526_);
v___x_2528_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2));
v___x_2529_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2530_ = lean_nat_dec_lt(v___x_2510_, v___x_2527_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___f_2508_);
v___y_2515_ = v___x_2528_;
goto v___jp_2514_;
}
else
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_nat_dec_le(v___x_2527_, v___x_2527_);
if (v___x_2531_ == 0)
{
if (v___x_2530_ == 0)
{
lean_dec_ref(v___x_2526_);
lean_dec_ref(v___f_2508_);
v___y_2515_ = v___x_2528_;
goto v___jp_2514_;
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2527_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2529_, v___f_2508_, v___x_2526_, v___x_2532_, v___x_2533_, v___x_2528_);
v___y_2515_ = v___x_2534_;
goto v___jp_2514_;
}
}
else
{
size_t v___x_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = ((size_t)0ULL);
v___x_2536_ = lean_usize_of_nat(v___x_2527_);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2529_, v___f_2508_, v___x_2526_, v___x_2535_, v___x_2536_, v___x_2528_);
v___y_2515_ = v___x_2537_;
goto v___jp_2514_;
}
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_resOrder_2518_; lean_object* v_defects_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2516_ = lean_unsigned_to_nat(1u);
v___x_2517_ = lean_mk_empty_array_with_capacity(v___x_2516_);
v_resOrder_2518_ = lean_array_push(v___x_2517_, v_structName_2506_);
v_defects_2519_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_resOrder_2518_);
lean_ctor_set(v___x_2520_, 1, v_defects_2519_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___y_2515_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_2504_, v___f_2513_, v___x_2521_);
v___x_2523_ = lean_apply_4(v_toBind_2505_, lean_box(0), lean_box(0), v___x_2522_, v___f_2507_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v_toPure_2538_, lean_object* v___f_2539_, lean_object* v_relaxed_2540_, lean_object* v_parentNames_2541_, lean_object* v_inst_2542_, lean_object* v_toBind_2543_, lean_object* v_structName_2544_, lean_object* v___f_2545_, lean_object* v___f_2546_, lean_object* v_parentResOrders_2547_){
_start:
{
uint8_t v_relaxed_boxed_2548_; lean_object* v_res_2549_; 
v_relaxed_boxed_2548_ = lean_unbox(v_relaxed_2540_);
v_res_2549_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v_toPure_2538_, v___f_2539_, v_relaxed_boxed_2548_, v_parentNames_2541_, v_inst_2542_, v_toBind_2543_, v_structName_2544_, v___f_2545_, v___f_2546_, v_parentResOrders_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2551_ = lean_array_get_size(v_x_2550_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = lean_nat_dec_eq(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
uint8_t v___x_2554_; 
v___x_2554_ = 1;
return v___x_2554_;
}
else
{
uint8_t v___x_2555_; 
v___x_2555_ = 0;
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2556_){
_start:
{
uint8_t v_res_2557_; lean_object* v_r_2558_; 
v_res_2557_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2556_);
lean_dec_ref(v_x_2556_);
v_r_2558_ = lean_box(v_res_2557_);
return v_r_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2559_, lean_object* v_x1_2560_, lean_object* v_x2_2561_){
_start:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
lean_inc_ref(v_x2_2561_);
v___x_2562_ = lean_apply_1(v___f_2559_, v_x2_2561_);
v___x_2563_ = lean_unbox(v___x_2562_);
if (v___x_2563_ == 0)
{
lean_dec_ref(v_x2_2561_);
return v_x1_2560_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_array_push(v_x1_2560_, v_x2_2561_);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2565_, lean_object* v_____s_2566_){
_start:
{
lean_object* v_snd_2567_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
v_snd_2567_ = lean_ctor_get(v_____s_2566_, 1);
lean_inc(v_snd_2567_);
lean_dec_ref(v_____s_2566_);
v_fst_2568_ = lean_ctor_get(v_snd_2567_, 0);
v_snd_2569_ = lean_ctor_get(v_snd_2567_, 1);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_snd_2567_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2571_ = v_snd_2567_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snd_2569_);
lean_inc(v_fst_2568_);
lean_dec(v_snd_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2568_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_snd_2569_);
v___x_2574_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_apply_2(v_toPure_2565_, lean_box(0), v___x_2574_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2578_, lean_object* v_____do__lift_2579_){
_start:
{
lean_object* v_resolutionOrder_2580_; lean_object* v___x_2581_; 
v_resolutionOrder_2580_ = lean_ctor_get(v_____do__lift_2579_, 0);
lean_inc_ref(v_resolutionOrder_2580_);
lean_dec_ref(v_____do__lift_2579_);
v___x_2581_ = lean_apply_2(v_toPure_2578_, lean_box(0), v_resolutionOrder_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_structName_2588_, lean_object* v_parentNames_2589_, uint8_t v_relaxed_2590_){
_start:
{
lean_object* v_toApplicative_2591_; lean_object* v_toBind_2592_; lean_object* v_toPure_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; lean_object* v___f_2599_; size_t v_sz_2600_; size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_toApplicative_2591_ = lean_ctor_get(v_inst_2586_, 0);
v_toBind_2592_ = lean_ctor_get(v_inst_2586_, 1);
lean_inc(v_toBind_2592_);
v_toPure_2593_ = lean_ctor_get(v_toApplicative_2591_, 1);
v___f_2594_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc(v_toPure_2593_);
v___f_2595_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2595_, 0, v_toPure_2593_);
lean_inc(v_toBind_2592_);
lean_inc_ref(v_inst_2586_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2596_, 0, v_inst_2586_);
lean_closure_set(v___f_2596_, 1, v_inst_2587_);
lean_closure_set(v___f_2596_, 2, v_toBind_2592_);
lean_closure_set(v___f_2596_, 3, v___f_2595_);
lean_inc(v_toPure_2593_);
v___f_2597_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2597_, 0, v_toPure_2593_);
v___x_2598_ = lean_box(v_relaxed_2590_);
lean_inc(v_toBind_2592_);
lean_inc_ref(v_inst_2586_);
lean_inc_ref(v_parentNames_2589_);
lean_inc(v_toPure_2593_);
v___f_2599_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 10, 9);
lean_closure_set(v___f_2599_, 0, v_toPure_2593_);
lean_closure_set(v___f_2599_, 1, v___f_2594_);
lean_closure_set(v___f_2599_, 2, v___x_2598_);
lean_closure_set(v___f_2599_, 3, v_parentNames_2589_);
lean_closure_set(v___f_2599_, 4, v_inst_2586_);
lean_closure_set(v___f_2599_, 5, v_toBind_2592_);
lean_closure_set(v___f_2599_, 6, v_structName_2588_);
lean_closure_set(v___f_2599_, 7, v___f_2597_);
lean_closure_set(v___f_2599_, 8, v___f_2594_);
v_sz_2600_ = lean_array_size(v_parentNames_2589_);
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2586_, v___f_2596_, v_sz_2600_, v___x_2601_, v_parentNames_2589_);
v___x_2603_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2602_, v___f_2599_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2604_, lean_object* v_toPure_2605_, lean_object* v___f_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, uint8_t v_relaxed_2609_, lean_object* v_toBind_2610_, lean_object* v___f_2611_, lean_object* v_env_2612_){
_start:
{
lean_object* v___x_2613_; 
lean_inc_ref(v_env_2612_);
v___x_2613_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2612_, v_structName_2604_);
if (lean_obj_tag(v___x_2613_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v_env_2612_);
lean_dec(v___f_2611_);
lean_dec(v_toBind_2610_);
lean_dec_ref(v_inst_2608_);
lean_dec_ref(v_inst_2607_);
lean_dec_ref(v___f_2606_);
lean_dec(v_structName_2604_);
v_val_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_val_2614_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_val_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_apply_2(v_toPure_2605_, lean_box(0), v___x_2616_);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; size_t v_sz_2620_; size_t v___x_2621_; lean_object* v_parentNames_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v___x_2613_);
lean_dec(v_toPure_2605_);
lean_inc(v_structName_2604_);
v___x_2618_ = l_Lean_getStructureParentInfo(v_env_2612_, v_structName_2604_);
v___x_2619_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2620_ = lean_array_size(v___x_2618_);
v___x_2621_ = ((size_t)0ULL);
v_parentNames_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2619_, v___f_2606_, v_sz_2620_, v___x_2621_, v___x_2618_);
v___x_2623_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2607_, v_inst_2608_, v_structName_2604_, v_parentNames_2622_, v_relaxed_2609_);
v___x_2624_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2623_, v___f_2611_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2625_, lean_object* v_toPure_2626_, lean_object* v___f_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_relaxed_2630_, lean_object* v_toBind_2631_, lean_object* v___f_2632_, lean_object* v_env_2633_){
_start:
{
uint8_t v_relaxed_boxed_2634_; lean_object* v_res_2635_; 
v_relaxed_boxed_2634_ = lean_unbox(v_relaxed_2630_);
v_res_2635_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2625_, v_toPure_2626_, v___f_2627_, v_inst_2628_, v_inst_2629_, v_relaxed_boxed_2634_, v_toBind_2631_, v___f_2632_, v_env_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_structName_2638_, uint8_t v_relaxed_2639_){
_start:
{
lean_object* v_toApplicative_2640_; lean_object* v_toBind_2641_; lean_object* v_getEnv_2642_; lean_object* v_toPure_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; 
v_toApplicative_2640_ = lean_ctor_get(v_inst_2636_, 0);
v_toBind_2641_ = lean_ctor_get(v_inst_2636_, 1);
lean_inc(v_toBind_2641_);
v_getEnv_2642_ = lean_ctor_get(v_inst_2637_, 0);
lean_inc(v_getEnv_2642_);
v_toPure_2643_ = lean_ctor_get(v_toApplicative_2640_, 1);
lean_inc(v_toPure_2643_);
v___f_2644_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_toBind_2641_);
lean_inc(v_structName_2638_);
lean_inc_ref(v_inst_2637_);
lean_inc(v_toPure_2643_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2645_, 0, v_toPure_2643_);
lean_closure_set(v___f_2645_, 1, v_inst_2637_);
lean_closure_set(v___f_2645_, 2, v_structName_2638_);
lean_closure_set(v___f_2645_, 3, v_toBind_2641_);
v___x_2646_ = lean_box(v_relaxed_2639_);
lean_inc(v_toBind_2641_);
v___f_2647_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2647_, 0, v_structName_2638_);
lean_closure_set(v___f_2647_, 1, v_toPure_2643_);
lean_closure_set(v___f_2647_, 2, v___f_2644_);
lean_closure_set(v___f_2647_, 3, v_inst_2636_);
lean_closure_set(v___f_2647_, 4, v_inst_2637_);
lean_closure_set(v___f_2647_, 5, v___x_2646_);
lean_closure_set(v___f_2647_, 6, v_toBind_2641_);
lean_closure_set(v___f_2647_, 7, v___f_2645_);
v___x_2648_ = lean_apply_4(v_toBind_2641_, lean_box(0), lean_box(0), v_getEnv_2642_, v___f_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_toBind_2651_, lean_object* v___f_2652_, lean_object* v_parentName_2653_){
_start:
{
uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = 1;
v___x_2655_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2649_, v_inst_2650_, v_parentName_2653_, v___x_2654_);
v___x_2656_ = lean_apply_4(v_toBind_2651_, lean_box(0), lean_box(0), v___x_2655_, v___f_2652_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_structName_2659_, lean_object* v_relaxed_2660_){
_start:
{
uint8_t v_relaxed_boxed_2661_; lean_object* v_res_2662_; 
v_relaxed_boxed_2661_ = lean_unbox(v_relaxed_2660_);
v_res_2662_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2657_, v_inst_2658_, v_structName_2659_, v_relaxed_boxed_2661_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_structName_2665_, lean_object* v_parentNames_2666_, lean_object* v_relaxed_2667_){
_start:
{
uint8_t v_relaxed_boxed_2668_; lean_object* v_res_2669_; 
v_relaxed_boxed_2668_ = lean_unbox(v_relaxed_2667_);
v_res_2669_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2663_, v_inst_2664_, v_structName_2665_, v_parentNames_2666_, v_relaxed_boxed_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_structName_2673_, uint8_t v_relaxed_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2671_, v_inst_2672_, v_structName_2673_, v_relaxed_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_structName_2679_, lean_object* v_relaxed_2680_){
_start:
{
uint8_t v_relaxed_boxed_2681_; lean_object* v_res_2682_; 
v_relaxed_boxed_2681_ = lean_unbox(v_relaxed_2680_);
v_res_2682_ = l_Lean_computeStructureResolutionOrder(v_m_2676_, v_inst_2677_, v_inst_2678_, v_structName_2679_, v_relaxed_boxed_2681_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_structName_2686_, lean_object* v_parentNames_2687_, uint8_t v_relaxed_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2684_, v_inst_2685_, v_structName_2686_, v_parentNames_2687_, v_relaxed_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_structName_2693_, lean_object* v_parentNames_2694_, lean_object* v_relaxed_2695_){
_start:
{
uint8_t v_relaxed_boxed_2696_; lean_object* v_res_2697_; 
v_relaxed_boxed_2696_ = lean_unbox(v_relaxed_2695_);
v_res_2697_ = l_Lean_mergeStructureResolutionOrders(v_m_2690_, v_inst_2691_, v_inst_2692_, v_structName_2693_, v_parentNames_2694_, v_relaxed_boxed_2696_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2698_){
_start:
{
lean_object* v_resolutionOrder_2699_; 
v_resolutionOrder_2699_ = lean_ctor_get(v_x_2698_, 0);
lean_inc_ref(v_resolutionOrder_2699_);
return v_resolutionOrder_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2700_);
lean_dec_ref(v_x_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_structName_2705_){
_start:
{
lean_object* v_toApplicative_2706_; lean_object* v_toFunctor_2707_; lean_object* v_map_2708_; lean_object* v___f_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_toApplicative_2706_ = lean_ctor_get(v_inst_2703_, 0);
v_toFunctor_2707_ = lean_ctor_get(v_toApplicative_2706_, 0);
v_map_2708_ = lean_ctor_get(v_toFunctor_2707_, 0);
lean_inc(v_map_2708_);
v___f_2709_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2710_ = 1;
v___x_2711_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2703_, v_inst_2704_, v_structName_2705_, v___x_2710_);
v___x_2712_ = lean_apply_4(v_map_2708_, lean_box(0), lean_box(0), v___f_2709_, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_structName_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2714_, v_inst_2715_, v_structName_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2718_, lean_object* v_structName_2719_, lean_object* v_x_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Array_erase___redArg(v___x_2718_, v_x_2720_, v_structName_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_structName_2724_){
_start:
{
lean_object* v_toApplicative_2725_; lean_object* v_toFunctor_2726_; lean_object* v_map_2727_; lean_object* v___x_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_toApplicative_2725_ = lean_ctor_get(v_inst_2722_, 0);
v_toFunctor_2726_ = lean_ctor_get(v_toApplicative_2725_, 0);
v_map_2727_ = lean_ctor_get(v_toFunctor_2726_, 0);
lean_inc(v_map_2727_);
v___x_2728_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2724_);
v___f_2729_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2729_, 0, v___x_2728_);
lean_closure_set(v___f_2729_, 1, v_structName_2724_);
v___x_2730_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2722_, v_inst_2723_, v_structName_2724_);
v___x_2731_ = lean_apply_4(v_map_2727_, lean_box(0), lean_box(0), v___f_2729_, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_structName_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_getAllParentStructures___redArg(v_inst_2733_, v_inst_2734_, v_structName_2735_);
return v___x_2736_;
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
l_Lean_instInhabitedStructureInfo_default = _init_l_Lean_instInhabitedStructureInfo_default();
lean_mark_persistent(l_Lean_instInhabitedStructureInfo_default);
l_Lean_instInhabitedStructureInfo = _init_l_Lean_instInhabitedStructureInfo();
lean_mark_persistent(l_Lean_instInhabitedStructureInfo);
l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default = _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default);
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
res = l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_structureResolutionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_structureResolutionExt);
lean_dec_ref(res);
l_Lean_instInhabitedStructureResolutionOrderResult_default = _init_l_Lean_instInhabitedStructureResolutionOrderResult_default();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionOrderResult_default);
l_Lean_instInhabitedStructureResolutionOrderResult = _init_l_Lean_instInhabitedStructureResolutionOrderResult();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionOrderResult);
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
