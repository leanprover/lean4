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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_392_, lean_object* v_x_393_, lean_object* v_s_394_){
_start:
{
lean_object* v_snd_395_; lean_object* v___x_396_; size_t v_sz_397_; size_t v___x_398_; lean_object* v___x_399_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_snd_395_ = lean_ctor_get(v_s_394_, 1);
v___x_396_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_395_);
v_sz_397_ = lean_array_size(v___x_396_);
v___x_398_ = ((size_t)0ULL);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_397_, v___x_398_, v___x_396_);
v___x_405_ = lean_array_get_size(v___x_399_);
v___x_406_ = lean_nat_dec_eq(v___x_405_, v___x_392_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___y_410_; uint8_t v___x_412_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_sub(v___x_405_, v___x_407_);
v___x_412_ = lean_nat_dec_le(v___x_392_, v___x_408_);
if (v___x_412_ == 0)
{
lean_dec(v___x_392_);
lean_inc(v___x_408_);
v___y_410_ = v___x_408_;
goto v___jp_409_;
}
else
{
v___y_410_ = v___x_392_;
goto v___jp_409_;
}
v___jp_409_:
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_le(v___y_410_, v___x_408_);
if (v___x_411_ == 0)
{
lean_dec(v___x_408_);
lean_inc(v___y_410_);
v___y_401_ = v___y_410_;
v___y_402_ = v___y_410_;
goto v___jp_400_;
}
else
{
v___y_401_ = v___y_410_;
v___y_402_ = v___x_408_;
goto v___jp_400_;
}
}
}
else
{
lean_object* v___x_413_; 
lean_dec(v___x_392_);
lean_inc_ref_n(v___x_399_, 2);
v___x_413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_413_, 0, v___x_399_);
lean_ctor_set(v___x_413_, 1, v___x_399_);
lean_ctor_set(v___x_413_, 2, v___x_399_);
return v___x_413_;
}
v___jp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_399_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_inc_ref_n(v___x_403_, 2);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_414_, lean_object* v_x_415_, lean_object* v_s_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_414_, v_x_415_, v_s_416_);
lean_dec_ref(v_s_416_);
lean_dec_ref(v_x_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_snd_420_; lean_object* v___x_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_snd_420_ = lean_ctor_get(v_x_419_, 1);
v___x_421_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_420_);
v_sz_422_ = lean_array_size(v___x_421_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_422_, v___x_423_, v___x_421_);
v___x_425_ = lean_array_get_size(v___x_424_);
v___x_426_ = lean_nat_dec_eq(v___x_425_, v___x_418_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___y_430_; uint8_t v___x_434_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_sub(v___x_425_, v___x_427_);
v___x_434_ = lean_nat_dec_le(v___x_418_, v___x_428_);
if (v___x_434_ == 0)
{
lean_dec(v___x_418_);
lean_inc(v___x_428_);
v___y_430_ = v___x_428_;
goto v___jp_429_;
}
else
{
v___y_430_ = v___x_418_;
goto v___jp_429_;
}
v___jp_429_:
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_le(v___y_430_, v___x_428_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec(v___x_428_);
lean_inc(v___y_430_);
v___x_432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_424_, v___y_430_, v___y_430_);
lean_dec(v___y_430_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_424_, v___y_430_, v___x_428_);
lean_dec(v___x_428_);
return v___x_433_;
}
}
}
else
{
lean_dec(v___x_418_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_435_, v_x_436_);
lean_dec_ref(v_x_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_ks_442_; lean_object* v_vs_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_467_; 
v_ks_442_ = lean_ctor_get(v_x_438_, 0);
v_vs_443_ = lean_ctor_get(v_x_438_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_445_ = v_x_438_;
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_vs_443_);
lean_inc(v_ks_442_);
lean_dec(v_x_438_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_array_get_size(v_ks_442_);
v___x_448_ = lean_nat_dec_lt(v_x_439_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec(v_x_439_);
v___x_449_ = lean_array_push(v_ks_442_, v_x_440_);
v___x_450_ = lean_array_push(v_vs_443_, v_x_441_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_450_);
lean_ctor_set(v___x_445_, 0, v___x_449_);
v___x_452_ = v___x_445_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v_k_x27_454_; uint8_t v___x_455_; 
v_k_x27_454_ = lean_array_fget_borrowed(v_ks_442_, v_x_439_);
v___x_455_ = lean_name_eq(v_x_440_, v_k_x27_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_457_; 
if (v_isShared_446_ == 0)
{
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_ks_442_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_vs_443_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_x_439_, v___x_458_);
lean_dec(v_x_439_);
v_x_438_ = v___x_457_;
v_x_439_ = v___x_459_;
goto _start;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = lean_array_fset(v_ks_442_, v_x_439_, v_x_440_);
v___x_463_ = lean_array_fset(v_vs_443_, v_x_439_, v_x_441_);
lean_dec(v_x_439_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_463_);
lean_ctor_set(v___x_445_, 0, v___x_462_);
v___x_465_ = v___x_445_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(lean_object* v_n_468_, lean_object* v_k_469_, lean_object* v_v_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_n_468_, v___x_471_, v_k_469_, v_v_470_);
return v___x_472_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_473_; uint64_t v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(1723u);
v___x_474_ = lean_uint64_of_nat(v___x_473_);
return v___x_474_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; 
v___x_475_ = ((size_t)5ULL);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_shift_left(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; 
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_480_ = lean_usize_sub(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_482_, size_t v_x_483_, size_t v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_es_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v_j_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_es_487_ = lean_ctor_get(v_x_482_, 0);
v___x_488_ = ((size_t)5ULL);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_491_ = lean_usize_land(v_x_483_, v___x_490_);
v_j_492_ = lean_usize_to_nat(v___x_491_);
v___x_493_ = lean_array_get_size(v_es_487_);
v___x_494_ = lean_nat_dec_lt(v_j_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_j_492_);
lean_dec(v_x_486_);
lean_dec(v_x_485_);
return v_x_482_;
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_es_487_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_532_);
v___x_496_ = v_x_482_;
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_v_498_; lean_object* v___x_499_; lean_object* v_xs_x27_500_; lean_object* v___y_502_; 
v_v_498_ = lean_array_fget(v_es_487_, v_j_492_);
v___x_499_ = lean_box(0);
v_xs_x27_500_ = lean_array_fset(v_es_487_, v_j_492_, v___x_499_);
switch(lean_obj_tag(v_v_498_))
{
case 0:
{
lean_object* v_key_507_; lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_key_507_ = lean_ctor_get(v_v_498_, 0);
v_val_508_ = lean_ctor_get(v_v_498_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_v_498_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_inc(v_key_507_);
lean_dec(v_v_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_name_eq(v_x_485_, v_key_507_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_510_);
v___x_513_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_507_, v_val_508_, v_x_485_, v_x_486_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___y_502_ = v___x_514_;
goto v___jp_501_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_val_508_);
lean_dec(v_key_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_x_486_);
lean_ctor_set(v___x_510_, 0, v_x_485_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_x_485_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_x_486_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_502_ = v___x_516_;
goto v___jp_501_;
}
}
}
}
case 1:
{
lean_object* v_node_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_node_519_ = lean_ctor_get(v_v_498_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v_v_498_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_node_519_);
lean_dec(v_v_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = lean_usize_shift_right(v_x_483_, v___x_488_);
v___x_524_ = lean_usize_add(v_x_484_, v___x_489_);
v___x_525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_node_519_, v___x_523_, v___x_524_, v_x_485_, v_x_486_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v___y_502_ = v___x_527_;
goto v___jp_501_;
}
}
}
default: 
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_x_485_);
lean_ctor_set(v___x_530_, 1, v_x_486_);
v___y_502_ = v___x_530_;
goto v___jp_501_;
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_array_fset(v_xs_x27_500_, v_j_492_, v___y_502_);
lean_dec(v_j_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_ks_533_; lean_object* v_vs_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_554_; 
v_ks_533_ = lean_ctor_get(v_x_482_, 0);
v_vs_534_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_554_ == 0)
{
v___x_536_ = v_x_482_;
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_vs_534_);
lean_inc(v_ks_533_);
lean_dec(v_x_482_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_ks_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vs_534_);
v___x_539_ = v_reuseFailAlloc_553_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v_newNode_540_; uint8_t v___y_542_; size_t v___x_548_; uint8_t v___x_549_; 
v_newNode_540_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v___x_539_, v_x_485_, v_x_486_);
v___x_548_ = ((size_t)7ULL);
v___x_549_ = lean_usize_dec_le(v___x_548_, v_x_484_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_540_);
v___x_551_ = lean_unsigned_to_nat(4u);
v___x_552_ = lean_nat_dec_lt(v___x_550_, v___x_551_);
lean_dec(v___x_550_);
v___y_542_ = v___x_552_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___x_549_;
goto v___jp_541_;
}
v___jp_541_:
{
if (v___y_542_ == 0)
{
lean_object* v_ks_543_; lean_object* v_vs_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_ks_543_ = lean_ctor_get(v_newNode_540_, 0);
lean_inc_ref(v_ks_543_);
v_vs_544_ = lean_ctor_get(v_newNode_540_, 1);
lean_inc_ref(v_vs_544_);
lean_dec_ref(v_newNode_540_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2);
v___x_547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_x_484_, v_ks_543_, v_vs_544_, v___x_545_, v___x_546_);
lean_dec_ref(v_vs_544_);
lean_dec_ref(v_ks_543_);
return v___x_547_;
}
else
{
return v_newNode_540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(size_t v_depth_555_, lean_object* v_keys_556_, lean_object* v_vals_557_, lean_object* v_i_558_, lean_object* v_entries_559_){
_start:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_get_size(v_keys_556_);
v___x_561_ = lean_nat_dec_lt(v_i_558_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec(v_i_558_);
return v_entries_559_;
}
else
{
lean_object* v_k_562_; lean_object* v_v_563_; uint64_t v___y_565_; 
v_k_562_ = lean_array_fget_borrowed(v_keys_556_, v_i_558_);
v_v_563_ = lean_array_fget_borrowed(v_vals_557_, v_i_558_);
if (lean_obj_tag(v_k_562_) == 0)
{
uint64_t v___x_576_; 
v___x_576_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_565_ = v___x_576_;
goto v___jp_564_;
}
else
{
uint64_t v_hash_577_; 
v_hash_577_ = lean_ctor_get_uint64(v_k_562_, sizeof(void*)*2);
v___y_565_ = v_hash_577_;
goto v___jp_564_;
}
v___jp_564_:
{
size_t v_h_566_; size_t v___x_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v_h_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_h_566_ = lean_uint64_to_usize(v___y_565_);
v___x_567_ = ((size_t)5ULL);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_sub(v_depth_555_, v___x_569_);
v___x_571_ = lean_usize_mul(v___x_567_, v___x_570_);
v_h_572_ = lean_usize_shift_right(v_h_566_, v___x_571_);
v___x_573_ = lean_nat_add(v_i_558_, v___x_568_);
lean_dec(v_i_558_);
lean_inc(v_v_563_);
lean_inc(v_k_562_);
v___x_574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_entries_559_, v_h_572_, v_depth_555_, v_k_562_, v_v_563_);
v_i_558_ = v___x_573_;
v_entries_559_ = v___x_574_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_depth_578_, lean_object* v_keys_579_, lean_object* v_vals_580_, lean_object* v_i_581_, lean_object* v_entries_582_){
_start:
{
size_t v_depth_boxed_583_; lean_object* v_res_584_; 
v_depth_boxed_583_ = lean_unbox_usize(v_depth_578_);
lean_dec(v_depth_578_);
v_res_584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_boxed_583_, v_keys_579_, v_vals_580_, v_i_581_, v_entries_582_);
lean_dec_ref(v_vals_580_);
lean_dec_ref(v_keys_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
size_t v_x_1682__boxed_590_; size_t v_x_1683__boxed_591_; lean_object* v_res_592_; 
v_x_1682__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_x_1683__boxed_591_ = lean_unbox_usize(v_x_587_);
lean_dec(v_x_587_);
v_res_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_585_, v_x_1682__boxed_590_, v_x_1683__boxed_591_, v_x_588_, v_x_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint64_t v___y_597_; 
if (lean_obj_tag(v_x_594_) == 0)
{
uint64_t v___x_601_; 
v___x_601_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_597_ = v___x_601_;
goto v___jp_596_;
}
else
{
uint64_t v_hash_602_; 
v_hash_602_ = lean_ctor_get_uint64(v_x_594_, sizeof(void*)*2);
v___y_597_ = v_hash_602_;
goto v___jp_596_;
}
v___jp_596_:
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_uint64_to_usize(v___y_597_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_593_, v___x_598_, v___x_599_, v_x_594_, v_x_595_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_603_, lean_object* v_x_604_, lean_object* v_e_605_){
_start:
{
lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v_snd_606_ = lean_ctor_get(v_x_604_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_x_604_, 0);
lean_dec(v_unused_616_);
v___x_608_ = v_x_604_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_dec(v_x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_structName_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_structName_610_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_structName_610_);
v___x_611_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_606_, v_structName_610_, v_e_605_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_611_);
lean_ctor_set(v___x_608_, 0, v___x_603_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_623_, lean_object* v_x_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_623_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_628_, v_x_629_, v___y_630_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_x_629_);
return v_res_632_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_665_; lean_object* v___f_666_; 
v___x_665_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_666_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_666_, 0, v___x_665_);
return v___f_666_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_667_; lean_object* v___f_668_; 
v___x_667_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_668_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_668_, 0, v___x_667_);
return v___f_668_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_box(2);
v___f_671_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_672_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_673_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_674_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_675_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_676_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_677_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___f_675_);
lean_ctor_set(v___x_677_, 2, v___f_674_);
lean_ctor_set(v___x_677_, 3, v___f_673_);
lean_ctor_set(v___x_677_, 4, v___f_672_);
lean_ctor_set(v___x_677_, 5, v___f_671_);
lean_ctor_set(v___x_677_, 6, v___x_670_);
lean_ctor_set(v___x_677_, 7, v___x_669_);
return v___x_677_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___f_678_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_679_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___f_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_683_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_686_, lean_object* v_m_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_689_, lean_object* v_m_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_689_, v_m_690_);
lean_dec_ref(v_m_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_692_, lean_object* v_as_693_, lean_object* v_lo_694_, lean_object* v_hi_695_, lean_object* v_w_696_, lean_object* v_hlo_697_, lean_object* v_hhi_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_as_693_, v_lo_694_, v_hi_695_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_700_, lean_object* v_as_701_, lean_object* v_lo_702_, lean_object* v_hi_703_, lean_object* v_w_704_, lean_object* v_hlo_705_, lean_object* v_hhi_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_700_, v_as_701_, v_lo_702_, v_hi_703_, v_w_704_, v_hlo_705_, v_hhi_706_);
lean_dec(v_hi_703_);
lean_dec(v_n_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_709_, v_x_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_713_, lean_object* v_00_u03b2_714_, lean_object* v_map_715_, lean_object* v_f_716_, lean_object* v_init_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_715_, v_f_716_, v_init_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_719_, lean_object* v_00_u03b2_720_, lean_object* v_map_721_, lean_object* v_f_722_, lean_object* v_init_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_719_, v_00_u03b2_720_, v_map_721_, v_f_722_, v_init_723_);
lean_dec_ref(v_map_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, size_t v_x_727_, size_t v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_726_, v_x_727_, v_x_728_, v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
size_t v_x_2083__boxed_738_; size_t v_x_2084__boxed_739_; lean_object* v_res_740_; 
v_x_2083__boxed_738_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_x_2084__boxed_739_ = lean_unbox_usize(v_x_735_);
lean_dec(v_x_735_);
v_res_740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_732_, v_x_733_, v_x_2083__boxed_738_, v_x_2084__boxed_739_, v_x_736_, v_x_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_741_, lean_object* v_f_742_, lean_object* v_init_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_742_, v_map_741_, v_init_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_745_, lean_object* v_f_746_, lean_object* v_init_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_745_, v_f_746_, v_init_747_);
lean_dec_ref(v_map_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_749_, lean_object* v_00_u03b2_750_, lean_object* v_map_751_, lean_object* v_f_752_, lean_object* v_init_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_752_, v_map_751_, v_init_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_755_, lean_object* v_00_u03b2_756_, lean_object* v_map_757_, lean_object* v_f_758_, lean_object* v_init_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_755_, v_00_u03b2_756_, v_map_757_, v_f_758_, v_init_759_);
lean_dec_ref(v_map_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object* v_00_u03b2_761_, lean_object* v_n_762_, lean_object* v_k_763_, lean_object* v_v_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v_n_762_, v_k_763_, v_v_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(lean_object* v_00_u03b2_766_, size_t v_depth_767_, lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_heq_770_, lean_object* v_i_771_, lean_object* v_entries_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_767_, v_keys_768_, v_vals_769_, v_i_771_, v_entries_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_774_, lean_object* v_depth_775_, lean_object* v_keys_776_, lean_object* v_vals_777_, lean_object* v_heq_778_, lean_object* v_i_779_, lean_object* v_entries_780_){
_start:
{
size_t v_depth_boxed_781_; lean_object* v_res_782_; 
v_depth_boxed_781_ = lean_unbox_usize(v_depth_775_);
lean_dec(v_depth_775_);
v_res_782_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(v_00_u03b2_774_, v_depth_boxed_781_, v_keys_776_, v_vals_777_, v_heq_778_, v_i_779_, v_entries_780_);
lean_dec_ref(v_vals_777_);
lean_dec_ref(v_keys_776_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_783_, lean_object* v_00_u03b1_784_, lean_object* v_00_u03b2_785_, lean_object* v_f_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_786_, v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_790_, lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_f_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_790_, v_00_u03b1_791_, v_00_u03b2_792_, v_f_793_, v_x_794_, v_x_795_);
lean_dec_ref(v_x_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_x_798_, v_x_799_, v_x_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_00_u03c3_805_, lean_object* v_f_806_, lean_object* v_as_807_, size_t v_i_808_, size_t v_stop_809_, lean_object* v_b_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_806_, v_as_807_, v_i_808_, v_stop_809_, v_b_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_00_u03c3_814_, lean_object* v_f_815_, lean_object* v_as_816_, lean_object* v_i_817_, lean_object* v_stop_818_, lean_object* v_b_819_){
_start:
{
size_t v_i_boxed_820_; size_t v_stop_boxed_821_; lean_object* v_res_822_; 
v_i_boxed_820_ = lean_unbox_usize(v_i_817_);
lean_dec(v_i_817_);
v_stop_boxed_821_ = lean_unbox_usize(v_stop_818_);
lean_dec(v_stop_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_812_, v_00_u03b2_813_, v_00_u03c3_814_, v_f_815_, v_as_816_, v_i_boxed_820_, v_stop_boxed_821_, v_b_819_);
lean_dec_ref(v_as_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03c3_823_, lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_f_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_acc_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_826_, v_keys_827_, v_vals_828_, v_i_830_, v_acc_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03c3_833_, lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_f_836_, lean_object* v_keys_837_, lean_object* v_vals_838_, lean_object* v_heq_839_, lean_object* v_i_840_, lean_object* v_acc_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03c3_833_, v_00_u03b1_834_, v_00_u03b2_835_, v_f_836_, v_keys_837_, v_vals_838_, v_heq_839_, v_i_840_, v_acc_841_);
lean_dec_ref(v_vals_838_);
lean_dec_ref(v_keys_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_850_, size_t v_i_851_, lean_object* v_bs_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
return v_bs_852_;
}
else
{
lean_object* v_v_854_; lean_object* v_fieldName_855_; lean_object* v___x_856_; lean_object* v_bs_x27_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v_v_854_ = lean_array_uget_borrowed(v_bs_852_, v_i_851_);
v_fieldName_855_ = lean_ctor_get(v_v_854_, 0);
lean_inc(v_fieldName_855_);
v___x_856_ = lean_unsigned_to_nat(0u);
v_bs_x27_857_ = lean_array_uset(v_bs_852_, v_i_851_, v___x_856_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_851_, v___x_858_);
v___x_860_ = lean_array_uset(v_bs_x27_857_, v_i_851_, v_fieldName_855_);
v_i_851_ = v___x_859_;
v_bs_852_ = v___x_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_bs_864_){
_start:
{
size_t v_sz_boxed_865_; size_t v_i_boxed_866_; lean_object* v_res_867_; 
v_sz_boxed_865_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_866_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_865_, v_i_boxed_866_, v_bs_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_as_869_, lean_object* v_lo_870_, lean_object* v_hi_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_nat_dec_lt(v_lo_870_, v_hi_871_);
if (v___x_872_ == 0)
{
lean_dec(v_lo_870_);
return v_as_869_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_fst_875_; lean_object* v_snd_876_; uint8_t v___x_877_; 
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0));
lean_inc(v_lo_870_);
v___x_874_ = l_Array_qpartition___redArg(v_as_869_, v___x_873_, v_lo_870_, v_hi_871_);
v_fst_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_fst_875_);
v_snd_876_ = lean_ctor_get(v___x_874_, 1);
lean_inc(v_snd_876_);
lean_dec_ref(v___x_874_);
v___x_877_ = lean_nat_dec_le(v_hi_871_, v_fst_875_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_snd_876_, v_lo_870_, v_fst_875_);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_fst_875_, v___x_879_);
lean_dec(v_fst_875_);
v_as_869_ = v___x_878_;
v_lo_870_ = v___x_880_;
goto _start;
}
else
{
lean_dec(v_fst_875_);
lean_dec(v_lo_870_);
return v_snd_876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_as_882_, lean_object* v_lo_883_, lean_object* v_hi_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_882_, v_lo_883_, v_hi_884_);
lean_dec(v_hi_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_888_, lean_object* v_e_889_){
_start:
{
lean_object* v_structName_890_; lean_object* v_fields_891_; lean_object* v___x_892_; size_t v_sz_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___y_897_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_structName_890_ = lean_ctor_get(v_e_889_, 0);
lean_inc(v_structName_890_);
v_fields_891_ = lean_ctor_get(v_e_889_, 1);
lean_inc_ref_n(v_fields_891_, 2);
lean_dec_ref(v_e_889_);
v___x_892_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_893_ = lean_array_size(v_fields_891_);
v___x_894_ = ((size_t)0ULL);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_893_, v___x_894_, v_fields_891_);
v___x_908_ = lean_array_get_size(v_fields_891_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___y_914_; uint8_t v___x_916_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_sub(v___x_908_, v___x_911_);
v___x_916_ = lean_nat_dec_le(v___x_909_, v___x_912_);
if (v___x_916_ == 0)
{
lean_inc(v___x_912_);
v___y_914_ = v___x_912_;
goto v___jp_913_;
}
else
{
v___y_914_ = v___x_909_;
goto v___jp_913_;
}
v___jp_913_:
{
uint8_t v___x_915_; 
v___x_915_ = lean_nat_dec_le(v___y_914_, v___x_912_);
if (v___x_915_ == 0)
{
lean_dec(v___x_912_);
lean_inc(v___y_914_);
v___y_905_ = v___y_914_;
v___y_906_ = v___y_914_;
goto v___jp_904_;
}
else
{
v___y_905_ = v___y_914_;
v___y_906_ = v___x_912_;
goto v___jp_904_;
}
}
}
else
{
v___y_897_ = v_fields_891_;
goto v___jp_896_;
}
v___jp_896_:
{
lean_object* v_toEnvExtension_898_; lean_object* v_asyncMode_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_toEnvExtension_898_ = lean_ctor_get(v___x_892_, 0);
v_asyncMode_899_ = lean_ctor_get(v_toEnvExtension_898_, 2);
v___x_900_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_901_, 0, v_structName_890_);
lean_ctor_set(v___x_901_, 1, v___x_895_);
lean_ctor_set(v___x_901_, 2, v___y_897_);
lean_ctor_set(v___x_901_, 3, v___x_900_);
v___x_902_ = lean_box(0);
v___x_903_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_892_, v_env_888_, v___x_901_, v_asyncMode_899_, v___x_902_);
return v___x_903_;
}
v___jp_904_:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_fields_891_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
v___y_897_ = v___x_907_;
goto v___jp_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_917_, lean_object* v_as_918_, lean_object* v_lo_919_, lean_object* v_hi_920_, lean_object* v_w_921_, lean_object* v_hlo_922_, lean_object* v_hhi_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_918_, v_lo_919_, v_hi_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_925_, lean_object* v_as_926_, lean_object* v_lo_927_, lean_object* v_hi_928_, lean_object* v_w_929_, lean_object* v_hlo_930_, lean_object* v_hhi_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_925_, v_as_926_, v_lo_927_, v_hi_928_, v_w_929_, v_hlo_930_, v_hhi_931_);
lean_dec(v_hi_928_);
lean_dec(v_n_925_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_933_, lean_object* v_parentInfo_934_, lean_object* v___x_935_, lean_object* v_asyncMode_936_, lean_object* v___x_937_, lean_object* v_env_938_){
_start:
{
lean_object* v_structName_939_; lean_object* v_fieldNames_940_; lean_object* v_fieldInfo_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_structName_939_ = lean_ctor_get(v_val_933_, 0);
v_fieldNames_940_ = lean_ctor_get(v_val_933_, 1);
v_fieldInfo_941_ = lean_ctor_get(v_val_933_, 2);
v_isSharedCheck_949_ = !lean_is_exclusive(v_val_933_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_val_933_, 3);
lean_dec(v_unused_950_);
v___x_943_ = v_val_933_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_fieldInfo_941_);
lean_inc(v_fieldNames_940_);
lean_inc(v_structName_939_);
lean_dec(v_val_933_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 3, v_parentInfo_934_);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_structName_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_fieldNames_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_fieldInfo_941_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_parentInfo_934_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_935_, v_env_938_, v___x_946_, v_asyncMode_936_, v___x_937_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_951_, lean_object* v_parentInfo_952_, lean_object* v___x_953_, lean_object* v_asyncMode_954_, lean_object* v___x_955_, lean_object* v_env_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_setStructureParents___redArg___lam__0(v_val_951_, v_parentInfo_952_, v___x_953_, v_asyncMode_954_, v___x_955_, v_env_956_);
lean_dec(v_asyncMode_954_);
return v_res_957_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_964_, lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_structName_967_, lean_object* v_parentInfo_968_, lean_object* v_modifyEnv_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_____do__lift_972_){
_start:
{
lean_object* v___x_973_; lean_object* v_toEnvExtension_974_; lean_object* v_asyncMode_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_994_; 
v___x_973_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_974_ = lean_ctor_get(v___x_973_, 0);
v_asyncMode_975_ = lean_ctor_get(v_toEnvExtension_974_, 2);
v___x_976_ = lean_box(0);
v___x_977_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_964_, v___x_973_, v_____do__lift_972_, v_asyncMode_975_, v___x_976_);
v_snd_978_ = lean_ctor_get(v___x_977_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_995_);
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_994_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_994_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; 
lean_inc(v_structName_967_);
v___x_982_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_965_, v___x_966_, v_snd_978_, v_structName_967_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
lean_del_object(v___x_980_);
lean_dec_ref(v_inst_971_);
lean_dec_ref(v_inst_970_);
lean_dec(v_structName_967_);
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v___x_982_);
lean_inc(v_asyncMode_975_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_984_, 0, v_val_983_);
lean_closure_set(v___f_984_, 1, v_parentInfo_968_);
lean_closure_set(v___f_984_, 2, v___x_973_);
lean_closure_set(v___f_984_, 3, v_asyncMode_975_);
lean_closure_set(v___f_984_, 4, v___x_976_);
v___x_985_ = lean_apply_1(v_modifyEnv_969_, v___f_984_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
lean_dec(v___x_982_);
lean_dec(v_modifyEnv_969_);
lean_dec_ref(v_parentInfo_968_);
v___x_986_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_987_ = l_Lean_MessageData_ofName(v_structName_967_);
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 7);
lean_ctor_set(v___x_980_, 1, v___x_987_);
lean_ctor_set(v___x_980_, 0, v___x_986_);
v___x_989_ = v___x_980_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_throwError___redArg(v_inst_970_, v_inst_971_, v___x_991_);
return v___x_992_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = l_Lean_instInhabitedStructureState_default;
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_structName_1004_, lean_object* v_parentInfo_1005_){
_start:
{
lean_object* v_toBind_1006_; lean_object* v_getEnv_1007_; lean_object* v_modifyEnv_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v_toBind_1006_ = lean_ctor_get(v_inst_1001_, 1);
lean_inc(v_toBind_1006_);
v_getEnv_1007_ = lean_ctor_get(v_inst_1002_, 0);
lean_inc(v_getEnv_1007_);
v_modifyEnv_1008_ = lean_ctor_get(v_inst_1002_, 1);
lean_inc(v_modifyEnv_1008_);
lean_dec_ref(v_inst_1002_);
v___x_1009_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1010_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1011_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1012_, 0, v___x_1011_);
lean_closure_set(v___f_1012_, 1, v___x_1009_);
lean_closure_set(v___f_1012_, 2, v___x_1010_);
lean_closure_set(v___f_1012_, 3, v_structName_1004_);
lean_closure_set(v___f_1012_, 4, v_parentInfo_1005_);
lean_closure_set(v___f_1012_, 5, v_modifyEnv_1008_);
lean_closure_set(v___f_1012_, 6, v_inst_1001_);
lean_closure_set(v___f_1012_, 7, v_inst_1003_);
v___x_1013_ = lean_apply_4(v_toBind_1006_, lean_box(0), lean_box(0), v_getEnv_1007_, v___f_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_structName_1018_, lean_object* v_parentInfo_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_setStructureParents___redArg(v_inst_1015_, v_inst_1016_, v_inst_1017_, v_structName_1018_, v_parentInfo_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1021_, lean_object* v_k_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_m_1027_; lean_object* v_a_1028_; uint8_t v___x_1029_; 
v___x_1025_ = lean_nat_add(v_x_1023_, v_x_1024_);
v___x_1026_ = lean_unsigned_to_nat(1u);
v_m_1027_ = lean_nat_shiftr(v___x_1025_, v___x_1026_);
lean_dec(v___x_1025_);
v_a_1028_ = lean_array_fget_borrowed(v_as_1021_, v_m_1027_);
v___x_1029_ = l_Lean_StructureInfo_lt(v_a_1028_, v_k_1022_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
lean_dec(v_x_1024_);
v___x_1030_ = l_Lean_StructureInfo_lt(v_k_1022_, v_a_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v_m_1027_);
lean_dec(v_x_1023_);
lean_inc(v_a_1028_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1028_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_nat_dec_eq(v_m_1027_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_nat_sub(v_m_1027_, v___x_1026_);
lean_dec(v_m_1027_);
v___x_1035_ = lean_nat_dec_lt(v___x_1034_, v_x_1023_);
if (v___x_1035_ == 0)
{
v_x_1024_ = v___x_1034_;
goto _start;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v___x_1034_);
lean_dec(v_x_1023_);
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v_m_1027_);
lean_dec(v_x_1023_);
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
}
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
lean_dec(v_x_1023_);
v___x_1039_ = lean_nat_add(v_m_1027_, v___x_1026_);
lean_dec(v_m_1027_);
v___x_1040_ = lean_nat_dec_le(v___x_1039_, v_x_1024_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v___x_1039_);
lean_dec(v_x_1024_);
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
v_x_1023_ = v___x_1039_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1043_, lean_object* v_k_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1043_, v_k_1044_, v_x_1045_, v_x_1046_);
lean_dec_ref(v_k_1044_);
lean_dec_ref(v_as_1043_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1048_, lean_object* v_vals_1049_, lean_object* v_i_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_array_get_size(v_keys_1048_);
v___x_1053_ = lean_nat_dec_lt(v_i_1050_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v_i_1050_);
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
else
{
lean_object* v_k_x27_1055_; uint8_t v___x_1056_; 
v_k_x27_1055_ = lean_array_fget_borrowed(v_keys_1048_, v_i_1050_);
v___x_1056_ = lean_name_eq(v_k_1051_, v_k_x27_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1050_, v___x_1057_);
lean_dec(v_i_1050_);
v_i_1050_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_array_fget_borrowed(v_vals_1049_, v_i_1050_);
lean_dec(v_i_1050_);
lean_inc(v___x_1060_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_i_1064_, lean_object* v_k_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1064_, v_k_1065_);
lean_dec(v_k_1065_);
lean_dec_ref(v_vals_1063_);
lean_dec_ref(v_keys_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_es_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1091_; 
v_es_1070_ = lean_ctor_get(v_x_1067_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1072_ = v_x_1067_;
v_isShared_1073_ = v_isSharedCheck_1091_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_es_1070_);
lean_dec(v_x_1067_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1091_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; lean_object* v_j_1078_; lean_object* v___x_1079_; 
v___x_1074_ = lean_box(2);
v___x_1075_ = ((size_t)5ULL);
v___x_1076_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1077_ = lean_usize_land(v_x_1068_, v___x_1076_);
v_j_1078_ = lean_usize_to_nat(v___x_1077_);
v___x_1079_ = lean_array_get(v___x_1074_, v_es_1070_, v_j_1078_);
lean_dec(v_j_1078_);
lean_dec_ref(v_es_1070_);
switch(lean_obj_tag(v___x_1079_))
{
case 0:
{
lean_object* v_key_1080_; lean_object* v_val_1081_; uint8_t v___x_1082_; 
v_key_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_key_1080_);
v_val_1081_ = lean_ctor_get(v___x_1079_, 1);
lean_inc(v_val_1081_);
lean_dec_ref(v___x_1079_);
v___x_1082_ = lean_name_eq(v_x_1069_, v_key_1080_);
lean_dec(v_key_1080_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_val_1081_);
lean_del_object(v___x_1072_);
v___x_1083_ = lean_box(0);
return v___x_1083_;
}
else
{
lean_object* v___x_1085_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 0, v_val_1081_);
v___x_1085_ = v___x_1072_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_val_1081_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
case 1:
{
lean_object* v_node_1087_; size_t v___x_1088_; 
lean_del_object(v___x_1072_);
v_node_1087_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_node_1087_);
lean_dec_ref(v___x_1079_);
v___x_1088_ = lean_usize_shift_right(v_x_1068_, v___x_1075_);
v_x_1067_ = v_node_1087_;
v_x_1068_ = v___x_1088_;
goto _start;
}
default: 
{
lean_object* v___x_1090_; 
lean_del_object(v___x_1072_);
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_ks_1092_; lean_object* v_vs_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_ks_1092_ = lean_ctor_get(v_x_1067_, 0);
lean_inc_ref(v_ks_1092_);
v_vs_1093_ = lean_ctor_get(v_x_1067_, 1);
lean_inc_ref(v_vs_1093_);
lean_dec_ref(v_x_1067_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1092_, v_vs_1093_, v___x_1094_, v_x_1069_);
lean_dec_ref(v_vs_1093_);
lean_dec_ref(v_ks_1092_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_395__boxed_1099_; lean_object* v_res_1100_; 
v_x_395__boxed_1099_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1100_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1096_, v_x_395__boxed_1099_, v_x_1098_);
lean_dec(v_x_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
uint64_t v___y_1104_; 
if (lean_obj_tag(v_x_1102_) == 0)
{
uint64_t v___x_1107_; 
v___x_1107_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_1104_ = v___x_1107_;
goto v___jp_1103_;
}
else
{
uint64_t v_hash_1108_; 
v_hash_1108_ = lean_ctor_get_uint64(v_x_1102_, sizeof(void*)*2);
v___y_1104_ = v_hash_1108_;
goto v___jp_1103_;
}
v___jp_1103_:
{
size_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_uint64_to_usize(v___y_1104_);
v___x_1106_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1101_, v___x_1105_, v_x_1102_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1109_, v_x_1110_);
lean_dec(v_x_1110_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1112_, lean_object* v_structName_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1115_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1112_, v_structName_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v_toEnvExtension_1117_; lean_object* v_asyncMode_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_snd_1121_; lean_object* v___x_1122_; 
v___x_1116_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1117_ = lean_ctor_get(v___x_1116_, 0);
v_asyncMode_1118_ = lean_ctor_get(v_toEnvExtension_1117_, 2);
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1114_, v___x_1116_, v_env_1112_, v_asyncMode_1118_, v___x_1119_);
v_snd_1121_ = lean_ctor_get(v___x_1120_, 1);
lean_inc(v_snd_1121_);
lean_dec(v___x_1120_);
v___x_1122_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1121_, v_structName_1113_);
lean_dec(v_structName_1113_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_val_1123_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1115_);
v___x_1124_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1125_ = 0;
v___x_1126_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1114_, v___x_1124_, v_env_1112_, v_val_1123_, v___x_1125_);
lean_dec(v_val_1123_);
lean_dec_ref(v_env_1112_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v___x_1126_);
v___x_1129_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v___x_1126_);
lean_dec(v_structName_1113_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_sub(v___x_1128_, v___x_1131_);
v___x_1133_ = lean_nat_dec_le(v___x_1127_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1126_);
lean_dec(v_structName_1113_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1136_, 0, v_structName_1113_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1135_);
lean_ctor_set(v___x_1136_, 3, v___x_1135_);
v___x_1137_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1126_, v___x_1136_, v___x_1127_, v___x_1132_);
lean_dec_ref(v___x_1136_);
lean_dec_ref(v___x_1126_);
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1142_, v_x_1143_, v_x_1144_);
lean_dec(v_x_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1146_, lean_object* v_k_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1146_, v_k_1147_, v_x_1148_, v_x_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1152_, lean_object* v_k_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1152_, v_k_1153_, v_x_1154_, v_x_1155_, v_x_1156_);
lean_dec_ref(v_k_1153_);
lean_dec_ref(v_as_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1158_, lean_object* v_x_1159_, size_t v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1159_, v_x_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
size_t v_x_543__boxed_1167_; lean_object* v_res_1168_; 
v_x_543__boxed_1167_ = lean_unbox_usize(v_x_1165_);
lean_dec(v_x_1165_);
v_res_1168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1163_, v_x_1164_, v_x_543__boxed_1167_, v_x_1166_);
lean_dec(v_x_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1169_, lean_object* v_keys_1170_, lean_object* v_vals_1171_, lean_object* v_heq_1172_, lean_object* v_i_1173_, lean_object* v_k_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1170_, v_vals_1171_, v_i_1173_, v_k_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1176_, lean_object* v_keys_1177_, lean_object* v_vals_1178_, lean_object* v_heq_1179_, lean_object* v_i_1180_, lean_object* v_k_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1176_, v_keys_1177_, v_vals_1178_, v_heq_1179_, v_i_1180_, v_k_1181_);
lean_dec(v_k_1181_);
lean_dec_ref(v_vals_1178_);
lean_dec_ref(v_keys_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1185_ = lean_panic_fn_borrowed(v___x_1184_, v_msg_1183_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1189_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1190_ = lean_unsigned_to_nat(4u);
v___x_1191_ = lean_unsigned_to_nat(139u);
v___x_1192_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1193_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1194_ = l_mkPanicMessageWithDecl(v___x_1193_, v___x_1192_, v___x_1191_, v___x_1190_, v___x_1189_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1195_, lean_object* v_structName_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_getStructureInfo_x3f(v_env_1195_, v_structName_1196_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v___x_1197_);
return v_val_1198_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v___x_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1200_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1199_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1203_ = lean_panic_fn_borrowed(v___x_1202_, v_msg_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1206_ = lean_unsigned_to_nat(9u);
v___x_1207_ = lean_unsigned_to_nat(154u);
v___x_1208_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1209_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1210_ = l_mkPanicMessageWithDecl(v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_, v___x_1205_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1213_ = lean_unsigned_to_nat(11u);
v___x_1214_ = lean_unsigned_to_nat(153u);
v___x_1215_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1216_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1217_ = l_mkPanicMessageWithDecl(v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1218_, lean_object* v_constName_1219_){
_start:
{
uint8_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = 0;
lean_inc_ref(v_env_1218_);
v___x_1227_ = l_Lean_Environment_find_x3f(v_env_1218_, v_constName_1219_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 1)
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref(v___x_1227_);
if (lean_obj_tag(v_val_1228_) == 5)
{
lean_object* v_val_1229_; lean_object* v_ctors_1230_; 
v_val_1229_ = lean_ctor_get(v_val_1228_, 0);
lean_inc_ref(v_val_1229_);
lean_dec_ref(v_val_1228_);
v_ctors_1230_ = lean_ctor_get(v_val_1229_, 4);
lean_inc(v_ctors_1230_);
lean_dec_ref(v_val_1229_);
if (lean_obj_tag(v_ctors_1230_) == 1)
{
lean_object* v_tail_1231_; 
v_tail_1231_ = lean_ctor_get(v_ctors_1230_, 1);
if (lean_obj_tag(v_tail_1231_) == 0)
{
lean_object* v_head_1232_; lean_object* v___x_1233_; 
v_head_1232_ = lean_ctor_get(v_ctors_1230_, 0);
lean_inc(v_head_1232_);
lean_dec_ref(v_ctors_1230_);
v___x_1233_ = l_Lean_Environment_find_x3f(v_env_1218_, v_head_1232_, v___x_1226_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; 
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref(v___x_1233_);
if (lean_obj_tag(v_val_1234_) == 6)
{
lean_object* v_val_1235_; 
v_val_1235_ = lean_ctor_get(v_val_1234_, 0);
lean_inc_ref(v_val_1235_);
lean_dec_ref(v_val_1234_);
return v_val_1235_;
}
else
{
lean_dec(v_val_1234_);
goto v___jp_1223_;
}
}
else
{
lean_dec(v___x_1233_);
goto v___jp_1223_;
}
}
else
{
lean_dec_ref(v_ctors_1230_);
lean_dec_ref(v_env_1218_);
goto v___jp_1220_;
}
}
else
{
lean_dec(v_ctors_1230_);
lean_dec_ref(v_env_1218_);
goto v___jp_1220_;
}
}
else
{
lean_dec(v_val_1228_);
lean_dec_ref(v_env_1218_);
goto v___jp_1220_;
}
}
else
{
lean_dec(v___x_1227_);
lean_dec_ref(v_env_1218_);
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1222_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1221_);
return v___x_1222_;
}
v___jp_1223_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1225_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1236_, lean_object* v_structName_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v_fieldNames_1239_; 
v___x_1238_ = l_Lean_getStructureInfo(v_env_1236_, v_structName_1237_);
v_fieldNames_1239_ = lean_ctor_get(v___x_1238_, 1);
lean_inc_ref(v_fieldNames_1239_);
lean_dec_ref(v___x_1238_);
return v_fieldNames_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1240_, lean_object* v_structName_1241_, lean_object* v_fieldName_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_getStructureInfo_x3f(v_env_1240_, v_structName_1241_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v_fieldInfo_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v___x_1243_);
v_fieldInfo_1245_ = lean_ctor_get(v_val_1244_, 2);
lean_inc_ref(v_fieldInfo_1245_);
lean_dec(v_val_1244_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_array_get_size(v_fieldInfo_1245_);
v___x_1248_ = lean_nat_dec_lt(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v_fieldInfo_1245_);
lean_dec(v_fieldName_1242_);
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_sub(v___x_1247_, v___x_1250_);
v___x_1252_ = lean_nat_dec_le(v___x_1246_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___x_1251_);
lean_dec_ref(v_fieldInfo_1245_);
lean_dec(v_fieldName_1242_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_box(0);
v___x_1256_ = 0;
v___x_1257_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1257_, 0, v_fieldName_1242_);
lean_ctor_set(v___x_1257_, 1, v___x_1254_);
lean_ctor_set(v___x_1257_, 2, v___x_1255_);
lean_ctor_set(v___x_1257_, 3, v___x_1255_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*4, v___x_1256_);
v___x_1258_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1245_, v___x_1257_, v___x_1246_, v___x_1251_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v_fieldInfo_1245_);
return v___x_1258_;
}
}
}
else
{
lean_object* v___x_1259_; 
lean_dec(v___x_1243_);
lean_dec(v_fieldName_1242_);
v___x_1259_ = lean_box(0);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1260_, lean_object* v_structName_1261_, lean_object* v_fieldName_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_getFieldInfo_x3f(v_env_1260_, v_structName_1261_, v_fieldName_1262_);
if (lean_obj_tag(v___x_1263_) == 1)
{
lean_object* v_val_1264_; lean_object* v_subobject_x3f_1265_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref(v___x_1263_);
v_subobject_x3f_1265_ = lean_ctor_get(v_val_1264_, 2);
lean_inc(v_subobject_x3f_1265_);
lean_dec(v_val_1264_);
return v_subobject_x3f_1265_;
}
else
{
lean_object* v___x_1266_; 
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1267_, lean_object* v_structName_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v_parentInfo_1270_; 
v___x_1269_ = l_Lean_getStructureInfo(v_env_1267_, v_structName_1268_);
v_parentInfo_1270_ = lean_ctor_get(v___x_1269_, 3);
lean_inc_ref(v_parentInfo_1270_);
lean_dec_ref(v___x_1269_);
return v_parentInfo_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1271_, lean_object* v_structName_1272_, lean_object* v_as_1273_, size_t v_i_1274_, size_t v_stop_1275_, lean_object* v_b_1276_){
_start:
{
lean_object* v___y_1278_; uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_eq(v_i_1274_, v_stop_1275_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_array_uget_borrowed(v_as_1273_, v_i_1274_);
lean_inc(v___x_1283_);
lean_inc(v_structName_1272_);
lean_inc_ref(v_env_1271_);
v___x_1284_ = l_Lean_isSubobjectField_x3f(v_env_1271_, v_structName_1272_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
v___y_1278_ = v_b_1276_;
goto v___jp_1277_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = lean_array_push(v_b_1276_, v_val_1285_);
v___y_1278_ = v___x_1286_;
goto v___jp_1277_;
}
}
else
{
lean_dec(v_structName_1272_);
lean_dec_ref(v_env_1271_);
return v_b_1276_;
}
v___jp_1277_:
{
size_t v___x_1279_; size_t v___x_1280_; 
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_add(v_i_1274_, v___x_1279_);
v_i_1274_ = v___x_1280_;
v_b_1276_ = v___y_1278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1287_, lean_object* v_structName_1288_, lean_object* v_as_1289_, lean_object* v_i_1290_, lean_object* v_stop_1291_, lean_object* v_b_1292_){
_start:
{
size_t v_i_boxed_1293_; size_t v_stop_boxed_1294_; lean_object* v_res_1295_; 
v_i_boxed_1293_ = lean_unbox_usize(v_i_1290_);
lean_dec(v_i_1290_);
v_stop_boxed_1294_ = lean_unbox_usize(v_stop_1291_);
lean_dec(v_stop_1291_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1287_, v_structName_1288_, v_as_1289_, v_i_boxed_1293_, v_stop_boxed_1294_, v_b_1292_);
lean_dec_ref(v_as_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1296_, lean_object* v_structName_1297_, lean_object* v_as_1298_, lean_object* v_start_1299_, lean_object* v_stop_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1302_ = lean_nat_dec_lt(v_start_1299_, v_stop_1300_);
if (v___x_1302_ == 0)
{
lean_dec(v_structName_1297_);
lean_dec_ref(v_env_1296_);
return v___x_1301_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_as_1298_);
v___x_1304_ = lean_nat_dec_le(v_stop_1300_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_nat_dec_lt(v_start_1299_, v___x_1303_);
if (v___x_1305_ == 0)
{
lean_dec(v_structName_1297_);
lean_dec_ref(v_env_1296_);
return v___x_1301_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_usize_of_nat(v_start_1299_);
v___x_1307_ = lean_usize_of_nat(v___x_1303_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1296_, v_structName_1297_, v_as_1298_, v___x_1306_, v___x_1307_, v___x_1301_);
return v___x_1308_;
}
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_usize_of_nat(v_start_1299_);
v___x_1310_ = lean_usize_of_nat(v_stop_1300_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1296_, v_structName_1297_, v_as_1298_, v___x_1309_, v___x_1310_, v___x_1301_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1312_, lean_object* v_structName_1313_, lean_object* v_as_1314_, lean_object* v_start_1315_, lean_object* v_stop_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1312_, v_structName_1313_, v_as_1314_, v_start_1315_, v_stop_1316_);
lean_dec(v_stop_1316_);
lean_dec(v_start_1315_);
lean_dec_ref(v_as_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1318_, lean_object* v_structName_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_inc(v_structName_1319_);
lean_inc_ref(v_env_1318_);
v___x_1320_ = l_Lean_getStructureFields(v_env_1318_, v_structName_1319_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v___x_1320_);
v___x_1323_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1318_, v_structName_1319_, v___x_1320_, v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1324_, lean_object* v_as_1325_, size_t v_i_1326_, size_t v_stop_1327_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_eq(v_i_1326_, v_stop_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_array_uget_borrowed(v_as_1325_, v_i_1326_);
v___x_1330_ = lean_name_eq(v_a_1324_, v___x_1329_);
if (v___x_1330_ == 0)
{
size_t v___x_1331_; size_t v___x_1332_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1326_, v___x_1331_);
v_i_1326_ = v___x_1332_;
goto _start;
}
else
{
return v___x_1330_;
}
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1335_, lean_object* v_as_1336_, lean_object* v_i_1337_, lean_object* v_stop_1338_){
_start:
{
size_t v_i_boxed_1339_; size_t v_stop_boxed_1340_; uint8_t v_res_1341_; lean_object* v_r_1342_; 
v_i_boxed_1339_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_stop_boxed_1340_ = lean_unbox_usize(v_stop_1338_);
lean_dec(v_stop_1338_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1335_, v_as_1336_, v_i_boxed_1339_, v_stop_boxed_1340_);
lean_dec_ref(v_as_1336_);
lean_dec(v_a_1335_);
v_r_1342_ = lean_box(v_res_1341_);
return v_r_1342_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_as_1343_);
v___x_1347_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
if (v___x_1347_ == 0)
{
return v___x_1347_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1346_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1344_, v_as_1343_, v___x_1348_, v___x_1349_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1351_, lean_object* v_a_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_as_1351_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1358_, lean_object* v_structName_1359_, lean_object* v_fieldName_1360_){
_start:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
lean_inc(v_structName_1359_);
lean_inc_ref(v_env_1358_);
v___x_1361_ = l_Lean_getStructureFields(v_env_1358_, v_structName_1359_);
v___x_1362_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1361_, v_fieldName_1360_);
lean_dec_ref(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; lean_object* v_fst_1369_; 
lean_inc_ref(v_env_1358_);
v___x_1363_ = l_Lean_getStructureSubobjects(v_env_1358_, v_structName_1359_);
v___x_1364_ = lean_box(0);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1366_ = lean_array_size(v___x_1363_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1358_, v_fieldName_1360_, v___x_1363_, v_sz_1366_, v___x_1367_, v___x_1365_);
lean_dec_ref(v___x_1363_);
v_fst_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_fst_1369_);
lean_dec_ref(v___x_1368_);
if (lean_obj_tag(v_fst_1369_) == 0)
{
return v___x_1364_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v_fst_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref(v_fst_1369_);
return v_val_1370_;
}
}
else
{
lean_object* v___x_1371_; 
lean_dec_ref(v_env_1358_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_structName_1359_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1372_, lean_object* v_fieldName_1373_, lean_object* v_as_1374_, size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_b_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1376_, v_sz_1375_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v_env_1372_);
lean_inc_ref(v_b_1377_);
return v_b_1377_;
}
else
{
lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1381_; 
v___x_1379_ = lean_box(0);
v_a_1380_ = lean_array_uget_borrowed(v_as_1374_, v_i_1376_);
lean_inc(v_a_1380_);
lean_inc_ref(v_env_1372_);
v___x_1381_ = l_Lean_findField_x3f(v_env_1372_, v_a_1380_, v_fieldName_1373_);
if (lean_obj_tag(v___x_1381_) == 1)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v_env_1372_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1379_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; 
lean_dec(v___x_1381_);
v___x_1384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1376_, v___x_1385_);
v_i_1376_ = v___x_1386_;
v_b_1377_ = v___x_1384_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1388_, lean_object* v_fieldName_1389_, lean_object* v_as_1390_, lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_b_1393_){
_start:
{
size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1388_, v_fieldName_1389_, v_as_1390_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1393_);
lean_dec_ref(v_b_1393_);
lean_dec_ref(v_as_1390_);
lean_dec(v_fieldName_1389_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1397_, lean_object* v_structName_1398_, lean_object* v_fieldName_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_findField_x3f(v_env_1397_, v_structName_1398_, v_fieldName_1399_);
lean_dec(v_fieldName_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1404_, lean_object* v_as_1405_, size_t v_sz_1406_, size_t v_i_1407_, lean_object* v_b_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_lt(v_i_1407_, v_sz_1406_);
if (v___x_1409_ == 0)
{
lean_inc_ref(v_b_1408_);
return v_b_1408_;
}
else
{
lean_object* v_a_1410_; lean_object* v_projFn_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_a_1410_ = lean_array_uget_borrowed(v_as_1405_, v_i_1407_);
v_projFn_1411_ = lean_ctor_get(v_a_1410_, 1);
v___x_1412_ = lean_box(0);
v___x_1413_ = l_Lean_Name_isSuffixOf(v_projName_1404_, v_projFn_1411_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; 
v___x_1414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1407_, v___x_1415_);
v_i_1407_ = v___x_1416_;
v_b_1408_ = v___x_1414_;
goto _start;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc(v_a_1410_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1410_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1412_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1421_, lean_object* v_as_1422_, lean_object* v_sz_1423_, lean_object* v_i_1424_, lean_object* v_b_1425_){
_start:
{
size_t v_sz_boxed_1426_; size_t v_i_boxed_1427_; lean_object* v_res_1428_; 
v_sz_boxed_1426_ = lean_unbox_usize(v_sz_1423_);
lean_dec(v_sz_1423_);
v_i_boxed_1427_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_res_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1421_, v_as_1422_, v_sz_boxed_1426_, v_i_boxed_1427_, v_b_1425_);
lean_dec_ref(v_b_1425_);
lean_dec_ref(v_as_1422_);
lean_dec(v_projName_1421_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1429_, lean_object* v_projName_1430_, lean_object* v_structName_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = l_Lean_NameSet_contains(v_a_1432_, v_structName_1431_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1458_; size_t v_sz_1459_; size_t v___x_1460_; lean_object* v___x_1461_; lean_object* v_fst_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1479_; 
lean_inc(v_structName_1431_);
lean_inc_ref(v_env_1429_);
v___x_1434_ = l_Lean_getStructureParentInfo(v_env_1429_, v_structName_1431_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1459_ = lean_array_size(v___x_1434_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1430_, v___x_1434_, v_sz_1459_, v___x_1460_, v___x_1458_);
v_fst_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v___x_1461_, 1);
lean_dec(v_unused_1480_);
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1479_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_fst_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1479_;
goto v_resetjp_1463_;
}
v___jp_1435_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; size_t v_sz_1439_; size_t v___x_1440_; lean_object* v___x_1441_; lean_object* v_fst_1442_; lean_object* v_fst_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1456_; 
v___x_1436_ = l_Lean_NameSet_insert(v_a_1432_, v_structName_1431_);
v___x_1437_ = lean_box(0);
v___x_1438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1439_ = lean_array_size(v___x_1434_);
v___x_1440_ = ((size_t)0ULL);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1429_, v_projName_1430_, v___x_1434_, v_sz_1439_, v___x_1440_, v___x_1438_, v___x_1436_);
lean_dec_ref(v___x_1434_);
v_fst_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_fst_1442_);
v_fst_1443_ = lean_ctor_get(v_fst_1442_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_fst_1442_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_fst_1442_, 1);
lean_dec(v_unused_1457_);
v___x_1445_ = v_fst_1442_;
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_fst_1443_);
lean_dec(v_fst_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
if (lean_obj_tag(v_fst_1443_) == 0)
{
lean_object* v_snd_1447_; lean_object* v___x_1449_; 
v_snd_1447_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_snd_1447_);
lean_dec_ref(v___x_1441_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v_snd_1447_);
lean_ctor_set(v___x_1445_, 0, v___x_1437_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_snd_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_snd_1451_; lean_object* v_val_1452_; lean_object* v___x_1454_; 
v_snd_1451_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_snd_1451_);
lean_dec_ref(v___x_1441_);
v_val_1452_ = lean_ctor_get(v_fst_1443_, 0);
lean_inc(v_val_1452_);
lean_dec_ref(v_fst_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v_snd_1451_);
lean_ctor_set(v___x_1445_, 0, v_val_1452_);
v___x_1454_ = v___x_1445_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1452_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_snd_1451_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
v_resetjp_1463_:
{
if (lean_obj_tag(v_fst_1462_) == 0)
{
lean_del_object(v___x_1464_);
goto v___jp_1435_;
}
else
{
lean_object* v_val_1466_; 
v_val_1466_ = lean_ctor_get(v_fst_1462_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v_fst_1462_);
if (lean_obj_tag(v_val_1466_) == 1)
{
lean_object* v_val_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___x_1434_);
lean_dec(v_structName_1431_);
lean_dec_ref(v_env_1429_);
v_val_1467_ = lean_ctor_get(v_val_1466_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_val_1466_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1469_ = v_val_1466_;
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_val_1467_);
lean_dec(v_val_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_structName_1471_; lean_object* v___x_1473_; 
v_structName_1471_ = lean_ctor_get(v_val_1467_, 0);
lean_inc(v_structName_1471_);
lean_dec(v_val_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_structName_1471_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_structName_1471_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v_a_1432_);
lean_ctor_set(v___x_1464_, 0, v___x_1473_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1432_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_dec(v_val_1466_);
lean_del_object(v___x_1464_);
goto v___jp_1435_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v_structName_1431_);
lean_dec_ref(v_env_1429_);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_a_1432_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1483_, lean_object* v_projName_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v_env_1483_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1488_);
lean_ctor_set(v___x_1491_, 1, v___y_1489_);
return v___x_1491_;
}
else
{
lean_object* v_a_1492_; lean_object* v_structName_1493_; lean_object* v___x_1494_; lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v_b_1488_);
v_a_1492_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
v_structName_1493_ = lean_ctor_get(v_a_1492_, 0);
lean_inc(v_structName_1493_);
lean_inc_ref(v_env_1483_);
v___x_1494_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1483_, v_projName_1484_, v_structName_1493_, v___y_1489_);
v_fst_1495_ = lean_ctor_get(v___x_1494_, 0);
v_snd_1496_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_inc(v_fst_1495_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_box(0);
if (lean_obj_tag(v_fst_1495_) == 1)
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec_ref(v_env_1483_);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_fst_1495_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1500_);
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1500_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_snd_1496_);
return v___x_1504_;
}
}
else
{
lean_object* v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; 
lean_del_object(v___x_1498_);
lean_dec(v_fst_1495_);
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1487_, v___x_1507_);
v_i_1487_ = v___x_1508_;
v_b_1488_ = v___x_1506_;
v___y_1489_ = v_snd_1496_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1511_, lean_object* v_projName_1512_, lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_sz_boxed_1518_; size_t v_i_boxed_1519_; lean_object* v_res_1520_; 
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1519_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1511_, v_projName_1512_, v_as_1513_, v_sz_boxed_1518_, v_i_boxed_1519_, v_b_1516_, v___y_1517_);
lean_dec_ref(v_as_1513_);
lean_dec(v_projName_1512_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1521_, lean_object* v_projName_1522_, lean_object* v_structName_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1521_, v_projName_1522_, v_structName_1523_, v_a_1524_);
lean_dec(v_projName_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1526_, lean_object* v_structName_1527_, lean_object* v_projName_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_fst_1531_; 
v___x_1529_ = l_Lean_NameSet_empty;
v___x_1530_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1526_, v_projName_1528_, v_structName_1527_, v___x_1529_);
v_fst_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_fst_1531_);
lean_dec_ref(v___x_1530_);
return v_fst_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1532_, lean_object* v_structName_1533_, lean_object* v_projName_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_findParentProjStruct_x3f(v_env_1532_, v_structName_1533_, v_projName_1534_);
lean_dec(v_projName_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1541_ = l_Lean_Name_append(v_structCtorName_1539_, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1542_, lean_object* v_structName_1543_, uint8_t v_includeSubobjectFields_1544_, lean_object* v_as_1545_, size_t v_i_1546_, size_t v_stop_1547_, lean_object* v_b_1548_){
_start:
{
lean_object* v___y_1550_; uint8_t v___x_1554_; 
v___x_1554_ = lean_usize_dec_eq(v_i_1546_, v_stop_1547_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_array_uget_borrowed(v_as_1545_, v_i_1546_);
lean_inc(v___x_1555_);
lean_inc(v_structName_1543_);
lean_inc_ref(v_env_1542_);
v___x_1556_ = l_Lean_isSubobjectField_x3f(v_env_1542_, v_structName_1543_, v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
lean_inc(v___x_1555_);
v___x_1557_ = lean_array_push(v_b_1548_, v___x_1555_);
v___y_1550_ = v___x_1557_;
goto v___jp_1549_;
}
else
{
if (v_includeSubobjectFields_1544_ == 0)
{
lean_object* v_val_1558_; lean_object* v___x_1559_; 
v_val_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1558_);
lean_dec_ref(v___x_1556_);
lean_inc_ref(v_env_1542_);
v___x_1559_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1542_, v_val_1558_, v_b_1548_, v_includeSubobjectFields_1544_);
v___y_1550_ = v___x_1559_;
goto v___jp_1549_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_val_1560_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1560_);
lean_dec_ref(v___x_1556_);
lean_inc(v___x_1555_);
v___x_1561_ = lean_array_push(v_b_1548_, v___x_1555_);
lean_inc_ref(v_env_1542_);
v___x_1562_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1542_, v_val_1560_, v___x_1561_, v_includeSubobjectFields_1544_);
v___y_1550_ = v___x_1562_;
goto v___jp_1549_;
}
}
}
else
{
lean_dec(v_structName_1543_);
lean_dec_ref(v_env_1542_);
return v_b_1548_;
}
v___jp_1549_:
{
size_t v___x_1551_; size_t v___x_1552_; 
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_add(v_i_1546_, v___x_1551_);
v_i_1546_ = v___x_1552_;
v_b_1548_ = v___y_1550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1563_, lean_object* v_structName_1564_, lean_object* v_fullNames_1565_, uint8_t v_includeSubobjectFields_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
lean_inc(v_structName_1564_);
lean_inc_ref(v_env_1563_);
v___x_1567_ = l_Lean_getStructureFields(v_env_1563_, v_structName_1564_);
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = lean_array_get_size(v___x_1567_);
v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v___x_1567_);
lean_dec(v_structName_1564_);
lean_dec_ref(v_env_1563_);
return v_fullNames_1565_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_le(v___x_1569_, v___x_1569_);
if (v___x_1571_ == 0)
{
if (v___x_1570_ == 0)
{
lean_dec_ref(v___x_1567_);
lean_dec(v_structName_1564_);
lean_dec_ref(v_env_1563_);
return v_fullNames_1565_;
}
else
{
size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((size_t)0ULL);
v___x_1573_ = lean_usize_of_nat(v___x_1569_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1563_, v_structName_1564_, v_includeSubobjectFields_1566_, v___x_1567_, v___x_1572_, v___x_1573_, v_fullNames_1565_);
lean_dec_ref(v___x_1567_);
return v___x_1574_;
}
}
else
{
size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = lean_usize_of_nat(v___x_1569_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1563_, v_structName_1564_, v_includeSubobjectFields_1566_, v___x_1567_, v___x_1575_, v___x_1576_, v_fullNames_1565_);
lean_dec_ref(v___x_1567_);
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1578_, lean_object* v_structName_1579_, lean_object* v_fullNames_1580_, lean_object* v_includeSubobjectFields_1581_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1582_; lean_object* v_res_1583_; 
v_includeSubobjectFields_boxed_1582_ = lean_unbox(v_includeSubobjectFields_1581_);
v_res_1583_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1578_, v_structName_1579_, v_fullNames_1580_, v_includeSubobjectFields_boxed_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1584_, lean_object* v_structName_1585_, lean_object* v_includeSubobjectFields_1586_, lean_object* v_as_1587_, lean_object* v_i_1588_, lean_object* v_stop_1589_, lean_object* v_b_1590_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1591_; size_t v_i_boxed_1592_; size_t v_stop_boxed_1593_; lean_object* v_res_1594_; 
v_includeSubobjectFields_boxed_1591_ = lean_unbox(v_includeSubobjectFields_1586_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v_stop_boxed_1593_ = lean_unbox_usize(v_stop_1589_);
lean_dec(v_stop_1589_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1584_, v_structName_1585_, v_includeSubobjectFields_boxed_1591_, v_as_1587_, v_i_boxed_1592_, v_stop_boxed_1593_, v_b_1590_);
lean_dec_ref(v_as_1587_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1595_, lean_object* v_structName_1596_, uint8_t v_includeSubobjectFields_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1599_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1595_, v_structName_1596_, v___x_1598_, v_includeSubobjectFields_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1600_, lean_object* v_structName_1601_, lean_object* v_includeSubobjectFields_1602_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1603_; lean_object* v_res_1604_; 
v_includeSubobjectFields_boxed_1603_ = lean_unbox(v_includeSubobjectFields_1602_);
v_res_1604_ = l_Lean_getStructureFieldsFlattened(v_env_1600_, v_structName_1601_, v_includeSubobjectFields_boxed_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1605_, lean_object* v_constName_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_getStructureInfo_x3f(v_env_1605_, v_constName_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
uint8_t v___x_1608_; 
v___x_1608_ = 0;
return v___x_1608_;
}
else
{
uint8_t v___x_1609_; 
lean_dec_ref(v___x_1607_);
v___x_1609_ = 1;
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1610_, lean_object* v_constName_1611_){
_start:
{
uint8_t v_res_1612_; lean_object* v_r_1613_; 
v_res_1612_ = l_Lean_isStructure(v_env_1610_, v_constName_1611_);
v_r_1613_ = lean_box(v_res_1612_);
return v_r_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1614_, lean_object* v_structName_1615_, lean_object* v_fieldName_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_getFieldInfo_x3f(v_env_1614_, v_structName_1615_, v_fieldName_1616_);
if (lean_obj_tag(v___x_1617_) == 1)
{
lean_object* v_val_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1626_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_val_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_projFn_1622_; lean_object* v___x_1624_; 
v_projFn_1622_ = lean_ctor_get(v_val_1618_, 1);
lean_inc(v_projFn_1622_);
lean_dec(v_val_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_projFn_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_projFn_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_object* v___x_1627_; 
lean_dec(v___x_1617_);
v___x_1627_ = lean_box(0);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1628_, lean_object* v_structName_1629_, lean_object* v_fieldName_1630_){
_start:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_env_1628_);
v___x_1631_ = l_Lean_getProjFnForField_x3f(v_env_1628_, v_structName_1629_, v_fieldName_1630_);
if (lean_obj_tag(v___x_1631_) == 1)
{
lean_object* v_val_1632_; lean_object* v___x_1633_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc_n(v_val_1632_, 2);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1628_, v_val_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec(v_val_1632_);
v___x_1634_ = lean_box(0);
return v___x_1634_;
}
else
{
lean_object* v_val_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
v_val_1635_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_val_1635_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_val_1632_);
lean_ctor_set(v___x_1639_, 1, v_val_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
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
else
{
lean_object* v___x_1644_; 
lean_dec(v___x_1631_);
lean_dec_ref(v_env_1628_);
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1650_ = l_Lean_Name_append(v_projFn_1648_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1656_ = l_Lean_Name_append(v_projFn_1654_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1657_, lean_object* v_env_1658_, lean_object* v_structName_1659_, lean_object* v_fieldName_1660_){
_start:
{
lean_object* v___x_1661_; 
lean_inc(v_fieldName_1660_);
lean_inc(v_structName_1659_);
lean_inc_ref(v_env_1658_);
v___x_1661_ = l_Lean_getProjFnForField_x3f(v_env_1658_, v_structName_1659_, v_fieldName_1660_);
if (lean_obj_tag(v___x_1661_) == 1)
{
lean_object* v_val_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_fieldName_1660_);
lean_dec(v_structName_1659_);
v_val_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_val_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_defFn_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; 
v_defFn_1666_ = lean_apply_1(v_mkName_1657_, v_val_1662_);
v___x_1667_ = 1;
lean_inc(v_defFn_1666_);
v___x_1668_ = l_Lean_Environment_contains(v_env_1658_, v_defFn_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v_defFn_1666_);
lean_del_object(v___x_1664_);
v___x_1669_ = lean_box(0);
return v___x_1669_;
}
else
{
lean_object* v___x_1671_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v_defFn_1666_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_defFn_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v_defFn_1675_; uint8_t v___x_1676_; uint8_t v___x_1677_; 
lean_dec(v___x_1661_);
v___x_1674_ = l_Lean_Name_append(v_structName_1659_, v_fieldName_1660_);
v_defFn_1675_ = lean_apply_1(v_mkName_1657_, v___x_1674_);
v___x_1676_ = 1;
lean_inc(v_defFn_1675_);
v___x_1677_ = l_Lean_Environment_contains(v_env_1658_, v_defFn_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_dec(v_defFn_1675_);
v___x_1678_ = lean_box(0);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_defFn_1675_);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1681_, lean_object* v_structName_1682_, lean_object* v_fieldName_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1685_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1684_, v_env_1681_, v_structName_1682_, v_fieldName_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1687_, lean_object* v_structName_1688_, lean_object* v_fieldName_1689_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v_fieldName_1689_);
lean_inc(v_structName_1688_);
lean_inc_ref(v_env_1687_);
v___x_1690_ = l_Lean_getDefaultFnForField_x3f(v_env_1687_, v_structName_1688_, v_fieldName_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1692_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1691_, v_env_1687_, v_structName_1688_, v_fieldName_1689_);
return v___x_1692_;
}
else
{
lean_dec(v_fieldName_1689_);
lean_dec(v_structName_1688_);
lean_dec_ref(v_env_1687_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1698_ = l_Lean_Name_append(v_projFn_1696_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1700_, lean_object* v_structName_1701_, lean_object* v_fieldName_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1704_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1703_, v_env_1700_, v_structName_1701_, v_fieldName_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(lean_object* v_f_1705_, lean_object* v_as_1706_, lean_object* v_i_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_array_get_size(v_as_1706_);
v___x_1710_ = lean_nat_dec_lt(v_i_1707_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v_i_1707_);
lean_dec_ref(v_f_1705_);
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v___y_1708_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_fst_1715_; 
v___x_1713_ = lean_array_fget_borrowed(v_as_1706_, v_i_1707_);
lean_inc_ref(v_f_1705_);
lean_inc(v___x_1713_);
v___x_1714_ = lean_apply_2(v_f_1705_, v___x_1713_, v___y_1708_);
v_fst_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_fst_1715_);
if (lean_obj_tag(v_fst_1715_) == 0)
{
lean_object* v_snd_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_snd_1716_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_snd_1716_);
lean_dec_ref(v___x_1714_);
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_add(v_i_1707_, v___x_1717_);
lean_dec(v_i_1707_);
v_i_1707_ = v___x_1718_;
v___y_1708_ = v_snd_1716_;
goto _start;
}
else
{
lean_dec_ref(v_fst_1715_);
lean_dec(v_i_1707_);
lean_dec_ref(v_f_1705_);
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg___boxed(lean_object* v_f_1720_, lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1720_, v_as_1721_, v_i_1722_, v___y_1723_);
lean_dec_ref(v_as_1721_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1(lean_object* v_path_1725_, lean_object* v_env_1726_, lean_object* v_baseStructName_1727_, lean_object* v_field_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_subobject_x3f_1730_; 
v_subobject_x3f_1730_ = lean_ctor_get(v_field_1728_, 2);
lean_inc(v_subobject_x3f_1730_);
if (lean_obj_tag(v_subobject_x3f_1730_) == 1)
{
lean_object* v_projFn_1731_; lean_object* v_val_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_projFn_1731_ = lean_ctor_get(v_field_1728_, 1);
lean_inc(v_projFn_1731_);
lean_dec_ref(v_field_1728_);
v_val_1732_ = lean_ctor_get(v_subobject_x3f_1730_, 0);
lean_inc(v_val_1732_);
lean_dec_ref(v_subobject_x3f_1730_);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_projFn_1731_);
lean_ctor_set(v___x_1733_, 1, v_path_1725_);
v___x_1734_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1726_, v_baseStructName_1727_, v_val_1732_, v___x_1733_, v___y_1729_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v_subobject_x3f_1730_);
lean_dec_ref(v_field_1728_);
lean_dec(v_baseStructName_1727_);
lean_dec_ref(v_env_1726_);
lean_dec(v_path_1725_);
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___y_1729_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1737_, lean_object* v_baseStructName_1738_, lean_object* v_structName_1739_, lean_object* v_path_1740_, lean_object* v_a_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_name_eq(v_baseStructName_1738_, v_structName_1739_);
if (v___x_1742_ == 0)
{
lean_object* v___f_1743_; lean_object* v___f_1744_; uint8_t v___x_1758_; 
lean_inc(v_baseStructName_1738_);
lean_inc_ref_n(v_env_1737_, 2);
lean_inc(v_path_1740_);
v___f_1743_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0), 5, 3);
lean_closure_set(v___f_1743_, 0, v_path_1740_);
lean_closure_set(v___f_1743_, 1, v_env_1737_);
lean_closure_set(v___f_1743_, 2, v_baseStructName_1738_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1), 5, 3);
lean_closure_set(v___f_1744_, 0, v_path_1740_);
lean_closure_set(v___f_1744_, 1, v_env_1737_);
lean_closure_set(v___f_1744_, 2, v_baseStructName_1738_);
v___x_1758_ = l_Lean_NameSet_contains(v_a_1741_, v_structName_1739_);
if (v___x_1758_ == 0)
{
goto v___jp_1745_;
}
else
{
if (v___x_1742_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref(v___f_1744_);
lean_dec_ref(v___f_1743_);
lean_dec(v_structName_1739_);
lean_dec_ref(v_env_1737_);
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v_a_1741_);
return v___x_1760_;
}
else
{
goto v___jp_1745_;
}
}
v___jp_1745_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc(v_structName_1739_);
v___x_1746_ = l_Lean_NameSet_insert(v_a_1741_, v_structName_1739_);
v___x_1747_ = l_Lean_getStructureInfo_x3f(v_env_1737_, v_structName_1739_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v_fieldInfo_1749_; lean_object* v_parentInfo_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_fst_1753_; 
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref(v___x_1747_);
v_fieldInfo_1749_ = lean_ctor_get(v_val_1748_, 2);
lean_inc_ref(v_fieldInfo_1749_);
v_parentInfo_1750_ = lean_ctor_get(v_val_1748_, 3);
lean_inc_ref(v_parentInfo_1750_);
lean_dec(v_val_1748_);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1744_, v_fieldInfo_1749_, v___x_1751_, v___x_1746_);
lean_dec_ref(v_fieldInfo_1749_);
v_fst_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_fst_1753_);
if (lean_obj_tag(v_fst_1753_) == 0)
{
lean_object* v_snd_1754_; lean_object* v___x_1755_; 
v_snd_1754_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1754_);
lean_dec_ref(v___x_1752_);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1743_, v_parentInfo_1750_, v___x_1751_, v_snd_1754_);
lean_dec_ref(v_parentInfo_1750_);
return v___x_1755_;
}
else
{
lean_dec_ref(v_fst_1753_);
lean_dec_ref(v_parentInfo_1750_);
lean_dec_ref(v___f_1743_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1747_);
lean_dec_ref(v___f_1744_);
lean_dec_ref(v___f_1743_);
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1746_);
return v___x_1757_;
}
}
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_structName_1739_);
lean_dec(v_baseStructName_1738_);
lean_dec_ref(v_env_1737_);
v___x_1761_ = l_List_reverse___redArg(v_path_1740_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1741_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0(lean_object* v_path_1764_, lean_object* v_env_1765_, lean_object* v_baseStructName_1766_, lean_object* v_parent_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_structName_1769_; lean_object* v_projFn_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_structName_1769_ = lean_ctor_get(v_parent_1767_, 0);
lean_inc(v_structName_1769_);
v_projFn_1770_ = lean_ctor_get(v_parent_1767_, 1);
lean_inc(v_projFn_1770_);
lean_dec_ref(v_parent_1767_);
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_projFn_1770_);
lean_ctor_set(v___x_1771_, 1, v_path_1764_);
v___x_1772_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1765_, v_baseStructName_1766_, v_structName_1769_, v___x_1771_, v___y_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_00_u03b2_1773_, lean_object* v_00_u03b1_1774_, lean_object* v_f_1775_, lean_object* v_as_1776_, lean_object* v_i_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1775_, v_as_1776_, v_i_1777_, v___y_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_00_u03b1_1781_, lean_object* v_f_1782_, lean_object* v_as_1783_, lean_object* v_i_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_00_u03b2_1780_, v_00_u03b1_1781_, v_f_1782_, v_as_1783_, v_i_1784_, v___y_1785_);
lean_dec_ref(v_as_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1787_, lean_object* v_baseStructName_1788_, lean_object* v_structName_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_fst_1793_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = l_Lean_NameSet_empty;
v___x_1792_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1787_, v_baseStructName_1788_, v_structName_1789_, v___x_1790_, v___x_1791_);
v_fst_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_fst_1793_);
lean_dec_ref(v___x_1792_);
return v_fst_1793_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1794_, lean_object* v_constName_1795_){
_start:
{
uint8_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = 0;
v___x_1797_ = l_Lean_Environment_find_x3f(v_env_1794_, v_constName_1795_, v___x_1796_);
if (lean_obj_tag(v___x_1797_) == 1)
{
lean_object* v_val_1798_; 
v_val_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_val_1798_);
lean_dec_ref(v___x_1797_);
if (lean_obj_tag(v_val_1798_) == 5)
{
lean_object* v_val_1799_; lean_object* v_numIndices_1800_; lean_object* v_ctors_1801_; uint8_t v_isRec_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_val_1799_ = lean_ctor_get(v_val_1798_, 0);
lean_inc_ref(v_val_1799_);
lean_dec_ref(v_val_1798_);
v_numIndices_1800_ = lean_ctor_get(v_val_1799_, 2);
lean_inc(v_numIndices_1800_);
v_ctors_1801_ = lean_ctor_get(v_val_1799_, 4);
lean_inc(v_ctors_1801_);
v_isRec_1802_ = lean_ctor_get_uint8(v_val_1799_, sizeof(void*)*6);
lean_dec_ref(v_val_1799_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_nat_dec_eq(v_numIndices_1800_, v___x_1803_);
lean_dec(v_numIndices_1800_);
if (v___x_1804_ == 0)
{
lean_dec(v_ctors_1801_);
return v___x_1796_;
}
else
{
if (lean_obj_tag(v_ctors_1801_) == 1)
{
lean_object* v_tail_1805_; 
v_tail_1805_ = lean_ctor_get(v_ctors_1801_, 1);
lean_inc(v_tail_1805_);
lean_dec_ref(v_ctors_1801_);
if (lean_obj_tag(v_tail_1805_) == 0)
{
if (v_isRec_1802_ == 0)
{
return v___x_1804_;
}
else
{
return v___x_1796_;
}
}
else
{
lean_dec(v_tail_1805_);
return v___x_1796_;
}
}
else
{
lean_dec(v_ctors_1801_);
return v___x_1796_;
}
}
}
else
{
lean_dec(v_val_1798_);
return v___x_1796_;
}
}
else
{
lean_dec(v___x_1797_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1806_, lean_object* v_constName_1807_){
_start:
{
uint8_t v_res_1808_; lean_object* v_r_1809_; 
v_res_1808_ = l_Lean_isNonRecStructure(v_env_1806_, v_constName_1807_);
v_r_1809_ = lean_box(v_res_1808_);
return v_r_1809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_panic_fn_borrowed(v___x_1811_, v_msg_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1815_ = lean_unsigned_to_nat(11u);
v___x_1816_ = lean_unsigned_to_nat(374u);
v___x_1817_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1818_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1819_ = l_mkPanicMessageWithDecl(v___x_1818_, v___x_1817_, v___x_1816_, v___x_1815_, v___x_1814_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1820_, lean_object* v_constName_1821_){
_start:
{
uint8_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = 0;
lean_inc_ref(v_env_1820_);
v___x_1826_ = l_Lean_Environment_find_x3f(v_env_1820_, v_constName_1821_, v___x_1825_);
if (lean_obj_tag(v___x_1826_) == 1)
{
lean_object* v_val_1827_; 
v_val_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1827_);
lean_dec_ref(v___x_1826_);
if (lean_obj_tag(v_val_1827_) == 5)
{
lean_object* v_val_1828_; lean_object* v_numIndices_1829_; lean_object* v_ctors_1830_; uint8_t v_isRec_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_val_1828_ = lean_ctor_get(v_val_1827_, 0);
lean_inc_ref(v_val_1828_);
lean_dec_ref(v_val_1827_);
v_numIndices_1829_ = lean_ctor_get(v_val_1828_, 2);
lean_inc(v_numIndices_1829_);
v_ctors_1830_ = lean_ctor_get(v_val_1828_, 4);
lean_inc(v_ctors_1830_);
v_isRec_1831_ = lean_ctor_get_uint8(v_val_1828_, sizeof(void*)*6);
lean_dec_ref(v_val_1828_);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_nat_dec_eq(v_numIndices_1829_, v___x_1832_);
lean_dec(v_numIndices_1829_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_ctors_1830_);
lean_dec_ref(v_env_1820_);
v___x_1834_ = lean_box(0);
return v___x_1834_;
}
else
{
if (lean_obj_tag(v_ctors_1830_) == 1)
{
lean_object* v_tail_1835_; 
v_tail_1835_ = lean_ctor_get(v_ctors_1830_, 1);
if (lean_obj_tag(v_tail_1835_) == 0)
{
if (v_isRec_1831_ == 0)
{
lean_object* v_head_1836_; lean_object* v___x_1837_; 
v_head_1836_ = lean_ctor_get(v_ctors_1830_, 0);
lean_inc(v_head_1836_);
lean_dec_ref(v_ctors_1830_);
v___x_1837_ = l_Lean_Environment_find_x3f(v_env_1820_, v_head_1836_, v_isRec_1831_);
if (lean_obj_tag(v___x_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_val_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_val_1838_) == 6)
{
lean_object* v_val_1842_; lean_object* v___x_1844_; 
v_val_1842_ = lean_ctor_get(v_val_1838_, 0);
lean_inc_ref(v_val_1842_);
lean_dec_ref(v_val_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_val_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_val_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
goto v___jp_1822_;
}
}
}
else
{
lean_dec(v___x_1837_);
goto v___jp_1822_;
}
}
else
{
lean_object* v___x_1847_; 
lean_dec_ref(v_ctors_1830_);
lean_dec_ref(v_env_1820_);
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
}
else
{
lean_object* v___x_1848_; 
lean_dec_ref(v_ctors_1830_);
lean_dec_ref(v_env_1820_);
v___x_1848_ = lean_box(0);
return v___x_1848_;
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v_ctors_1830_);
lean_dec_ref(v_env_1820_);
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
}
}
else
{
lean_object* v___x_1850_; 
lean_dec(v_val_1827_);
lean_dec_ref(v_env_1820_);
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
}
else
{
lean_object* v___x_1851_; 
lean_dec(v___x_1826_);
lean_dec_ref(v_env_1820_);
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
v___jp_1822_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1824_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1852_, lean_object* v_constName_1853_){
_start:
{
uint8_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = 0;
lean_inc_ref(v_env_1852_);
v___x_1855_ = l_Lean_Environment_find_x3f(v_env_1852_, v_constName_1853_, v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 1)
{
lean_object* v_val_1856_; 
v_val_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1856_);
lean_dec_ref(v___x_1855_);
if (lean_obj_tag(v_val_1856_) == 5)
{
lean_object* v_val_1857_; lean_object* v_numIndices_1858_; lean_object* v_ctors_1859_; uint8_t v_isRec_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_val_1857_ = lean_ctor_get(v_val_1856_, 0);
lean_inc_ref(v_val_1857_);
lean_dec_ref(v_val_1856_);
v_numIndices_1858_ = lean_ctor_get(v_val_1857_, 2);
lean_inc(v_numIndices_1858_);
v_ctors_1859_ = lean_ctor_get(v_val_1857_, 4);
lean_inc(v_ctors_1859_);
v_isRec_1860_ = lean_ctor_get_uint8(v_val_1857_, sizeof(void*)*6);
lean_dec_ref(v_val_1857_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_nat_dec_eq(v_numIndices_1858_, v___x_1861_);
lean_dec(v_numIndices_1858_);
if (v___x_1862_ == 0)
{
lean_dec(v_ctors_1859_);
lean_dec_ref(v_env_1852_);
return v___x_1861_;
}
else
{
if (lean_obj_tag(v_ctors_1859_) == 1)
{
lean_object* v_tail_1863_; 
v_tail_1863_ = lean_ctor_get(v_ctors_1859_, 1);
if (lean_obj_tag(v_tail_1863_) == 0)
{
if (v_isRec_1860_ == 0)
{
lean_object* v_head_1864_; lean_object* v___x_1865_; 
v_head_1864_ = lean_ctor_get(v_ctors_1859_, 0);
lean_inc(v_head_1864_);
lean_dec_ref(v_ctors_1859_);
v___x_1865_ = l_Lean_Environment_find_x3f(v_env_1852_, v_head_1864_, v_isRec_1860_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v___x_1865_);
if (lean_obj_tag(v_val_1866_) == 6)
{
lean_object* v_val_1867_; lean_object* v_numFields_1868_; 
v_val_1867_ = lean_ctor_get(v_val_1866_, 0);
lean_inc_ref(v_val_1867_);
lean_dec_ref(v_val_1866_);
v_numFields_1868_ = lean_ctor_get(v_val_1867_, 4);
lean_inc(v_numFields_1868_);
lean_dec_ref(v_val_1867_);
return v_numFields_1868_;
}
else
{
lean_dec(v_val_1866_);
return v___x_1861_;
}
}
else
{
lean_dec(v___x_1865_);
return v___x_1861_;
}
}
else
{
lean_dec_ref(v_ctors_1859_);
lean_dec_ref(v_env_1852_);
return v___x_1861_;
}
}
else
{
lean_dec_ref(v_ctors_1859_);
lean_dec_ref(v_env_1852_);
return v___x_1861_;
}
}
else
{
lean_dec(v_ctors_1859_);
lean_dec_ref(v_env_1852_);
return v___x_1861_;
}
}
}
else
{
lean_object* v___x_1869_; 
lean_dec(v_val_1856_);
lean_dec_ref(v_env_1852_);
v___x_1869_ = lean_unsigned_to_nat(0u);
return v___x_1869_;
}
}
else
{
lean_object* v___x_1870_; 
lean_dec(v___x_1855_);
lean_dec_ref(v_env_1852_);
v___x_1870_ = lean_unsigned_to_nat(0u);
return v___x_1870_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_1879_);
return v_res_1881_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___f_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1883_, 0, v___x_1882_);
return v___f_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___f_1885_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_box(1);
v___x_1888_ = l_Lean_registerEnvExtension___redArg(v___f_1885_, v___x_1886_, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_1891_, lean_object* v_structName_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v_asyncMode_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1893_ = l_Lean_structureResolutionExt;
v_asyncMode_1894_ = lean_ctor_get(v___x_1893_, 2);
v___x_1895_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_1896_ = lean_box(0);
v___x_1897_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1895_, v___x_1893_, v_env_1891_, v_asyncMode_1894_, v___x_1896_);
v___x_1898_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_1897_, v_structName_1892_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_1899_, lean_object* v_structName_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_1899_, v_structName_1900_);
lean_dec(v_structName_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_1902_, lean_object* v___x_1903_, lean_object* v_structName_1904_, lean_object* v_resolutionOrder_1905_, lean_object* v_s_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1902_, v___x_1903_, v_s_1906_, v_structName_1904_, v_resolutionOrder_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_1908_, lean_object* v_env_1909_){
_start:
{
lean_object* v___x_1910_; lean_object* v_asyncMode_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = l_Lean_structureResolutionExt;
v_asyncMode_1911_ = lean_ctor_get(v___x_1910_, 2);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1910_, v_env_1909_, v___f_1908_, v_asyncMode_1911_, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_1914_, lean_object* v_structName_1915_, lean_object* v_resolutionOrder_1916_){
_start:
{
lean_object* v_modifyEnv_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; 
v_modifyEnv_1917_ = lean_ctor_get(v_inst_1914_, 1);
lean_inc(v_modifyEnv_1917_);
lean_dec_ref(v_inst_1914_);
v___x_1918_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1919_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_1920_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1920_, 0, v___x_1918_);
lean_closure_set(v___f_1920_, 1, v___x_1919_);
lean_closure_set(v___f_1920_, 2, v_structName_1915_);
lean_closure_set(v___f_1920_, 3, v_resolutionOrder_1916_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1921_, 0, v___f_1920_);
v___x_1922_ = lean_apply_1(v_modifyEnv_1917_, v___f_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_1923_, lean_object* v_inst_1924_, lean_object* v_structName_1925_, lean_object* v_resolutionOrder_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_1924_, v_structName_1925_, v_resolutionOrder_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_1945_, lean_object* v_resOrders_1946_, lean_object* v___x_1947_, lean_object* v_toPure_1948_, lean_object* v_____s_1949_){
_start:
{
lean_object* v_fst_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1965_; 
v_fst_1950_ = lean_ctor_get(v_____s_1949_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_____s_1949_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_____s_1949_, 1);
lean_dec(v_unused_1966_);
v___x_1952_ = v_____s_1949_;
v_isShared_1953_ = v_isSharedCheck_1965_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_fst_1950_);
lean_dec(v_____s_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1965_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
if (lean_obj_tag(v_fst_1950_) == 0)
{
uint8_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1954_ = 0;
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_array_get_borrowed(v___x_1945_, v_resOrders_1946_, v___x_1955_);
v___x_1957_ = lean_array_get_borrowed(v___x_1947_, v___x_1956_, v___x_1955_);
v___x_1958_ = lean_box(v___x_1954_);
lean_inc(v___x_1957_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v___x_1957_);
lean_ctor_set(v___x_1952_, 0, v___x_1958_);
v___x_1960_ = v___x_1952_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1957_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1960_);
return v___x_1961_;
}
}
else
{
lean_object* v_val_1963_; lean_object* v___x_1964_; 
lean_del_object(v___x_1952_);
v_val_1963_ = lean_ctor_get(v_fst_1950_, 0);
lean_inc(v_val_1963_);
lean_dec_ref(v_fst_1950_);
v___x_1964_ = lean_apply_2(v_toPure_1948_, lean_box(0), v_val_1963_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_1967_, lean_object* v_resOrders_1968_, lean_object* v___x_1969_, lean_object* v_toPure_1970_, lean_object* v_____s_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_1967_, v_resOrders_1968_, v___x_1969_, v_toPure_1970_, v_____s_1971_);
lean_dec(v___x_1969_);
lean_dec_ref(v_resOrders_1968_);
lean_dec_ref(v___x_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_1973_, lean_object* v_____do__lift_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_apply_2(v_toPure_1973_, lean_box(0), v_____do__lift_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_1976_, lean_object* v_toPure_1977_, lean_object* v___x_1978_, lean_object* v_____s_1979_){
_start:
{
lean_object* v_fst_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1998_; 
v_fst_1980_ = lean_ctor_get(v_____s_1979_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_____s_1979_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_____s_1979_, 1);
lean_dec(v_unused_1999_);
v___x_1982_ = v_____s_1979_;
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_fst_1980_);
lean_dec(v_____s_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
if (lean_obj_tag(v_fst_1980_) == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_del_object(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1976_);
v___x_1985_ = lean_apply_2(v_toPure_1977_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref(v___x_1976_);
lean_inc_ref(v_fst_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___x_1978_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_fst_1980_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1978_);
v___x_1987_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v_fst_1980_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_fst_1980_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v_fst_1980_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v_fst_1980_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_apply_2(v_toPure_1977_, lean_box(0), v___x_1992_);
return v___x_1993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2000_, lean_object* v_next_2001_, lean_object* v_G_2002_, lean_object* v_____do__lift_2003_){
_start:
{
if (lean_obj_tag(v_____do__lift_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
lean_dec(v_G_2002_);
v_a_2004_ = lean_ctor_get(v_____do__lift_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v_____do__lift_2003_);
v___x_2005_ = lean_apply_2(v_toPure_2000_, lean_box(0), v_a_2004_);
return v___x_2005_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_toPure_2000_);
v_a_2006_ = lean_ctor_get(v_____do__lift_2003_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v_____do__lift_2003_);
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_add(v_next_2001_, v___x_2007_);
v___x_2009_ = lean_apply_4(v_G_2002_, v___x_2008_, v_a_2006_, lean_box(0), lean_box(0));
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2010_, lean_object* v_next_2011_, lean_object* v_G_2012_, lean_object* v_____do__lift_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2010_, v_next_2011_, v_G_2012_, v_____do__lift_2013_);
lean_dec(v_next_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2015_, lean_object* v_v_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_name_eq(v_v_2016_, v___x_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2018_, lean_object* v_v_2019_){
_start:
{
uint8_t v_res_2020_; lean_object* v_r_2021_; 
v_res_2020_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2018_, v_v_2019_);
lean_dec(v_v_2019_);
lean_dec(v___x_2018_);
v_r_2021_ = lean_box(v_res_2020_);
return v_r_2021_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2041_, lean_object* v___f_2042_, lean_object* v_resOrder_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_array_2048_; lean_object* v_start_2049_; lean_object* v_stop_2050_; uint8_t v___x_2051_; lean_object* v___y_2053_; 
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_array_get_size(v_resOrder_2043_);
v___x_2046_ = l_Array_toSubarray___redArg(v_resOrder_2043_, v___x_2044_, v___x_2045_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2048_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_array_2048_);
v_start_2049_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_start_2049_);
v_stop_2050_ = lean_ctor_get(v___x_2046_, 2);
lean_inc(v_stop_2050_);
lean_dec_ref(v___x_2046_);
v___x_2051_ = lean_nat_dec_lt(v_start_2049_, v_stop_2050_);
if (v___x_2051_ == 0)
{
lean_dec(v_stop_2050_);
lean_dec(v_start_2049_);
lean_dec_ref(v_array_2048_);
lean_dec_ref(v___f_2042_);
return v___x_2041_;
}
else
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = lean_array_get_size(v_array_2048_);
v___x_2061_ = lean_nat_dec_le(v_stop_2050_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec(v_stop_2050_);
v___y_2053_ = v___x_2060_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v_stop_2050_;
goto v___jp_2052_;
}
}
v___jp_2052_:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_nat_dec_lt(v_start_2049_, v___y_2053_);
if (v___x_2054_ == 0)
{
lean_dec(v___y_2053_);
lean_dec(v_start_2049_);
lean_dec_ref(v_array_2048_);
lean_dec_ref(v___f_2042_);
return v___x_2051_;
}
else
{
size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2055_ = lean_usize_of_nat(v_start_2049_);
lean_dec(v_start_2049_);
v___x_2056_ = lean_usize_of_nat(v___y_2053_);
lean_dec(v___y_2053_);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2047_, v___f_2042_, v_array_2048_, v___x_2055_, v___x_2056_);
v___x_2058_ = lean_unbox(v___x_2057_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
return v___x_2054_;
}
else
{
uint8_t v___x_2059_; 
v___x_2059_ = 0;
return v___x_2059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2062_, lean_object* v___f_2063_, lean_object* v_resOrder_2064_){
_start:
{
uint8_t v___x_1715__boxed_2065_; uint8_t v_res_2066_; lean_object* v_r_2067_; 
v___x_1715__boxed_2065_ = lean_unbox(v___x_2062_);
v_res_2066_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2065_, v___f_2063_, v_resOrder_2064_);
v_r_2067_ = lean_box(v_res_2066_);
return v_r_2067_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2068_, uint8_t v___y_2069_, lean_object* v_v_2070_){
_start:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_apply_1(v___f_2068_, v_v_2070_);
v___x_2072_ = lean_unbox(v___x_2071_);
if (v___x_2072_ == 0)
{
return v___y_2069_;
}
else
{
uint8_t v___x_2073_; 
v___x_2073_ = 0;
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2074_, lean_object* v___y_2075_, lean_object* v_v_2076_){
_start:
{
uint8_t v___y_1771__boxed_2077_; uint8_t v_res_2078_; lean_object* v_r_2079_; 
v___y_1771__boxed_2077_ = lean_unbox(v___y_2075_);
v_res_2078_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2074_, v___y_1771__boxed_2077_, v_v_2076_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2080_, uint8_t v___x_2081_, lean_object* v_v_2082_){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_apply_1(v___f_2080_, v_v_2082_);
v___x_2084_ = lean_unbox(v___x_2083_);
if (v___x_2084_ == 0)
{
return v___x_2081_;
}
else
{
uint8_t v___x_2085_; 
v___x_2085_ = 0;
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2086_, lean_object* v___x_2087_, lean_object* v_v_2088_){
_start:
{
uint8_t v___x_1783__boxed_2089_; uint8_t v_res_2090_; lean_object* v_r_2091_; 
v___x_1783__boxed_2089_ = lean_unbox(v___x_2087_);
v_res_2090_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2086_, v___x_1783__boxed_2089_, v_v_2088_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2092_, lean_object* v_toPure_2093_, lean_object* v___x_2094_, lean_object* v_resOrders_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v_toBind_2098_, lean_object* v___f_2099_, lean_object* v___x_2100_, lean_object* v_next_2101_, lean_object* v___x_2102_, lean_object* v_next_2103_, lean_object* v_acc_2104_, lean_object* v_h_2105_, lean_object* v_G_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_nat_dec_lt(v_next_2103_, v___x_2092_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec(v_G_2106_);
lean_dec(v_next_2103_);
lean_dec_ref(v___x_2100_);
lean_dec(v___f_2099_);
lean_dec(v_toBind_2098_);
lean_dec(v___x_2097_);
lean_dec_ref(v_resOrders_2095_);
lean_dec(v___x_2092_);
v___x_2108_ = lean_apply_2(v_toPure_2093_, lean_box(0), v_acc_2104_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_array_2113_; lean_object* v_start_2114_; lean_object* v_stop_2115_; lean_object* v___f_2116_; lean_object* v___y_2118_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___f_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; uint8_t v___y_2147_; uint8_t v___x_2159_; 
lean_dec_ref(v_acc_2104_);
v___x_2109_ = lean_array_get_borrowed(v___x_2094_, v_resOrders_2095_, v_next_2103_);
v___x_2110_ = lean_array_get(v___x_2096_, v___x_2109_, v___x_2097_);
lean_inc_n(v_next_2103_, 2);
lean_inc(v___x_2097_);
lean_inc_ref(v_resOrders_2095_);
v___x_2111_ = l_Array_toSubarray___redArg(v_resOrders_2095_, v___x_2097_, v_next_2103_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2113_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_array_2113_);
v_start_2114_ = lean_ctor_get(v___x_2111_, 1);
lean_inc(v_start_2114_);
v_stop_2115_ = lean_ctor_get(v___x_2111_, 2);
lean_inc(v_stop_2115_);
lean_dec_ref(v___x_2111_);
lean_inc(v_toPure_2093_);
v___f_2116_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2116_, 0, v_toPure_2093_);
lean_closure_set(v___f_2116_, 1, v_next_2103_);
lean_closure_set(v___f_2116_, 2, v_G_2106_);
lean_inc(v___x_2110_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2143_, 0, v___x_2110_);
v___x_2144_ = lean_box(v___x_2107_);
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2145_, 0, v___x_2144_);
lean_closure_set(v___f_2145_, 1, v___f_2143_);
v___x_2159_ = lean_nat_dec_lt(v_start_2114_, v_stop_2115_);
if (v___x_2159_ == 0)
{
lean_dec(v_stop_2115_);
lean_dec(v_start_2114_);
lean_dec_ref(v_array_2113_);
v___y_2147_ = v___x_2107_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2160_; lean_object* v___f_2161_; lean_object* v___y_2163_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2160_ = lean_box(v___x_2107_);
lean_inc_ref(v___f_2145_);
v___f_2161_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2161_, 0, v___f_2145_);
lean_closure_set(v___f_2161_, 1, v___x_2160_);
v___x_2169_ = lean_array_get_size(v_array_2113_);
v___x_2170_ = lean_nat_dec_le(v_stop_2115_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec(v_stop_2115_);
v___y_2163_ = v___x_2169_;
goto v___jp_2162_;
}
else
{
v___y_2163_ = v_stop_2115_;
goto v___jp_2162_;
}
v___jp_2162_:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_lt(v_start_2114_, v___y_2163_);
if (v___x_2164_ == 0)
{
lean_dec(v___y_2163_);
lean_dec_ref(v___f_2161_);
lean_dec(v_start_2114_);
lean_dec_ref(v_array_2113_);
v___y_2147_ = v___x_2159_;
goto v___jp_2146_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2165_ = lean_usize_of_nat(v_start_2114_);
lean_dec(v_start_2114_);
v___x_2166_ = lean_usize_of_nat(v___y_2163_);
lean_dec(v___y_2163_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2112_, v___f_2161_, v_array_2113_, v___x_2165_, v___x_2166_);
v___x_2168_ = lean_unbox(v___x_2167_);
lean_dec(v___x_2167_);
if (v___x_2168_ == 0)
{
v___y_2147_ = v___x_2164_;
goto v___jp_2146_;
}
else
{
lean_dec_ref(v___f_2145_);
lean_dec(v___x_2110_);
lean_dec(v_next_2103_);
lean_dec(v___x_2097_);
lean_dec_ref(v_resOrders_2095_);
lean_dec(v___x_2092_);
goto v___jp_2121_;
}
}
}
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_inc(v_toBind_2098_);
v___x_2119_ = lean_apply_4(v_toBind_2098_, lean_box(0), lean_box(0), v___y_2118_, v___f_2099_);
v___x_2120_ = lean_apply_4(v_toBind_2098_, lean_box(0), lean_box(0), v___x_2119_, v___f_2116_);
return v___x_2120_;
}
v___jp_2121_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2100_);
v___x_2123_ = lean_apply_2(v_toPure_2093_, lean_box(0), v___x_2122_);
v___y_2118_ = v___x_2123_;
goto v___jp_2117_;
}
v___jp_2124_:
{
uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2125_ = lean_nat_dec_eq(v_next_2101_, v___x_2097_);
lean_dec(v___x_2097_);
v___x_2126_ = lean_box(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2110_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2102_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_apply_2(v_toPure_2093_, lean_box(0), v___x_2130_);
v___y_2118_ = v___x_2131_;
goto v___jp_2117_;
}
v___jp_2132_:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_nat_dec_lt(v___y_2136_, v___y_2137_);
if (v___x_2138_ == 0)
{
lean_dec(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___x_2100_);
goto v___jp_2124_;
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = lean_usize_of_nat(v___y_2136_);
lean_dec(v___y_2136_);
v___x_2140_ = lean_usize_of_nat(v___y_2137_);
lean_dec(v___y_2137_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2135_, v___y_2133_, v___y_2134_, v___x_2139_, v___x_2140_);
v___x_2142_ = lean_unbox(v___x_2141_);
lean_dec(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec_ref(v___x_2100_);
goto v___jp_2124_;
}
else
{
lean_dec(v___x_2110_);
lean_dec(v___x_2097_);
goto v___jp_2121_;
}
}
}
v___jp_2146_:
{
if (v___y_2147_ == 0)
{
lean_dec_ref(v___f_2145_);
lean_dec(v___x_2110_);
lean_dec(v_next_2103_);
lean_dec(v___x_2097_);
lean_dec_ref(v_resOrders_2095_);
lean_dec(v___x_2092_);
goto v___jp_2121_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_array_2151_; lean_object* v_start_2152_; lean_object* v_stop_2153_; uint8_t v___x_2154_; 
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_add(v_next_2103_, v___x_2148_);
lean_dec(v_next_2103_);
v___x_2150_ = l_Array_toSubarray___redArg(v_resOrders_2095_, v___x_2149_, v___x_2092_);
v_array_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_ref(v_array_2151_);
v_start_2152_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_start_2152_);
v_stop_2153_ = lean_ctor_get(v___x_2150_, 2);
lean_inc(v_stop_2153_);
lean_dec_ref(v___x_2150_);
v___x_2154_ = lean_nat_dec_lt(v_start_2152_, v_stop_2153_);
if (v___x_2154_ == 0)
{
lean_dec(v_stop_2153_);
lean_dec(v_start_2152_);
lean_dec_ref(v_array_2151_);
lean_dec_ref(v___f_2145_);
lean_dec_ref(v___x_2100_);
goto v___jp_2124_;
}
else
{
lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2155_ = lean_box(v___y_2147_);
v___f_2156_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2156_, 0, v___f_2145_);
lean_closure_set(v___f_2156_, 1, v___x_2155_);
v___x_2157_ = lean_array_get_size(v_array_2151_);
v___x_2158_ = lean_nat_dec_le(v_stop_2153_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_dec(v_stop_2153_);
v___y_2133_ = v___f_2156_;
v___y_2134_ = v_array_2151_;
v___y_2135_ = v___x_2112_;
v___y_2136_ = v_start_2152_;
v___y_2137_ = v___x_2157_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v___f_2156_;
v___y_2134_ = v_array_2151_;
v___y_2135_ = v___x_2112_;
v___y_2136_ = v_start_2152_;
v___y_2137_ = v_stop_2153_;
goto v___jp_2132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2171_, lean_object* v_toPure_2172_, lean_object* v___x_2173_, lean_object* v_resOrders_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_toBind_2177_, lean_object* v___f_2178_, lean_object* v___x_2179_, lean_object* v_next_2180_, lean_object* v___x_2181_, lean_object* v_next_2182_, lean_object* v_acc_2183_, lean_object* v_h_2184_, lean_object* v_G_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2171_, v_toPure_2172_, v___x_2173_, v_resOrders_2174_, v___x_2175_, v___x_2176_, v_toBind_2177_, v___f_2178_, v___x_2179_, v_next_2180_, v___x_2181_, v_next_2182_, v_acc_2183_, v_h_2184_, v_G_2185_);
lean_dec(v_next_2180_);
lean_dec(v___x_2175_);
lean_dec_ref(v___x_2173_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2187_, lean_object* v_toPure_2188_, lean_object* v___x_2189_, lean_object* v_resOrders_2190_, lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v_toBind_2193_, lean_object* v___f_2194_, lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v___f_2197_, lean_object* v___f_2198_, lean_object* v_next_2199_, lean_object* v_acc_2200_, lean_object* v_h_2201_, lean_object* v_G_2202_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_nat_dec_lt(v_next_2199_, v___x_2187_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_G_2202_);
lean_dec(v_next_2199_);
lean_dec(v___f_2198_);
lean_dec(v___f_2197_);
lean_dec_ref(v___x_2195_);
lean_dec(v___f_2194_);
lean_dec(v_toBind_2193_);
lean_dec(v___x_2192_);
lean_dec(v___x_2191_);
lean_dec_ref(v_resOrders_2190_);
lean_dec_ref(v___x_2189_);
v___x_2204_ = lean_apply_2(v_toPure_2188_, lean_box(0), v_acc_2200_);
return v___x_2204_;
}
else
{
lean_object* v___f_2205_; lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_acc_2200_);
lean_inc(v_next_2199_);
lean_inc(v_toPure_2188_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2205_, 0, v_toPure_2188_);
lean_closure_set(v___f_2205_, 1, v_next_2199_);
lean_closure_set(v___f_2205_, 2, v_G_2202_);
v___x_2206_ = lean_nat_sub(v___x_2187_, v_next_2199_);
lean_inc_ref(v___x_2195_);
lean_inc_n(v_toBind_2193_, 3);
lean_inc(v___x_2192_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2207_, 0, v___x_2206_);
lean_closure_set(v___f_2207_, 1, v_toPure_2188_);
lean_closure_set(v___f_2207_, 2, v___x_2189_);
lean_closure_set(v___f_2207_, 3, v_resOrders_2190_);
lean_closure_set(v___f_2207_, 4, v___x_2191_);
lean_closure_set(v___f_2207_, 5, v___x_2192_);
lean_closure_set(v___f_2207_, 6, v_toBind_2193_);
lean_closure_set(v___f_2207_, 7, v___f_2194_);
lean_closure_set(v___f_2207_, 8, v___x_2195_);
lean_closure_set(v___f_2207_, 9, v_next_2199_);
lean_closure_set(v___f_2207_, 10, v___x_2196_);
v___x_2208_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2207_, v___x_2192_, v___x_2195_, lean_box(0));
v___x_2209_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2208_, v___f_2197_);
v___x_2210_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2209_, v___f_2198_);
v___x_2211_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2210_, v___f_2205_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2212_, lean_object* v_toPure_2213_, lean_object* v___x_2214_, lean_object* v_resOrders_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v_toBind_2218_, lean_object* v___f_2219_, lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v___f_2222_, lean_object* v___f_2223_, lean_object* v_next_2224_, lean_object* v_acc_2225_, lean_object* v_h_2226_, lean_object* v_G_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2212_, v_toPure_2213_, v___x_2214_, v_resOrders_2215_, v___x_2216_, v___x_2217_, v_toBind_2218_, v___f_2219_, v___x_2220_, v___x_2221_, v___f_2222_, v___f_2223_, v_next_2224_, v_acc_2225_, v_h_2226_, v_G_2227_);
lean_dec(v___x_2212_);
return v_res_2228_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Array_instInhabited(lean_box(0));
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2233_, lean_object* v_resOrders_2234_){
_start:
{
lean_object* v_toApplicative_2235_; lean_object* v_toBind_2236_; lean_object* v_toPure_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_toApplicative_2235_ = lean_ctor_get(v_inst_2233_, 0);
lean_inc_ref(v_toApplicative_2235_);
v_toBind_2236_ = lean_ctor_get(v_inst_2233_, 1);
lean_inc_n(v_toBind_2236_, 2);
lean_dec_ref(v_inst_2233_);
v_toPure_2237_ = lean_ctor_get(v_toApplicative_2235_, 1);
lean_inc_n(v_toPure_2237_, 4);
lean_dec_ref(v_toApplicative_2235_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2240_ = lean_array_get_size(v_resOrders_2234_);
lean_inc_ref(v_resOrders_2234_);
v___f_2241_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2241_, 0, v___x_2239_);
lean_closure_set(v___f_2241_, 1, v_resOrders_2234_);
lean_closure_set(v___f_2241_, 2, v___x_2238_);
lean_closure_set(v___f_2241_, 3, v_toPure_2237_);
v___f_2242_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2242_, 0, v_toPure_2237_);
v___x_2243_ = lean_unsigned_to_nat(0u);
v___x_2244_ = lean_box(0);
v___x_2245_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2246_, 0, v___x_2245_);
lean_closure_set(v___f_2246_, 1, v_toPure_2237_);
lean_closure_set(v___f_2246_, 2, v___x_2244_);
lean_inc_ref(v___f_2242_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2247_, 0, v___x_2240_);
lean_closure_set(v___f_2247_, 1, v_toPure_2237_);
lean_closure_set(v___f_2247_, 2, v___x_2239_);
lean_closure_set(v___f_2247_, 3, v_resOrders_2234_);
lean_closure_set(v___f_2247_, 4, v___x_2238_);
lean_closure_set(v___f_2247_, 5, v___x_2243_);
lean_closure_set(v___f_2247_, 6, v_toBind_2236_);
lean_closure_set(v___f_2247_, 7, v___f_2242_);
lean_closure_set(v___f_2247_, 8, v___x_2245_);
lean_closure_set(v___f_2247_, 9, v___x_2244_);
lean_closure_set(v___f_2247_, 10, v___f_2246_);
lean_closure_set(v___f_2247_, 11, v___f_2242_);
v___x_2248_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2247_, v___x_2243_, v___x_2245_, lean_box(0));
v___x_2249_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2248_, v___f_2241_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2250_, lean_object* v_inst_2251_, lean_object* v_resOrders_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2251_, v_resOrders_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2254_){
_start:
{
lean_object* v_structName_2255_; 
v_structName_2255_ = lean_ctor_get(v_x_2254_, 0);
lean_inc(v_structName_2255_);
return v_structName_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2256_);
lean_dec_ref(v_x_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2258_, lean_object* v_result_2259_, lean_object* v_____r_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_apply_2(v_toPure_2258_, lean_box(0), v_result_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2262_, lean_object* v_inst_2263_, lean_object* v_structName_2264_, lean_object* v_toBind_2265_, lean_object* v_result_2266_){
_start:
{
lean_object* v_resolutionOrder_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_resolutionOrder_2267_ = lean_ctor_get(v_result_2266_, 0);
lean_inc_ref(v_resolutionOrder_2267_);
v___f_2268_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2268_, 0, v_toPure_2262_);
lean_closure_set(v___f_2268_, 1, v_result_2266_);
v___x_2269_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2263_, v_structName_2264_, v_resolutionOrder_2267_);
v___x_2270_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v___x_2269_, v___f_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v___x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_array_get_borrowed(v___x_2273_, v_x_2272_, v___x_2271_);
lean_inc(v___x_2274_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object* v___x_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__5(v___x_2275_, v_x_2276_);
lean_dec_ref(v_x_2276_);
lean_dec(v___x_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_snd_2278_, lean_object* v_x1_2279_, lean_object* v_x2_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_name_eq(v_x2_2280_, v_snd_2278_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_array_push(v_x1_2279_, v_x2_2280_);
return v___x_2282_;
}
else
{
lean_dec(v_x2_2280_);
return v_x1_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v_snd_2283_, lean_object* v_x1_2284_, lean_object* v_x2_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v_snd_2283_, v_x1_2284_, v_x2_2285_);
lean_dec(v_snd_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v_snd_2287_, lean_object* v_x_2288_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_name_eq(v_x_2288_, v_snd_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v_snd_2290_, lean_object* v_x_2291_){
_start:
{
uint8_t v_res_2292_; lean_object* v_r_2293_; 
v_res_2292_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v_snd_2290_, v_x_2291_);
lean_dec(v_x_2291_);
lean_dec(v_snd_2290_);
v_r_2293_ = lean_box(v_res_2292_);
return v_r_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2294_, lean_object* v_parentNames_2295_, lean_object* v_x_2296_){
_start:
{
uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_inc(v_x_2296_);
v___x_2297_ = l_Array_contains___redArg(v___x_2294_, v_parentNames_2295_, v_x_2296_);
v___x_2298_ = lean_box(v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_x_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2300_, lean_object* v___f_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2303_ = lean_array_get_size(v_x_2302_);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2300_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2306_ = lean_nat_dec_lt(v___x_2300_, v___x_2303_);
if (v___x_2306_ == 0)
{
lean_dec_ref(v_x_2302_);
lean_dec_ref(v___f_2301_);
return v___x_2304_;
}
else
{
uint8_t v___x_2307_; 
v___x_2307_ = lean_nat_dec_le(v___x_2303_, v___x_2303_);
if (v___x_2307_ == 0)
{
if (v___x_2306_ == 0)
{
lean_dec_ref(v_x_2302_);
lean_dec_ref(v___f_2301_);
return v___x_2304_;
}
else
{
size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2303_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2305_, v___f_2301_, v_x_2302_, v___x_2308_, v___x_2309_, v___x_2304_);
return v___x_2310_;
}
}
else
{
size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = lean_usize_of_nat(v___x_2303_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2305_, v___f_2301_, v_x_2302_, v___x_2311_, v___x_2312_, v___x_2304_);
return v___x_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2314_, lean_object* v___f_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2314_, v___f_2315_, v_x_2316_);
lean_dec(v___x_2314_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v___f_2318_, lean_object* v_x1_2319_, lean_object* v_x2_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_array_2325_; lean_object* v_start_2326_; lean_object* v_stop_2327_; lean_object* v___y_2329_; uint8_t v___x_2336_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_array_get_size(v_x2_2320_);
lean_inc_ref(v_x2_2320_);
v___x_2323_ = l_Array_toSubarray___redArg(v_x2_2320_, v___x_2321_, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2325_ = lean_ctor_get(v___x_2323_, 0);
lean_inc_ref(v_array_2325_);
v_start_2326_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_start_2326_);
v_stop_2327_ = lean_ctor_get(v___x_2323_, 2);
lean_inc(v_stop_2327_);
lean_dec_ref(v___x_2323_);
v___x_2336_ = lean_nat_dec_lt(v_start_2326_, v_stop_2327_);
if (v___x_2336_ == 0)
{
lean_dec(v_stop_2327_);
lean_dec(v_start_2326_);
lean_dec_ref(v_array_2325_);
lean_dec_ref(v_x2_2320_);
lean_dec_ref(v___f_2318_);
return v_x1_2319_;
}
else
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = lean_array_get_size(v_array_2325_);
v___x_2338_ = lean_nat_dec_le(v_stop_2327_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec(v_stop_2327_);
v___y_2329_ = v___x_2337_;
goto v___jp_2328_;
}
else
{
v___y_2329_ = v_stop_2327_;
goto v___jp_2328_;
}
}
v___jp_2328_:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_nat_dec_lt(v_start_2326_, v___y_2329_);
if (v___x_2330_ == 0)
{
lean_dec(v___y_2329_);
lean_dec(v_start_2326_);
lean_dec_ref(v_array_2325_);
lean_dec_ref(v_x2_2320_);
lean_dec_ref(v___f_2318_);
return v_x1_2319_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2331_ = lean_usize_of_nat(v_start_2326_);
lean_dec(v_start_2326_);
v___x_2332_ = lean_usize_of_nat(v___y_2329_);
lean_dec(v___y_2329_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2324_, v___f_2318_, v_array_2325_, v___x_2331_, v___x_2332_);
v___x_2334_ = lean_unbox(v___x_2333_);
lean_dec(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v_x2_2320_);
return v_x1_2319_;
}
else
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_array_push(v_x1_2319_, v_x2_2320_);
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v_toPure_2340_, lean_object* v___x_2341_, lean_object* v_fst_2342_, lean_object* v_fst_2343_, lean_object* v___f_2344_, uint8_t v_relaxed_2345_, lean_object* v_parentNames_2346_, lean_object* v_snd_2347_, lean_object* v___f_2348_, lean_object* v_____x_2349_){
_start:
{
lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v_fst_2358_; lean_object* v_snd_2359_; lean_object* v___f_2360_; lean_object* v___f_2361_; lean_object* v_defects_2363_; uint8_t v___x_2377_; 
v_fst_2358_ = lean_ctor_get(v_____x_2349_, 0);
lean_inc(v_fst_2358_);
v_snd_2359_ = lean_ctor_get(v_____x_2349_, 1);
lean_inc_n(v_snd_2359_, 2);
lean_dec_ref(v_____x_2349_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2360_, 0, v_snd_2359_);
lean_inc(v___x_2341_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2361_, 0, v___x_2341_);
lean_closure_set(v___f_2361_, 1, v___f_2360_);
v___x_2377_ = lean_unbox(v_fst_2358_);
lean_dec(v_fst_2358_);
if (v___x_2377_ == 0)
{
if (v_relaxed_2345_ == 0)
{
lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___y_2381_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2405_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2378_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2346_);
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2379_, 0, v___x_2378_);
lean_closure_set(v___f_2379_, 1, v_parentNames_2346_);
v___x_2416_ = lean_array_get_size(v_fst_2343_);
v___x_2417_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2419_ = lean_nat_dec_lt(v___x_2341_, v___x_2416_);
if (v___x_2419_ == 0)
{
v___y_2405_ = v___x_2417_;
goto v___jp_2404_;
}
else
{
lean_object* v___f_2420_; lean_object* v___f_2421_; uint8_t v___x_2422_; 
lean_inc(v_snd_2359_);
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_2420_, 0, v_snd_2359_);
v___f_2421_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10), 3, 1);
lean_closure_set(v___f_2421_, 0, v___f_2420_);
v___x_2422_ = lean_nat_dec_le(v___x_2416_, v___x_2416_);
if (v___x_2422_ == 0)
{
if (v___x_2419_ == 0)
{
lean_dec_ref(v___f_2421_);
v___y_2405_ = v___x_2417_;
goto v___jp_2404_;
}
else
{
size_t v___x_2423_; size_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = lean_usize_of_nat(v___x_2416_);
lean_inc(v_fst_2343_);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2418_, v___f_2421_, v_fst_2343_, v___x_2423_, v___x_2424_, v___x_2417_);
v___y_2405_ = v___x_2425_;
goto v___jp_2404_;
}
}
else
{
size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = ((size_t)0ULL);
v___x_2427_ = lean_usize_of_nat(v___x_2416_);
lean_inc(v_fst_2343_);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2418_, v___f_2421_, v_fst_2343_, v___x_2426_, v___x_2427_, v___x_2417_);
v___y_2405_ = v___x_2428_;
goto v___jp_2404_;
}
}
v___jp_2380_:
{
lean_object* v_conflicts_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_defects_2389_; 
v_conflicts_2382_ = l_Array_eraseReps___redArg(v___x_2378_, v___y_2381_);
lean_inc_n(v_snd_2359_, 2);
v___x_2383_ = l_Array_contains___redArg(v___x_2378_, v_parentNames_2346_, v_snd_2359_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2385_ = lean_array_size(v_conflicts_2382_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2384_, v___f_2379_, v_sz_2385_, v___x_2386_, v_conflicts_2382_);
v___x_2388_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2388_, 0, v_snd_2359_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*2, v___x_2383_);
v_defects_2389_ = lean_array_push(v_snd_2347_, v___x_2388_);
v_defects_2363_ = v_defects_2389_;
goto v___jp_2362_;
}
v___jp_2390_:
{
lean_object* v___x_2396_; 
lean_inc_ref(v___y_2392_);
v___x_2396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2392_, v___y_2391_, v___y_2393_, v___y_2394_, v___y_2395_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2395_);
lean_dec(v___y_2391_);
v___y_2381_ = v___x_2396_;
goto v___jp_2380_;
}
v___jp_2397_:
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_le(v___y_2402_, v___y_2400_);
if (v___x_2403_ == 0)
{
lean_dec(v___y_2400_);
lean_inc(v___y_2402_);
v___y_2391_ = v___y_2398_;
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2402_;
goto v___jp_2390_;
}
else
{
v___y_2391_ = v___y_2398_;
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2400_;
goto v___jp_2390_;
}
}
v___jp_2404_:
{
lean_object* v___x_2406_; size_t v_sz_2407_; size_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2406_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2407_ = lean_array_size(v___y_2405_);
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2406_, v___f_2348_, v_sz_2407_, v___x_2408_, v___y_2405_);
v___x_2410_ = lean_array_get_size(v___x_2409_);
v___x_2411_ = lean_nat_dec_eq(v___x_2410_, v___x_2341_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2412_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0));
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_sub(v___x_2410_, v___x_2413_);
v___x_2415_ = lean_nat_dec_le(v___x_2341_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_inc(v___x_2414_);
v___y_2398_ = v___x_2410_;
v___y_2399_ = v___x_2412_;
v___y_2400_ = v___x_2414_;
v___y_2401_ = v___x_2409_;
v___y_2402_ = v___x_2414_;
goto v___jp_2397_;
}
else
{
lean_inc(v___x_2341_);
v___y_2398_ = v___x_2410_;
v___y_2399_ = v___x_2412_;
v___y_2400_ = v___x_2414_;
v___y_2401_ = v___x_2409_;
v___y_2402_ = v___x_2341_;
goto v___jp_2397_;
}
}
else
{
v___y_2381_ = v___x_2409_;
goto v___jp_2380_;
}
}
}
else
{
lean_dec_ref(v___f_2348_);
lean_dec_ref(v_parentNames_2346_);
v_defects_2363_ = v_snd_2347_;
goto v___jp_2362_;
}
}
else
{
lean_dec_ref(v___f_2348_);
lean_dec_ref(v_parentNames_2346_);
v_defects_2363_ = v_snd_2347_;
goto v___jp_2362_;
}
v___jp_2350_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___y_2352_);
lean_ctor_set(v___x_2354_, 1, v___y_2351_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___y_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
v___x_2357_ = lean_apply_2(v_toPure_2340_, lean_box(0), v___x_2356_);
return v___x_2357_;
}
v___jp_2362_:
{
lean_object* v_resOrder_2364_; lean_object* v___x_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_resOrder_2364_ = lean_array_push(v_fst_2342_, v_snd_2359_);
v___x_2365_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2366_ = lean_array_size(v_fst_2343_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2365_, v___f_2361_, v_sz_2366_, v___x_2367_, v_fst_2343_);
v___x_2369_ = lean_array_get_size(v___x_2368_);
v___x_2370_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2371_ = lean_nat_dec_lt(v___x_2341_, v___x_2369_);
lean_dec(v___x_2341_);
if (v___x_2371_ == 0)
{
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2344_);
v___y_2351_ = v_defects_2363_;
v___y_2352_ = v_resOrder_2364_;
v___y_2353_ = v___x_2370_;
goto v___jp_2350_;
}
else
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_nat_dec_le(v___x_2369_, v___x_2369_);
if (v___x_2372_ == 0)
{
if (v___x_2371_ == 0)
{
lean_dec(v___x_2368_);
lean_dec_ref(v___f_2344_);
v___y_2351_ = v_defects_2363_;
v___y_2352_ = v_resOrder_2364_;
v___y_2353_ = v___x_2370_;
goto v___jp_2350_;
}
else
{
size_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_usize_of_nat(v___x_2369_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2365_, v___f_2344_, v___x_2368_, v___x_2367_, v___x_2373_, v___x_2370_);
v___y_2351_ = v_defects_2363_;
v___y_2352_ = v_resOrder_2364_;
v___y_2353_ = v___x_2374_;
goto v___jp_2350_;
}
}
else
{
size_t v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_usize_of_nat(v___x_2369_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2365_, v___f_2344_, v___x_2368_, v___x_2367_, v___x_2375_, v___x_2370_);
v___y_2351_ = v_defects_2363_;
v___y_2352_ = v_resOrder_2364_;
v___y_2353_ = v___x_2376_;
goto v___jp_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object* v_toPure_2429_, lean_object* v___x_2430_, lean_object* v_fst_2431_, lean_object* v_fst_2432_, lean_object* v___f_2433_, lean_object* v_relaxed_2434_, lean_object* v_parentNames_2435_, lean_object* v_snd_2436_, lean_object* v___f_2437_, lean_object* v_____x_2438_){
_start:
{
uint8_t v_relaxed_boxed_2439_; lean_object* v_res_2440_; 
v_relaxed_boxed_2439_ = lean_unbox(v_relaxed_2434_);
v_res_2440_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__11(v_toPure_2429_, v___x_2430_, v_fst_2431_, v_fst_2432_, v___f_2433_, v_relaxed_boxed_2439_, v_parentNames_2435_, v_snd_2436_, v___f_2437_, v_____x_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v___x_2441_, lean_object* v_toPure_2442_, lean_object* v___f_2443_, uint8_t v_relaxed_2444_, lean_object* v_parentNames_2445_, lean_object* v___f_2446_, lean_object* v_inst_2447_, lean_object* v_toBind_2448_, lean_object* v_x_2449_, lean_object* v_____s_2450_){
_start:
{
lean_object* v_snd_2451_; lean_object* v_fst_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2476_; 
v_snd_2451_ = lean_ctor_get(v_____s_2450_, 1);
v_fst_2452_ = lean_ctor_get(v_____s_2450_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_____s_2450_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2454_ = v_____s_2450_;
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snd_2451_);
lean_inc(v_fst_2452_);
lean_dec(v_____s_2450_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2475_; 
v_fst_2456_ = lean_ctor_get(v_snd_2451_, 0);
v_snd_2457_ = lean_ctor_get(v_snd_2451_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_snd_2451_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2459_ = v_snd_2451_;
v_isShared_2460_ = v_isSharedCheck_2475_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
lean_dec(v_snd_2451_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2475_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = lean_array_get_size(v_fst_2452_);
v___x_2462_ = lean_nat_dec_eq(v___x_2461_, v___x_2441_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_del_object(v___x_2459_);
lean_del_object(v___x_2454_);
v___x_2463_ = lean_box(v_relaxed_2444_);
lean_inc(v_fst_2452_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_2464_, 0, v_toPure_2442_);
lean_closure_set(v___f_2464_, 1, v___x_2441_);
lean_closure_set(v___f_2464_, 2, v_fst_2456_);
lean_closure_set(v___f_2464_, 3, v_fst_2452_);
lean_closure_set(v___f_2464_, 4, v___f_2443_);
lean_closure_set(v___f_2464_, 5, v___x_2463_);
lean_closure_set(v___f_2464_, 6, v_parentNames_2445_);
lean_closure_set(v___f_2464_, 7, v_snd_2457_);
lean_closure_set(v___f_2464_, 8, v___f_2446_);
v___x_2465_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2447_, v_fst_2452_);
v___x_2466_ = lean_apply_4(v_toBind_2448_, lean_box(0), lean_box(0), v___x_2465_, v___f_2464_);
return v___x_2466_;
}
else
{
lean_object* v___x_2468_; 
lean_dec(v_toBind_2448_);
lean_dec_ref(v_inst_2447_);
lean_dec_ref(v___f_2446_);
lean_dec_ref(v_parentNames_2445_);
lean_dec_ref(v___f_2443_);
lean_dec(v___x_2441_);
if (v_isShared_2460_ == 0)
{
v___x_2468_ = v___x_2459_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2456_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_snd_2457_);
v___x_2468_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2468_);
v___x_2470_ = v___x_2454_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_fst_2452_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
v___x_2472_ = lean_apply_2(v_toPure_2442_, lean_box(0), v___x_2471_);
return v___x_2472_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v___x_2477_, lean_object* v_toPure_2478_, lean_object* v___f_2479_, lean_object* v_relaxed_2480_, lean_object* v_parentNames_2481_, lean_object* v___f_2482_, lean_object* v_inst_2483_, lean_object* v_toBind_2484_, lean_object* v_x_2485_, lean_object* v_____s_2486_){
_start:
{
uint8_t v_relaxed_boxed_2487_; lean_object* v_res_2488_; 
v_relaxed_boxed_2487_ = lean_unbox(v_relaxed_2480_);
v_res_2488_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v___x_2477_, v_toPure_2478_, v___f_2479_, v_relaxed_boxed_2487_, v_parentNames_2481_, v___f_2482_, v_inst_2483_, v_toBind_2484_, v_x_2485_, v_____s_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v_toPure_2493_, lean_object* v___f_2494_, uint8_t v_relaxed_2495_, lean_object* v_parentNames_2496_, lean_object* v_inst_2497_, lean_object* v_toBind_2498_, lean_object* v_structName_2499_, lean_object* v___f_2500_, lean_object* v___f_2501_, lean_object* v_parentResOrders_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___y_2508_; lean_object* v_j_2517_; lean_object* v_as_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2503_ = lean_unsigned_to_nat(0u);
v___f_2504_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0));
v___x_2505_ = lean_box(v_relaxed_2495_);
lean_inc(v_toBind_2498_);
lean_inc_ref(v_inst_2497_);
lean_inc_ref(v_parentNames_2496_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2506_, 0, v___x_2503_);
lean_closure_set(v___f_2506_, 1, v_toPure_2493_);
lean_closure_set(v___f_2506_, 2, v___f_2494_);
lean_closure_set(v___f_2506_, 3, v___x_2505_);
lean_closure_set(v___f_2506_, 4, v_parentNames_2496_);
lean_closure_set(v___f_2506_, 5, v___f_2504_);
lean_closure_set(v___f_2506_, 6, v_inst_2497_);
lean_closure_set(v___f_2506_, 7, v_toBind_2498_);
v_j_2517_ = lean_array_get_size(v_parentResOrders_2502_);
v_as_2518_ = lean_array_push(v_parentResOrders_2502_, v_parentNames_2496_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2503_, v_as_2518_, v_j_2517_);
v___x_2520_ = lean_array_get_size(v___x_2519_);
v___x_2521_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2522_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2523_ = lean_nat_dec_lt(v___x_2503_, v___x_2520_);
if (v___x_2523_ == 0)
{
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___f_2501_);
v___y_2508_ = v___x_2521_;
goto v___jp_2507_;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_le(v___x_2520_, v___x_2520_);
if (v___x_2524_ == 0)
{
if (v___x_2523_ == 0)
{
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___f_2501_);
v___y_2508_ = v___x_2521_;
goto v___jp_2507_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2520_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2522_, v___f_2501_, v___x_2519_, v___x_2525_, v___x_2526_, v___x_2521_);
v___y_2508_ = v___x_2527_;
goto v___jp_2507_;
}
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2520_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2522_, v___f_2501_, v___x_2519_, v___x_2528_, v___x_2529_, v___x_2521_);
v___y_2508_ = v___x_2530_;
goto v___jp_2507_;
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v_resOrder_2511_; lean_object* v_defects_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2509_ = lean_unsigned_to_nat(1u);
v___x_2510_ = lean_mk_empty_array_with_capacity(v___x_2509_);
v_resOrder_2511_ = lean_array_push(v___x_2510_, v_structName_2499_);
v_defects_2512_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v_resOrder_2511_);
lean_ctor_set(v___x_2513_, 1, v_defects_2512_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2508_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_2497_, v___f_2506_, v___x_2514_);
v___x_2516_ = lean_apply_4(v_toBind_2498_, lean_box(0), lean_box(0), v___x_2515_, v___f_2500_);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v_toPure_2531_, lean_object* v___f_2532_, lean_object* v_relaxed_2533_, lean_object* v_parentNames_2534_, lean_object* v_inst_2535_, lean_object* v_toBind_2536_, lean_object* v_structName_2537_, lean_object* v___f_2538_, lean_object* v___f_2539_, lean_object* v_parentResOrders_2540_){
_start:
{
uint8_t v_relaxed_boxed_2541_; lean_object* v_res_2542_; 
v_relaxed_boxed_2541_ = lean_unbox(v_relaxed_2533_);
v_res_2542_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v_toPure_2531_, v___f_2532_, v_relaxed_boxed_2541_, v_parentNames_2534_, v_inst_2535_, v_toBind_2536_, v_structName_2537_, v___f_2538_, v___f_2539_, v_parentResOrders_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2543_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_array_get_size(v_x_2543_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_nat_dec_eq(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
uint8_t v___x_2547_; 
v___x_2547_ = 1;
return v___x_2547_;
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = 0;
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2549_){
_start:
{
uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_res_2550_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2549_);
lean_dec_ref(v_x_2549_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2552_, lean_object* v_x1_2553_, lean_object* v_x2_2554_){
_start:
{
lean_object* v___x_2555_; uint8_t v___x_2556_; 
lean_inc_ref(v_x2_2554_);
v___x_2555_ = lean_apply_1(v___f_2552_, v_x2_2554_);
v___x_2556_ = lean_unbox(v___x_2555_);
if (v___x_2556_ == 0)
{
lean_dec_ref(v_x2_2554_);
return v_x1_2553_;
}
else
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_array_push(v_x1_2553_, v_x2_2554_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2558_, lean_object* v_____s_2559_){
_start:
{
lean_object* v_snd_2560_; lean_object* v_fst_2561_; lean_object* v_snd_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
v_snd_2560_ = lean_ctor_get(v_____s_2559_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v_____s_2559_);
v_fst_2561_ = lean_ctor_get(v_snd_2560_, 0);
v_snd_2562_ = lean_ctor_get(v_snd_2560_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_snd_2560_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v_snd_2560_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_snd_2562_);
lean_inc(v_fst_2561_);
lean_dec(v_snd_2560_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_fst_2561_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_snd_2562_);
v___x_2567_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_apply_2(v_toPure_2558_, lean_box(0), v___x_2567_);
return v___x_2568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2571_, lean_object* v_____do__lift_2572_){
_start:
{
lean_object* v_resolutionOrder_2573_; lean_object* v___x_2574_; 
v_resolutionOrder_2573_ = lean_ctor_get(v_____do__lift_2572_, 0);
lean_inc_ref(v_resolutionOrder_2573_);
lean_dec_ref(v_____do__lift_2572_);
v___x_2574_ = lean_apply_2(v_toPure_2571_, lean_box(0), v_resolutionOrder_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_structName_2581_, lean_object* v_parentNames_2582_, uint8_t v_relaxed_2583_){
_start:
{
lean_object* v_toApplicative_2584_; lean_object* v_toBind_2585_; lean_object* v_toPure_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___f_2592_; size_t v_sz_2593_; size_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_toApplicative_2584_ = lean_ctor_get(v_inst_2579_, 0);
v_toBind_2585_ = lean_ctor_get(v_inst_2579_, 1);
lean_inc_n(v_toBind_2585_, 3);
v_toPure_2586_ = lean_ctor_get(v_toApplicative_2584_, 1);
v___f_2587_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc_n(v_toPure_2586_, 3);
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2588_, 0, v_toPure_2586_);
lean_inc_ref_n(v_inst_2579_, 2);
v___f_2589_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2589_, 0, v_inst_2579_);
lean_closure_set(v___f_2589_, 1, v_inst_2580_);
lean_closure_set(v___f_2589_, 2, v_toBind_2585_);
lean_closure_set(v___f_2589_, 3, v___f_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2590_, 0, v_toPure_2586_);
v___x_2591_ = lean_box(v_relaxed_2583_);
lean_inc_ref(v_parentNames_2582_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 10, 9);
lean_closure_set(v___f_2592_, 0, v_toPure_2586_);
lean_closure_set(v___f_2592_, 1, v___f_2587_);
lean_closure_set(v___f_2592_, 2, v___x_2591_);
lean_closure_set(v___f_2592_, 3, v_parentNames_2582_);
lean_closure_set(v___f_2592_, 4, v_inst_2579_);
lean_closure_set(v___f_2592_, 5, v_toBind_2585_);
lean_closure_set(v___f_2592_, 6, v_structName_2581_);
lean_closure_set(v___f_2592_, 7, v___f_2590_);
lean_closure_set(v___f_2592_, 8, v___f_2587_);
v_sz_2593_ = lean_array_size(v_parentNames_2582_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2579_, v___f_2589_, v_sz_2593_, v___x_2594_, v_parentNames_2582_);
v___x_2596_ = lean_apply_4(v_toBind_2585_, lean_box(0), lean_box(0), v___x_2595_, v___f_2592_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2597_, lean_object* v_toPure_2598_, lean_object* v___f_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_, uint8_t v_relaxed_2602_, lean_object* v_toBind_2603_, lean_object* v___f_2604_, lean_object* v_env_2605_){
_start:
{
lean_object* v___x_2606_; 
lean_inc_ref(v_env_2605_);
v___x_2606_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2605_, v_structName_2597_);
if (lean_obj_tag(v___x_2606_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_env_2605_);
lean_dec(v___f_2604_);
lean_dec(v_toBind_2603_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v___f_2599_);
lean_dec(v_structName_2597_);
v_val_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_val_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_apply_2(v_toPure_2598_, lean_box(0), v___x_2609_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; size_t v_sz_2613_; size_t v___x_2614_; lean_object* v_parentNames_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec(v___x_2606_);
lean_dec(v_toPure_2598_);
lean_inc(v_structName_2597_);
v___x_2611_ = l_Lean_getStructureParentInfo(v_env_2605_, v_structName_2597_);
v___x_2612_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2613_ = lean_array_size(v___x_2611_);
v___x_2614_ = ((size_t)0ULL);
v_parentNames_2615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2612_, v___f_2599_, v_sz_2613_, v___x_2614_, v___x_2611_);
v___x_2616_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2600_, v_inst_2601_, v_structName_2597_, v_parentNames_2615_, v_relaxed_2602_);
v___x_2617_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v___x_2616_, v___f_2604_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2618_, lean_object* v_toPure_2619_, lean_object* v___f_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_relaxed_2623_, lean_object* v_toBind_2624_, lean_object* v___f_2625_, lean_object* v_env_2626_){
_start:
{
uint8_t v_relaxed_boxed_2627_; lean_object* v_res_2628_; 
v_relaxed_boxed_2627_ = lean_unbox(v_relaxed_2623_);
v_res_2628_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2618_, v_toPure_2619_, v___f_2620_, v_inst_2621_, v_inst_2622_, v_relaxed_boxed_2627_, v_toBind_2624_, v___f_2625_, v_env_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_structName_2631_, uint8_t v_relaxed_2632_){
_start:
{
lean_object* v_toApplicative_2633_; lean_object* v_toBind_2634_; lean_object* v_getEnv_2635_; lean_object* v_toPure_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; 
v_toApplicative_2633_ = lean_ctor_get(v_inst_2629_, 0);
v_toBind_2634_ = lean_ctor_get(v_inst_2629_, 1);
lean_inc_n(v_toBind_2634_, 3);
v_getEnv_2635_ = lean_ctor_get(v_inst_2630_, 0);
lean_inc(v_getEnv_2635_);
v_toPure_2636_ = lean_ctor_get(v_toApplicative_2633_, 1);
lean_inc_n(v_toPure_2636_, 2);
v___f_2637_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2631_);
lean_inc_ref(v_inst_2630_);
v___f_2638_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2638_, 0, v_toPure_2636_);
lean_closure_set(v___f_2638_, 1, v_inst_2630_);
lean_closure_set(v___f_2638_, 2, v_structName_2631_);
lean_closure_set(v___f_2638_, 3, v_toBind_2634_);
v___x_2639_ = lean_box(v_relaxed_2632_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2640_, 0, v_structName_2631_);
lean_closure_set(v___f_2640_, 1, v_toPure_2636_);
lean_closure_set(v___f_2640_, 2, v___f_2637_);
lean_closure_set(v___f_2640_, 3, v_inst_2629_);
lean_closure_set(v___f_2640_, 4, v_inst_2630_);
lean_closure_set(v___f_2640_, 5, v___x_2639_);
lean_closure_set(v___f_2640_, 6, v_toBind_2634_);
lean_closure_set(v___f_2640_, 7, v___f_2638_);
v___x_2641_ = lean_apply_4(v_toBind_2634_, lean_box(0), lean_box(0), v_getEnv_2635_, v___f_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_toBind_2644_, lean_object* v___f_2645_, lean_object* v_parentName_2646_){
_start:
{
uint8_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = 1;
v___x_2648_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2642_, v_inst_2643_, v_parentName_2646_, v___x_2647_);
v___x_2649_ = lean_apply_4(v_toBind_2644_, lean_box(0), lean_box(0), v___x_2648_, v___f_2645_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_structName_2652_, lean_object* v_relaxed_2653_){
_start:
{
uint8_t v_relaxed_boxed_2654_; lean_object* v_res_2655_; 
v_relaxed_boxed_2654_ = lean_unbox(v_relaxed_2653_);
v_res_2655_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2650_, v_inst_2651_, v_structName_2652_, v_relaxed_boxed_2654_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_structName_2658_, lean_object* v_parentNames_2659_, lean_object* v_relaxed_2660_){
_start:
{
uint8_t v_relaxed_boxed_2661_; lean_object* v_res_2662_; 
v_relaxed_boxed_2661_ = lean_unbox(v_relaxed_2660_);
v_res_2662_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2656_, v_inst_2657_, v_structName_2658_, v_parentNames_2659_, v_relaxed_boxed_2661_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_structName_2666_, uint8_t v_relaxed_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2664_, v_inst_2665_, v_structName_2666_, v_relaxed_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_structName_2672_, lean_object* v_relaxed_2673_){
_start:
{
uint8_t v_relaxed_boxed_2674_; lean_object* v_res_2675_; 
v_relaxed_boxed_2674_ = lean_unbox(v_relaxed_2673_);
v_res_2675_ = l_Lean_computeStructureResolutionOrder(v_m_2669_, v_inst_2670_, v_inst_2671_, v_structName_2672_, v_relaxed_boxed_2674_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_structName_2679_, lean_object* v_parentNames_2680_, uint8_t v_relaxed_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2677_, v_inst_2678_, v_structName_2679_, v_parentNames_2680_, v_relaxed_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_structName_2686_, lean_object* v_parentNames_2687_, lean_object* v_relaxed_2688_){
_start:
{
uint8_t v_relaxed_boxed_2689_; lean_object* v_res_2690_; 
v_relaxed_boxed_2689_ = lean_unbox(v_relaxed_2688_);
v_res_2690_ = l_Lean_mergeStructureResolutionOrders(v_m_2683_, v_inst_2684_, v_inst_2685_, v_structName_2686_, v_parentNames_2687_, v_relaxed_boxed_2689_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2691_){
_start:
{
lean_object* v_resolutionOrder_2692_; 
v_resolutionOrder_2692_ = lean_ctor_get(v_x_2691_, 0);
lean_inc_ref(v_resolutionOrder_2692_);
return v_resolutionOrder_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2693_);
lean_dec_ref(v_x_2693_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_structName_2698_){
_start:
{
lean_object* v_toApplicative_2699_; lean_object* v_toFunctor_2700_; lean_object* v_map_2701_; lean_object* v___f_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_toApplicative_2699_ = lean_ctor_get(v_inst_2696_, 0);
v_toFunctor_2700_ = lean_ctor_get(v_toApplicative_2699_, 0);
v_map_2701_ = lean_ctor_get(v_toFunctor_2700_, 0);
lean_inc(v_map_2701_);
v___f_2702_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2703_ = 1;
v___x_2704_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2696_, v_inst_2697_, v_structName_2698_, v___x_2703_);
v___x_2705_ = lean_apply_4(v_map_2701_, lean_box(0), lean_box(0), v___f_2702_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_structName_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2707_, v_inst_2708_, v_structName_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2711_, lean_object* v_structName_2712_, lean_object* v_x_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Array_erase___redArg(v___x_2711_, v_x_2713_, v_structName_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_structName_2717_){
_start:
{
lean_object* v_toApplicative_2718_; lean_object* v_toFunctor_2719_; lean_object* v_map_2720_; lean_object* v___x_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_toApplicative_2718_ = lean_ctor_get(v_inst_2715_, 0);
v_toFunctor_2719_ = lean_ctor_get(v_toApplicative_2718_, 0);
v_map_2720_ = lean_ctor_get(v_toFunctor_2719_, 0);
lean_inc(v_map_2720_);
v___x_2721_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2717_);
v___f_2722_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2722_, 0, v___x_2721_);
lean_closure_set(v___f_2722_, 1, v_structName_2717_);
v___x_2723_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2715_, v_inst_2716_, v_structName_2717_);
v___x_2724_ = lean_apply_4(v_map_2720_, lean_box(0), lean_box(0), v___f_2722_, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_structName_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_getAllParentStructures___redArg(v_inst_2726_, v_inst_2727_, v_structName_2728_);
return v___x_2729_;
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
