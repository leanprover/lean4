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
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
size_t v_x_1688__boxed_590_; size_t v_x_1689__boxed_591_; lean_object* v_res_592_; 
v_x_1688__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_x_1689__boxed_591_ = lean_unbox_usize(v_x_587_);
lean_dec(v_x_587_);
v_res_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_585_, v_x_1688__boxed_590_, v_x_1689__boxed_591_, v_x_588_, v_x_589_);
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
size_t v_x_2089__boxed_738_; size_t v_x_2090__boxed_739_; lean_object* v_res_740_; 
v_x_2089__boxed_738_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_x_2090__boxed_739_ = lean_unbox_usize(v_x_735_);
lean_dec(v_x_735_);
v_res_740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_732_, v_x_733_, v_x_2089__boxed_738_, v_x_2090__boxed_739_, v_x_736_, v_x_737_);
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
lean_dec(v_snd_978_);
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
lean_object* v_es_1070_; lean_object* v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; lean_object* v_j_1075_; lean_object* v___x_1076_; 
v_es_1070_ = lean_ctor_get(v_x_1067_, 0);
v___x_1071_ = lean_box(2);
v___x_1072_ = ((size_t)5ULL);
v___x_1073_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1074_ = lean_usize_land(v_x_1068_, v___x_1073_);
v_j_1075_ = lean_usize_to_nat(v___x_1074_);
v___x_1076_ = lean_array_get_borrowed(v___x_1071_, v_es_1070_, v_j_1075_);
lean_dec(v_j_1075_);
switch(lean_obj_tag(v___x_1076_))
{
case 0:
{
lean_object* v_key_1077_; lean_object* v_val_1078_; uint8_t v___x_1079_; 
v_key_1077_ = lean_ctor_get(v___x_1076_, 0);
v_val_1078_ = lean_ctor_get(v___x_1076_, 1);
v___x_1079_ = lean_name_eq(v_x_1069_, v_key_1077_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_box(0);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; 
lean_inc(v_val_1078_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_val_1078_);
return v___x_1081_;
}
}
case 1:
{
lean_object* v_node_1082_; size_t v___x_1083_; 
v_node_1082_ = lean_ctor_get(v___x_1076_, 0);
v___x_1083_ = lean_usize_shift_right(v_x_1068_, v___x_1072_);
v_x_1067_ = v_node_1082_;
v_x_1068_ = v___x_1083_;
goto _start;
}
default: 
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_box(0);
return v___x_1085_;
}
}
}
else
{
lean_object* v_ks_1086_; lean_object* v_vs_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_ks_1086_ = lean_ctor_get(v_x_1067_, 0);
v_vs_1087_ = lean_ctor_get(v_x_1067_, 1);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1086_, v_vs_1087_, v___x_1088_, v_x_1069_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_395__boxed_1093_; lean_object* v_res_1094_; 
v_x_395__boxed_1093_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1094_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1090_, v_x_395__boxed_1093_, v_x_1092_);
lean_dec(v_x_1092_);
lean_dec_ref(v_x_1090_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
uint64_t v___y_1098_; 
if (lean_obj_tag(v_x_1096_) == 0)
{
uint64_t v___x_1101_; 
v___x_1101_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_1098_ = v___x_1101_;
goto v___jp_1097_;
}
else
{
uint64_t v_hash_1102_; 
v_hash_1102_ = lean_ctor_get_uint64(v_x_1096_, sizeof(void*)*2);
v___y_1098_ = v_hash_1102_;
goto v___jp_1097_;
}
v___jp_1097_:
{
size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_uint64_to_usize(v___y_1098_);
v___x_1100_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1095_, v___x_1099_, v_x_1096_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1103_, v_x_1104_);
lean_dec(v_x_1104_);
lean_dec_ref(v_x_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1106_, lean_object* v_structName_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1109_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1106_, v_structName_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; lean_object* v_toEnvExtension_1111_; lean_object* v_asyncMode_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v_snd_1115_; lean_object* v___x_1116_; 
v___x_1110_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1111_ = lean_ctor_get(v___x_1110_, 0);
v_asyncMode_1112_ = lean_ctor_get(v_toEnvExtension_1111_, 2);
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1108_, v___x_1110_, v_env_1106_, v_asyncMode_1112_, v___x_1113_);
v_snd_1115_ = lean_ctor_get(v___x_1114_, 1);
lean_inc(v_snd_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1115_, v_structName_1107_);
lean_dec(v_structName_1107_);
lean_dec(v_snd_1115_);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_val_1117_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1117_);
lean_dec_ref(v___x_1109_);
v___x_1118_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1119_ = 0;
v___x_1120_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1108_, v___x_1118_, v_env_1106_, v_val_1117_, v___x_1119_);
lean_dec(v_val_1117_);
lean_dec_ref(v_env_1106_);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_array_get_size(v___x_1120_);
v___x_1123_ = lean_nat_dec_lt(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1120_);
lean_dec(v_structName_1107_);
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_sub(v___x_1122_, v___x_1125_);
v___x_1127_ = lean_nat_dec_le(v___x_1121_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec(v___x_1126_);
lean_dec_ref(v___x_1120_);
lean_dec(v_structName_1107_);
v___x_1128_ = lean_box(0);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1130_, 0, v_structName_1107_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_ctor_set(v___x_1130_, 2, v___x_1129_);
lean_ctor_set(v___x_1130_, 3, v___x_1129_);
v___x_1131_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1120_, v___x_1130_, v___x_1121_, v___x_1126_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1120_);
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1133_, v_x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1136_, v_x_1137_, v_x_1138_);
lean_dec(v_x_1138_);
lean_dec_ref(v_x_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1140_, lean_object* v_k_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1140_, v_k_1141_, v_x_1142_, v_x_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1146_, lean_object* v_k_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1146_, v_k_1147_, v_x_1148_, v_x_1149_, v_x_1150_);
lean_dec_ref(v_k_1147_);
lean_dec_ref(v_as_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, size_t v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1153_, v_x_1154_, v_x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
size_t v_x_531__boxed_1161_; lean_object* v_res_1162_; 
v_x_531__boxed_1161_ = lean_unbox_usize(v_x_1159_);
lean_dec(v_x_1159_);
v_res_1162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1157_, v_x_1158_, v_x_531__boxed_1161_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec_ref(v_x_1158_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_heq_1166_, lean_object* v_i_1167_, lean_object* v_k_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1164_, v_vals_1165_, v_i_1167_, v_k_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1170_, lean_object* v_keys_1171_, lean_object* v_vals_1172_, lean_object* v_heq_1173_, lean_object* v_i_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1170_, v_keys_1171_, v_vals_1172_, v_heq_1173_, v_i_1174_, v_k_1175_);
lean_dec(v_k_1175_);
lean_dec_ref(v_vals_1172_);
lean_dec_ref(v_keys_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1179_ = lean_panic_fn_borrowed(v___x_1178_, v_msg_1177_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1184_ = lean_unsigned_to_nat(4u);
v___x_1185_ = lean_unsigned_to_nat(139u);
v___x_1186_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1187_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1188_ = l_mkPanicMessageWithDecl(v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_, v___x_1183_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1189_, lean_object* v_structName_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_getStructureInfo_x3f(v_env_1189_, v_structName_1190_);
if (lean_obj_tag(v___x_1191_) == 1)
{
lean_object* v_val_1192_; 
v_val_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1192_);
lean_dec_ref(v___x_1191_);
return v_val_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v___x_1191_);
v___x_1193_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1194_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1197_ = lean_panic_fn_borrowed(v___x_1196_, v_msg_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1200_ = lean_unsigned_to_nat(9u);
v___x_1201_ = lean_unsigned_to_nat(154u);
v___x_1202_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1203_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1204_ = l_mkPanicMessageWithDecl(v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1207_ = lean_unsigned_to_nat(11u);
v___x_1208_ = lean_unsigned_to_nat(153u);
v___x_1209_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1210_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1212_, lean_object* v_constName_1213_){
_start:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = 0;
lean_inc_ref(v_env_1212_);
v___x_1221_ = l_Lean_Environment_find_x3f(v_env_1212_, v_constName_1213_, v___x_1220_);
if (lean_obj_tag(v___x_1221_) == 1)
{
lean_object* v_val_1222_; 
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref(v___x_1221_);
if (lean_obj_tag(v_val_1222_) == 5)
{
lean_object* v_val_1223_; lean_object* v_ctors_1224_; 
v_val_1223_ = lean_ctor_get(v_val_1222_, 0);
lean_inc_ref(v_val_1223_);
lean_dec_ref(v_val_1222_);
v_ctors_1224_ = lean_ctor_get(v_val_1223_, 4);
lean_inc(v_ctors_1224_);
lean_dec_ref(v_val_1223_);
if (lean_obj_tag(v_ctors_1224_) == 1)
{
lean_object* v_tail_1225_; 
v_tail_1225_ = lean_ctor_get(v_ctors_1224_, 1);
if (lean_obj_tag(v_tail_1225_) == 0)
{
lean_object* v_head_1226_; lean_object* v___x_1227_; 
v_head_1226_ = lean_ctor_get(v_ctors_1224_, 0);
lean_inc(v_head_1226_);
lean_dec_ref(v_ctors_1224_);
v___x_1227_ = l_Lean_Environment_find_x3f(v_env_1212_, v_head_1226_, v___x_1220_);
if (lean_obj_tag(v___x_1227_) == 1)
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref(v___x_1227_);
if (lean_obj_tag(v_val_1228_) == 6)
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v_val_1228_, 0);
lean_inc_ref(v_val_1229_);
lean_dec_ref(v_val_1228_);
return v_val_1229_;
}
else
{
lean_dec(v_val_1228_);
goto v___jp_1217_;
}
}
else
{
lean_dec(v___x_1227_);
goto v___jp_1217_;
}
}
else
{
lean_dec_ref(v_ctors_1224_);
lean_dec_ref(v_env_1212_);
goto v___jp_1214_;
}
}
else
{
lean_dec(v_ctors_1224_);
lean_dec_ref(v_env_1212_);
goto v___jp_1214_;
}
}
else
{
lean_dec(v_val_1222_);
lean_dec_ref(v_env_1212_);
goto v___jp_1214_;
}
}
else
{
lean_dec(v___x_1221_);
lean_dec_ref(v_env_1212_);
goto v___jp_1214_;
}
v___jp_1214_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1216_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1215_);
return v___x_1216_;
}
v___jp_1217_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1219_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1218_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1230_, lean_object* v_structName_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v_fieldNames_1233_; 
v___x_1232_ = l_Lean_getStructureInfo(v_env_1230_, v_structName_1231_);
v_fieldNames_1233_ = lean_ctor_get(v___x_1232_, 1);
lean_inc_ref(v_fieldNames_1233_);
lean_dec_ref(v___x_1232_);
return v_fieldNames_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1234_, lean_object* v_structName_1235_, lean_object* v_fieldName_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_getStructureInfo_x3f(v_env_1234_, v_structName_1235_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; lean_object* v_fieldInfo_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref(v___x_1237_);
v_fieldInfo_1239_ = lean_ctor_get(v_val_1238_, 2);
lean_inc_ref(v_fieldInfo_1239_);
lean_dec(v_val_1238_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_array_get_size(v_fieldInfo_1239_);
v___x_1242_ = lean_nat_dec_lt(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec_ref(v_fieldInfo_1239_);
lean_dec(v_fieldName_1236_);
v___x_1243_ = lean_box(0);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_sub(v___x_1241_, v___x_1244_);
v___x_1246_ = lean_nat_dec_le(v___x_1240_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec(v___x_1245_);
lean_dec_ref(v_fieldInfo_1239_);
lean_dec(v_fieldName_1236_);
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_box(0);
v___x_1250_ = 0;
v___x_1251_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1251_, 0, v_fieldName_1236_);
lean_ctor_set(v___x_1251_, 1, v___x_1248_);
lean_ctor_set(v___x_1251_, 2, v___x_1249_);
lean_ctor_set(v___x_1251_, 3, v___x_1249_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*4, v___x_1250_);
v___x_1252_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1239_, v___x_1251_, v___x_1240_, v___x_1245_);
lean_dec_ref(v___x_1251_);
lean_dec_ref(v_fieldInfo_1239_);
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1253_; 
lean_dec(v___x_1237_);
lean_dec(v_fieldName_1236_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1254_, lean_object* v_structName_1255_, lean_object* v_fieldName_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_getFieldInfo_x3f(v_env_1254_, v_structName_1255_, v_fieldName_1256_);
if (lean_obj_tag(v___x_1257_) == 1)
{
lean_object* v_val_1258_; lean_object* v_subobject_x3f_1259_; 
v_val_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1258_);
lean_dec_ref(v___x_1257_);
v_subobject_x3f_1259_ = lean_ctor_get(v_val_1258_, 2);
lean_inc(v_subobject_x3f_1259_);
lean_dec(v_val_1258_);
return v_subobject_x3f_1259_;
}
else
{
lean_object* v___x_1260_; 
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1261_, lean_object* v_structName_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v_parentInfo_1264_; 
v___x_1263_ = l_Lean_getStructureInfo(v_env_1261_, v_structName_1262_);
v_parentInfo_1264_ = lean_ctor_get(v___x_1263_, 3);
lean_inc_ref(v_parentInfo_1264_);
lean_dec_ref(v___x_1263_);
return v_parentInfo_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1265_, lean_object* v_structName_1266_, lean_object* v_as_1267_, size_t v_i_1268_, size_t v_stop_1269_, lean_object* v_b_1270_){
_start:
{
lean_object* v___y_1272_; uint8_t v___x_1276_; 
v___x_1276_ = lean_usize_dec_eq(v_i_1268_, v_stop_1269_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_array_uget_borrowed(v_as_1267_, v_i_1268_);
lean_inc(v___x_1277_);
lean_inc(v_structName_1266_);
lean_inc_ref(v_env_1265_);
v___x_1278_ = l_Lean_isSubobjectField_x3f(v_env_1265_, v_structName_1266_, v___x_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
v___y_1272_ = v_b_1270_;
goto v___jp_1271_;
}
else
{
lean_object* v_val_1279_; lean_object* v___x_1280_; 
v_val_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = lean_array_push(v_b_1270_, v_val_1279_);
v___y_1272_ = v___x_1280_;
goto v___jp_1271_;
}
}
else
{
lean_dec(v_structName_1266_);
lean_dec_ref(v_env_1265_);
return v_b_1270_;
}
v___jp_1271_:
{
size_t v___x_1273_; size_t v___x_1274_; 
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1268_, v___x_1273_);
v_i_1268_ = v___x_1274_;
v_b_1270_ = v___y_1272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1281_, lean_object* v_structName_1282_, lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_stop_1285_, lean_object* v_b_1286_){
_start:
{
size_t v_i_boxed_1287_; size_t v_stop_boxed_1288_; lean_object* v_res_1289_; 
v_i_boxed_1287_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_stop_boxed_1288_ = lean_unbox_usize(v_stop_1285_);
lean_dec(v_stop_1285_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1281_, v_structName_1282_, v_as_1283_, v_i_boxed_1287_, v_stop_boxed_1288_, v_b_1286_);
lean_dec_ref(v_as_1283_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1290_, lean_object* v_structName_1291_, lean_object* v_as_1292_, lean_object* v_start_1293_, lean_object* v_stop_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1296_ = lean_nat_dec_lt(v_start_1293_, v_stop_1294_);
if (v___x_1296_ == 0)
{
lean_dec(v_structName_1291_);
lean_dec_ref(v_env_1290_);
return v___x_1295_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_array_get_size(v_as_1292_);
v___x_1298_ = lean_nat_dec_le(v_stop_1294_, v___x_1297_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_nat_dec_lt(v_start_1293_, v___x_1297_);
if (v___x_1299_ == 0)
{
lean_dec(v_structName_1291_);
lean_dec_ref(v_env_1290_);
return v___x_1295_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_usize_of_nat(v_start_1293_);
v___x_1301_ = lean_usize_of_nat(v___x_1297_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1290_, v_structName_1291_, v_as_1292_, v___x_1300_, v___x_1301_, v___x_1295_);
return v___x_1302_;
}
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_usize_of_nat(v_start_1293_);
v___x_1304_ = lean_usize_of_nat(v_stop_1294_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1290_, v_structName_1291_, v_as_1292_, v___x_1303_, v___x_1304_, v___x_1295_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1306_, lean_object* v_structName_1307_, lean_object* v_as_1308_, lean_object* v_start_1309_, lean_object* v_stop_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1306_, v_structName_1307_, v_as_1308_, v_start_1309_, v_stop_1310_);
lean_dec(v_stop_1310_);
lean_dec(v_start_1309_);
lean_dec_ref(v_as_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1312_, lean_object* v_structName_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_inc(v_structName_1313_);
lean_inc_ref(v_env_1312_);
v___x_1314_ = l_Lean_getStructureFields(v_env_1312_, v_structName_1313_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_array_get_size(v___x_1314_);
v___x_1317_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1312_, v_structName_1313_, v___x_1314_, v___x_1315_, v___x_1316_);
lean_dec_ref(v___x_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1318_, lean_object* v_as_1319_, size_t v_i_1320_, size_t v_stop_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_eq(v_i_1320_, v_stop_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_array_uget_borrowed(v_as_1319_, v_i_1320_);
v___x_1324_ = lean_name_eq(v_a_1318_, v___x_1323_);
if (v___x_1324_ == 0)
{
size_t v___x_1325_; size_t v___x_1326_; 
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1320_, v___x_1325_);
v_i_1320_ = v___x_1326_;
goto _start;
}
else
{
return v___x_1324_;
}
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = 0;
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1329_, lean_object* v_as_1330_, lean_object* v_i_1331_, lean_object* v_stop_1332_){
_start:
{
size_t v_i_boxed_1333_; size_t v_stop_boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_i_boxed_1333_ = lean_unbox_usize(v_i_1331_);
lean_dec(v_i_1331_);
v_stop_boxed_1334_ = lean_unbox_usize(v_stop_1332_);
lean_dec(v_stop_1332_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1329_, v_as_1330_, v_i_boxed_1333_, v_stop_boxed_1334_);
lean_dec_ref(v_as_1330_);
lean_dec(v_a_1329_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_array_get_size(v_as_1337_);
v___x_1341_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
return v___x_1341_;
}
else
{
if (v___x_1341_ == 0)
{
return v___x_1341_;
}
else
{
size_t v___x_1342_; size_t v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = lean_usize_of_nat(v___x_1340_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1338_, v_as_1337_, v___x_1342_, v___x_1343_);
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1345_, lean_object* v_a_1346_){
_start:
{
uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_res_1347_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_as_1345_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1352_, lean_object* v_structName_1353_, lean_object* v_fieldName_1354_){
_start:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
lean_inc(v_structName_1353_);
lean_inc_ref(v_env_1352_);
v___x_1355_ = l_Lean_getStructureFields(v_env_1352_, v_structName_1353_);
v___x_1356_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1355_, v_fieldName_1354_);
lean_dec_ref(v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v_fst_1363_; 
lean_inc_ref(v_env_1352_);
v___x_1357_ = l_Lean_getStructureSubobjects(v_env_1352_, v_structName_1353_);
v___x_1358_ = lean_box(0);
v___x_1359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1360_ = lean_array_size(v___x_1357_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1352_, v_fieldName_1354_, v___x_1357_, v_sz_1360_, v___x_1361_, v___x_1359_);
lean_dec_ref(v___x_1357_);
v_fst_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_fst_1363_);
lean_dec_ref(v___x_1362_);
if (lean_obj_tag(v_fst_1363_) == 0)
{
return v___x_1358_;
}
else
{
lean_object* v_val_1364_; 
v_val_1364_ = lean_ctor_get(v_fst_1363_, 0);
lean_inc(v_val_1364_);
lean_dec_ref(v_fst_1363_);
return v_val_1364_;
}
}
else
{
lean_object* v___x_1365_; 
lean_dec_ref(v_env_1352_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_structName_1353_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1366_, lean_object* v_fieldName_1367_, lean_object* v_as_1368_, size_t v_sz_1369_, size_t v_i_1370_, lean_object* v_b_1371_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_usize_dec_lt(v_i_1370_, v_sz_1369_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v_env_1366_);
lean_inc_ref(v_b_1371_);
return v_b_1371_;
}
else
{
lean_object* v___x_1373_; lean_object* v_a_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(0);
v_a_1374_ = lean_array_uget_borrowed(v_as_1368_, v_i_1370_);
lean_inc(v_a_1374_);
lean_inc_ref(v_env_1366_);
v___x_1375_ = l_Lean_findField_x3f(v_env_1366_, v_a_1374_, v_fieldName_1367_);
if (lean_obj_tag(v___x_1375_) == 1)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_env_1366_);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___x_1373_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; 
lean_dec(v___x_1375_);
v___x_1378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1370_, v___x_1379_);
v_i_1370_ = v___x_1380_;
v_b_1371_ = v___x_1378_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1382_, lean_object* v_fieldName_1383_, lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1382_, v_fieldName_1383_, v_as_1384_, v_sz_boxed_1388_, v_i_boxed_1389_, v_b_1387_);
lean_dec_ref(v_b_1387_);
lean_dec_ref(v_as_1384_);
lean_dec(v_fieldName_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1391_, lean_object* v_structName_1392_, lean_object* v_fieldName_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_findField_x3f(v_env_1391_, v_structName_1392_, v_fieldName_1393_);
lean_dec(v_fieldName_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1398_, lean_object* v_as_1399_, size_t v_sz_1400_, size_t v_i_1401_, lean_object* v_b_1402_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_usize_dec_lt(v_i_1401_, v_sz_1400_);
if (v___x_1403_ == 0)
{
lean_inc_ref(v_b_1402_);
return v_b_1402_;
}
else
{
lean_object* v_a_1404_; lean_object* v_projFn_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_a_1404_ = lean_array_uget_borrowed(v_as_1399_, v_i_1401_);
v_projFn_1405_ = lean_ctor_get(v_a_1404_, 1);
v___x_1406_ = lean_box(0);
v___x_1407_ = l_Lean_Name_isSuffixOf(v_projName_1398_, v_projFn_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; 
v___x_1408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1401_, v___x_1409_);
v_i_1401_ = v___x_1410_;
v_b_1402_ = v___x_1408_;
goto _start;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_inc(v_a_1404_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_a_1404_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1406_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1415_, lean_object* v_as_1416_, lean_object* v_sz_1417_, lean_object* v_i_1418_, lean_object* v_b_1419_){
_start:
{
size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1417_);
lean_dec(v_sz_1417_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1415_, v_as_1416_, v_sz_boxed_1420_, v_i_boxed_1421_, v_b_1419_);
lean_dec_ref(v_b_1419_);
lean_dec_ref(v_as_1416_);
lean_dec(v_projName_1415_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1423_, lean_object* v_projName_1424_, lean_object* v_structName_1425_, lean_object* v_a_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = l_Lean_NameSet_contains(v_a_1426_, v_structName_1425_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; lean_object* v_fst_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1473_; 
lean_inc(v_structName_1425_);
lean_inc_ref(v_env_1423_);
v___x_1428_ = l_Lean_getStructureParentInfo(v_env_1423_, v_structName_1425_);
v___x_1452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1453_ = lean_array_size(v___x_1428_);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1424_, v___x_1428_, v_sz_1453_, v___x_1454_, v___x_1452_);
v_fst_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v___x_1455_, 1);
lean_dec(v_unused_1474_);
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1473_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_fst_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1473_;
goto v_resetjp_1457_;
}
v___jp_1429_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v_fst_1436_; lean_object* v_fst_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1450_; 
v___x_1430_ = l_Lean_NameSet_insert(v_a_1426_, v_structName_1425_);
v___x_1431_ = lean_box(0);
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1433_ = lean_array_size(v___x_1428_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1423_, v_projName_1424_, v___x_1428_, v_sz_1433_, v___x_1434_, v___x_1432_, v___x_1430_);
lean_dec_ref(v___x_1428_);
v_fst_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_fst_1436_);
v_fst_1437_ = lean_ctor_get(v_fst_1436_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_fst_1436_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_fst_1436_, 1);
lean_dec(v_unused_1451_);
v___x_1439_ = v_fst_1436_;
v_isShared_1440_ = v_isSharedCheck_1450_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_fst_1437_);
lean_dec(v_fst_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1450_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
if (lean_obj_tag(v_fst_1437_) == 0)
{
lean_object* v_snd_1441_; lean_object* v___x_1443_; 
v_snd_1441_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_snd_1441_);
lean_dec_ref(v___x_1435_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_snd_1441_);
lean_ctor_set(v___x_1439_, 0, v___x_1431_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
lean_object* v_snd_1445_; lean_object* v_val_1446_; lean_object* v___x_1448_; 
v_snd_1445_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_snd_1445_);
lean_dec_ref(v___x_1435_);
v_val_1446_ = lean_ctor_get(v_fst_1437_, 0);
lean_inc(v_val_1446_);
lean_dec_ref(v_fst_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_snd_1445_);
lean_ctor_set(v___x_1439_, 0, v_val_1446_);
v___x_1448_ = v___x_1439_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1446_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1445_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
v_resetjp_1457_:
{
if (lean_obj_tag(v_fst_1456_) == 0)
{
lean_del_object(v___x_1458_);
goto v___jp_1429_;
}
else
{
lean_object* v_val_1460_; 
v_val_1460_ = lean_ctor_get(v_fst_1456_, 0);
lean_inc(v_val_1460_);
lean_dec_ref(v_fst_1456_);
if (lean_obj_tag(v_val_1460_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___x_1428_);
lean_dec(v_structName_1425_);
lean_dec_ref(v_env_1423_);
v_val_1461_ = lean_ctor_get(v_val_1460_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_val_1460_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1463_ = v_val_1460_;
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_val_1461_);
lean_dec(v_val_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_structName_1465_; lean_object* v___x_1467_; 
v_structName_1465_ = lean_ctor_get(v_val_1461_, 0);
lean_inc(v_structName_1465_);
lean_dec(v_val_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v_structName_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_structName_1465_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v_a_1426_);
lean_ctor_set(v___x_1458_, 0, v___x_1467_);
v___x_1469_ = v___x_1458_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1426_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_dec(v_val_1460_);
lean_del_object(v___x_1458_);
goto v___jp_1429_;
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec(v_structName_1425_);
lean_dec_ref(v_env_1423_);
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v_a_1426_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1477_, lean_object* v_projName_1478_, lean_object* v_as_1479_, size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_usize_dec_lt(v_i_1481_, v_sz_1480_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref(v_env_1477_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_b_1482_);
lean_ctor_set(v___x_1485_, 1, v___y_1483_);
return v___x_1485_;
}
else
{
lean_object* v_a_1486_; lean_object* v_structName_1487_; lean_object* v___x_1488_; lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_b_1482_);
v_a_1486_ = lean_array_uget_borrowed(v_as_1479_, v_i_1481_);
v_structName_1487_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_structName_1487_);
lean_inc_ref(v_env_1477_);
v___x_1488_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1477_, v_projName_1478_, v_structName_1487_, v___y_1483_);
v_fst_1489_ = lean_ctor_get(v___x_1488_, 0);
v_snd_1490_ = lean_ctor_get(v___x_1488_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1492_ = v___x_1488_;
v_isShared_1493_ = v_isSharedCheck_1504_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_snd_1490_);
lean_inc(v_fst_1489_);
lean_dec(v___x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1504_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(0);
if (lean_obj_tag(v_fst_1489_) == 1)
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec_ref(v_env_1477_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_fst_1489_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v___x_1494_);
lean_ctor_set(v___x_1492_, 0, v___x_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1494_);
v___x_1497_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_snd_1490_);
return v___x_1498_;
}
}
else
{
lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; 
lean_del_object(v___x_1492_);
lean_dec(v_fst_1489_);
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1481_, v___x_1501_);
v_i_1481_ = v___x_1502_;
v_b_1482_ = v___x_1500_;
v___y_1483_ = v_snd_1490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1505_, lean_object* v_projName_1506_, lean_object* v_as_1507_, lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1505_, v_projName_1506_, v_as_1507_, v_sz_boxed_1512_, v_i_boxed_1513_, v_b_1510_, v___y_1511_);
lean_dec_ref(v_as_1507_);
lean_dec(v_projName_1506_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1515_, lean_object* v_projName_1516_, lean_object* v_structName_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1515_, v_projName_1516_, v_structName_1517_, v_a_1518_);
lean_dec(v_projName_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1520_, lean_object* v_structName_1521_, lean_object* v_projName_1522_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_fst_1525_; 
v___x_1523_ = l_Lean_NameSet_empty;
v___x_1524_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1520_, v_projName_1522_, v_structName_1521_, v___x_1523_);
v_fst_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_fst_1525_);
lean_dec_ref(v___x_1524_);
return v_fst_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1526_, lean_object* v_structName_1527_, lean_object* v_projName_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_findParentProjStruct_x3f(v_env_1526_, v_structName_1527_, v_projName_1528_);
lean_dec(v_projName_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1535_ = l_Lean_Name_append(v_structCtorName_1533_, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1536_, lean_object* v_structName_1537_, uint8_t v_includeSubobjectFields_1538_, lean_object* v_as_1539_, size_t v_i_1540_, size_t v_stop_1541_, lean_object* v_b_1542_){
_start:
{
lean_object* v___y_1544_; uint8_t v___x_1548_; 
v___x_1548_ = lean_usize_dec_eq(v_i_1540_, v_stop_1541_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_array_uget_borrowed(v_as_1539_, v_i_1540_);
lean_inc(v___x_1549_);
lean_inc(v_structName_1537_);
lean_inc_ref(v_env_1536_);
v___x_1550_ = l_Lean_isSubobjectField_x3f(v_env_1536_, v_structName_1537_, v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_inc(v___x_1549_);
v___x_1551_ = lean_array_push(v_b_1542_, v___x_1549_);
v___y_1544_ = v___x_1551_;
goto v___jp_1543_;
}
else
{
if (v_includeSubobjectFields_1538_ == 0)
{
lean_object* v_val_1552_; lean_object* v___x_1553_; 
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref(v___x_1550_);
lean_inc_ref(v_env_1536_);
v___x_1553_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1536_, v_val_1552_, v_b_1542_, v_includeSubobjectFields_1538_);
v___y_1544_ = v___x_1553_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_val_1554_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v___x_1550_);
lean_inc(v___x_1549_);
v___x_1555_ = lean_array_push(v_b_1542_, v___x_1549_);
lean_inc_ref(v_env_1536_);
v___x_1556_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1536_, v_val_1554_, v___x_1555_, v_includeSubobjectFields_1538_);
v___y_1544_ = v___x_1556_;
goto v___jp_1543_;
}
}
}
else
{
lean_dec(v_structName_1537_);
lean_dec_ref(v_env_1536_);
return v_b_1542_;
}
v___jp_1543_:
{
size_t v___x_1545_; size_t v___x_1546_; 
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1540_, v___x_1545_);
v_i_1540_ = v___x_1546_;
v_b_1542_ = v___y_1544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1557_, lean_object* v_structName_1558_, lean_object* v_fullNames_1559_, uint8_t v_includeSubobjectFields_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
lean_inc(v_structName_1558_);
lean_inc_ref(v_env_1557_);
v___x_1561_ = l_Lean_getStructureFields(v_env_1557_, v_structName_1558_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = lean_array_get_size(v___x_1561_);
v___x_1564_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1561_);
lean_dec(v_structName_1558_);
lean_dec_ref(v_env_1557_);
return v_fullNames_1559_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_nat_dec_le(v___x_1563_, v___x_1563_);
if (v___x_1565_ == 0)
{
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1561_);
lean_dec(v_structName_1558_);
lean_dec_ref(v_env_1557_);
return v_fullNames_1559_;
}
else
{
size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = lean_usize_of_nat(v___x_1563_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1557_, v_structName_1558_, v_includeSubobjectFields_1560_, v___x_1561_, v___x_1566_, v___x_1567_, v_fullNames_1559_);
lean_dec_ref(v___x_1561_);
return v___x_1568_;
}
}
else
{
size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = lean_usize_of_nat(v___x_1563_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1557_, v_structName_1558_, v_includeSubobjectFields_1560_, v___x_1561_, v___x_1569_, v___x_1570_, v_fullNames_1559_);
lean_dec_ref(v___x_1561_);
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1572_, lean_object* v_structName_1573_, lean_object* v_fullNames_1574_, lean_object* v_includeSubobjectFields_1575_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1576_; lean_object* v_res_1577_; 
v_includeSubobjectFields_boxed_1576_ = lean_unbox(v_includeSubobjectFields_1575_);
v_res_1577_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1572_, v_structName_1573_, v_fullNames_1574_, v_includeSubobjectFields_boxed_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1578_, lean_object* v_structName_1579_, lean_object* v_includeSubobjectFields_1580_, lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_, lean_object* v_b_1584_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1585_; size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; lean_object* v_res_1588_; 
v_includeSubobjectFields_boxed_1585_ = lean_unbox(v_includeSubobjectFields_1580_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1578_, v_structName_1579_, v_includeSubobjectFields_boxed_1585_, v_as_1581_, v_i_boxed_1586_, v_stop_boxed_1587_, v_b_1584_);
lean_dec_ref(v_as_1581_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1589_, lean_object* v_structName_1590_, uint8_t v_includeSubobjectFields_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1593_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1589_, v_structName_1590_, v___x_1592_, v_includeSubobjectFields_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1594_, lean_object* v_structName_1595_, lean_object* v_includeSubobjectFields_1596_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1597_; lean_object* v_res_1598_; 
v_includeSubobjectFields_boxed_1597_ = lean_unbox(v_includeSubobjectFields_1596_);
v_res_1598_ = l_Lean_getStructureFieldsFlattened(v_env_1594_, v_structName_1595_, v_includeSubobjectFields_boxed_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1599_, lean_object* v_constName_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_getStructureInfo_x3f(v_env_1599_, v_constName_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = 0;
return v___x_1602_;
}
else
{
uint8_t v___x_1603_; 
lean_dec_ref(v___x_1601_);
v___x_1603_ = 1;
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1604_, lean_object* v_constName_1605_){
_start:
{
uint8_t v_res_1606_; lean_object* v_r_1607_; 
v_res_1606_ = l_Lean_isStructure(v_env_1604_, v_constName_1605_);
v_r_1607_ = lean_box(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1608_, lean_object* v_structName_1609_, lean_object* v_fieldName_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_getFieldInfo_x3f(v_env_1608_, v_structName_1609_, v_fieldName_1610_);
if (lean_obj_tag(v___x_1611_) == 1)
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_projFn_1616_; lean_object* v___x_1618_; 
v_projFn_1616_ = lean_ctor_get(v_val_1612_, 1);
lean_inc(v_projFn_1616_);
lean_dec(v_val_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v_projFn_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_projFn_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
else
{
lean_object* v___x_1621_; 
lean_dec(v___x_1611_);
v___x_1621_ = lean_box(0);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1622_, lean_object* v_structName_1623_, lean_object* v_fieldName_1624_){
_start:
{
lean_object* v___x_1625_; 
lean_inc_ref(v_env_1622_);
v___x_1625_ = l_Lean_getProjFnForField_x3f(v_env_1622_, v_structName_1623_, v_fieldName_1624_);
if (lean_obj_tag(v___x_1625_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1627_; 
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_n(v_val_1626_, 2);
lean_dec_ref(v___x_1625_);
v___x_1627_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1622_, v_val_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; 
lean_dec(v_val_1626_);
v___x_1628_ = lean_box(0);
return v___x_1628_;
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_val_1629_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v___x_1627_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_val_1629_);
lean_dec(v___x_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_val_1626_);
lean_ctor_set(v___x_1633_, 1, v_val_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v___x_1625_);
lean_dec_ref(v_env_1622_);
v___x_1638_ = lean_box(0);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1644_ = l_Lean_Name_append(v_projFn_1642_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1650_ = l_Lean_Name_append(v_projFn_1648_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1651_, lean_object* v_env_1652_, lean_object* v_structName_1653_, lean_object* v_fieldName_1654_){
_start:
{
lean_object* v___x_1655_; 
lean_inc(v_fieldName_1654_);
lean_inc(v_structName_1653_);
lean_inc_ref(v_env_1652_);
v___x_1655_ = l_Lean_getProjFnForField_x3f(v_env_1652_, v_structName_1653_, v_fieldName_1654_);
if (lean_obj_tag(v___x_1655_) == 1)
{
lean_object* v_val_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_fieldName_1654_);
lean_dec(v_structName_1653_);
v_val_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_val_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_defFn_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; 
v_defFn_1660_ = lean_apply_1(v_mkName_1651_, v_val_1656_);
v___x_1661_ = 1;
lean_inc(v_defFn_1660_);
v___x_1662_ = l_Lean_Environment_contains(v_env_1652_, v_defFn_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_dec(v_defFn_1660_);
lean_del_object(v___x_1658_);
v___x_1663_ = lean_box(0);
return v___x_1663_;
}
else
{
lean_object* v___x_1665_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_defFn_1660_);
v___x_1665_ = v___x_1658_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_defFn_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v_defFn_1669_; uint8_t v___x_1670_; uint8_t v___x_1671_; 
lean_dec(v___x_1655_);
v___x_1668_ = l_Lean_Name_append(v_structName_1653_, v_fieldName_1654_);
v_defFn_1669_ = lean_apply_1(v_mkName_1651_, v___x_1668_);
v___x_1670_ = 1;
lean_inc(v_defFn_1669_);
v___x_1671_ = l_Lean_Environment_contains(v_env_1652_, v_defFn_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
lean_dec(v_defFn_1669_);
v___x_1672_ = lean_box(0);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_defFn_1669_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1675_, lean_object* v_structName_1676_, lean_object* v_fieldName_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1679_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1678_, v_env_1675_, v_structName_1676_, v_fieldName_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1681_, lean_object* v_structName_1682_, lean_object* v_fieldName_1683_){
_start:
{
lean_object* v___x_1684_; 
lean_inc(v_fieldName_1683_);
lean_inc(v_structName_1682_);
lean_inc_ref(v_env_1681_);
v___x_1684_ = l_Lean_getDefaultFnForField_x3f(v_env_1681_, v_structName_1682_, v_fieldName_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1686_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1685_, v_env_1681_, v_structName_1682_, v_fieldName_1683_);
return v___x_1686_;
}
else
{
lean_dec(v_fieldName_1683_);
lean_dec(v_structName_1682_);
lean_dec_ref(v_env_1681_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1692_ = l_Lean_Name_append(v_projFn_1690_, v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1694_, lean_object* v_structName_1695_, lean_object* v_fieldName_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1698_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1697_, v_env_1694_, v_structName_1695_, v_fieldName_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1699_, lean_object* v_env_1700_, lean_object* v_baseStructName_1701_, lean_object* v_as_1702_, lean_object* v_i_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_snd_1706_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_array_get_size(v_as_1702_);
v___x_1711_ = lean_nat_dec_lt(v_i_1703_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_i_1703_);
lean_dec_ref(v_env_1700_);
lean_dec(v_path_1699_);
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___y_1704_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v_subobject_x3f_1715_; 
v___x_1714_ = lean_array_fget_borrowed(v_as_1702_, v_i_1703_);
v_subobject_x3f_1715_ = lean_ctor_get(v___x_1714_, 2);
if (lean_obj_tag(v_subobject_x3f_1715_) == 1)
{
lean_object* v_projFn_1716_; lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_fst_1720_; 
v_projFn_1716_ = lean_ctor_get(v___x_1714_, 1);
v_val_1717_ = lean_ctor_get(v_subobject_x3f_1715_, 0);
lean_inc(v_path_1699_);
lean_inc(v_projFn_1716_);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_projFn_1716_);
lean_ctor_set(v___x_1718_, 1, v_path_1699_);
lean_inc(v_val_1717_);
lean_inc_ref(v_env_1700_);
v___x_1719_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1700_, v_baseStructName_1701_, v_val_1717_, v___x_1718_, v___y_1704_);
v_fst_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_fst_1720_);
if (lean_obj_tag(v_fst_1720_) == 0)
{
lean_object* v_snd_1721_; 
v_snd_1721_ = lean_ctor_get(v___x_1719_, 1);
lean_inc(v_snd_1721_);
lean_dec_ref(v___x_1719_);
v_snd_1706_ = v_snd_1721_;
goto v___jp_1705_;
}
else
{
lean_dec_ref(v_fst_1720_);
lean_dec(v_i_1703_);
lean_dec_ref(v_env_1700_);
lean_dec(v_path_1699_);
return v___x_1719_;
}
}
else
{
v_snd_1706_ = v___y_1704_;
goto v___jp_1705_;
}
}
v___jp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_unsigned_to_nat(1u);
v___x_1708_ = lean_nat_add(v_i_1703_, v___x_1707_);
lean_dec(v_i_1703_);
v_i_1703_ = v___x_1708_;
v___y_1704_ = v_snd_1706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1722_, lean_object* v_baseStructName_1723_, lean_object* v_structName_1724_, lean_object* v_path_1725_, lean_object* v_a_1726_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_name_eq(v_baseStructName_1723_, v_structName_1724_);
if (v___x_1740_ == 0)
{
uint8_t v___x_1741_; 
v___x_1741_ = l_Lean_NameSet_contains(v_a_1726_, v_structName_1724_);
if (v___x_1741_ == 0)
{
goto v___jp_1727_;
}
else
{
if (v___x_1740_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v_path_1725_);
lean_dec(v_structName_1724_);
lean_dec_ref(v_env_1722_);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1726_);
return v___x_1743_;
}
else
{
goto v___jp_1727_;
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_structName_1724_);
lean_dec_ref(v_env_1722_);
v___x_1744_ = l_List_reverse___redArg(v_path_1725_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v_a_1726_);
return v___x_1746_;
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_inc(v_structName_1724_);
v___x_1728_ = l_Lean_NameSet_insert(v_a_1726_, v_structName_1724_);
lean_inc_ref(v_env_1722_);
v___x_1729_ = l_Lean_getStructureInfo_x3f(v_env_1722_, v_structName_1724_);
if (lean_obj_tag(v___x_1729_) == 1)
{
lean_object* v_val_1730_; lean_object* v_fieldInfo_1731_; lean_object* v_parentInfo_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_fst_1735_; 
v_val_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_val_1730_);
lean_dec_ref(v___x_1729_);
v_fieldInfo_1731_ = lean_ctor_get(v_val_1730_, 2);
lean_inc_ref(v_fieldInfo_1731_);
v_parentInfo_1732_ = lean_ctor_get(v_val_1730_, 3);
lean_inc_ref(v_parentInfo_1732_);
lean_dec(v_val_1730_);
v___x_1733_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1722_);
lean_inc(v_path_1725_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1725_, v_env_1722_, v_baseStructName_1723_, v_fieldInfo_1731_, v___x_1733_, v___x_1728_);
lean_dec_ref(v_fieldInfo_1731_);
v_fst_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_fst_1735_);
if (lean_obj_tag(v_fst_1735_) == 0)
{
lean_object* v_snd_1736_; lean_object* v___x_1737_; 
v_snd_1736_ = lean_ctor_get(v___x_1734_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v___x_1734_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1725_, v_env_1722_, v_baseStructName_1723_, v_parentInfo_1732_, v___x_1733_, v_snd_1736_);
lean_dec_ref(v_parentInfo_1732_);
return v___x_1737_;
}
else
{
lean_dec_ref(v_fst_1735_);
lean_dec_ref(v_parentInfo_1732_);
lean_dec(v_path_1725_);
lean_dec_ref(v_env_1722_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1729_);
lean_dec(v_path_1725_);
lean_dec_ref(v_env_1722_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1728_);
return v___x_1739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1747_, lean_object* v_env_1748_, lean_object* v_baseStructName_1749_, lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_as_1750_);
v___x_1754_ = lean_nat_dec_lt(v_i_1751_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_i_1751_);
lean_dec_ref(v_env_1748_);
lean_dec(v_path_1747_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___y_1752_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v_structName_1758_; lean_object* v_projFn_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_fst_1762_; 
v___x_1757_ = lean_array_fget_borrowed(v_as_1750_, v_i_1751_);
v_structName_1758_ = lean_ctor_get(v___x_1757_, 0);
v_projFn_1759_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_path_1747_);
lean_inc(v_projFn_1759_);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_projFn_1759_);
lean_ctor_set(v___x_1760_, 1, v_path_1747_);
lean_inc(v_structName_1758_);
lean_inc_ref(v_env_1748_);
v___x_1761_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1748_, v_baseStructName_1749_, v_structName_1758_, v___x_1760_, v___y_1752_);
v_fst_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_fst_1762_);
if (lean_obj_tag(v_fst_1762_) == 0)
{
lean_object* v_snd_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_snd_1763_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_snd_1763_);
lean_dec_ref(v___x_1761_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_i_1751_, v___x_1764_);
lean_dec(v_i_1751_);
v_i_1751_ = v___x_1765_;
v___y_1752_ = v_snd_1763_;
goto _start;
}
else
{
lean_dec_ref(v_fst_1762_);
lean_dec(v_i_1751_);
lean_dec_ref(v_env_1748_);
lean_dec(v_path_1747_);
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1767_, lean_object* v_env_1768_, lean_object* v_baseStructName_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1767_, v_env_1768_, v_baseStructName_1769_, v_as_1770_, v_i_1771_, v___y_1772_);
lean_dec_ref(v_as_1770_);
lean_dec(v_baseStructName_1769_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1774_, lean_object* v_env_1775_, lean_object* v_baseStructName_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1774_, v_env_1775_, v_baseStructName_1776_, v_as_1777_, v_i_1778_, v___y_1779_);
lean_dec_ref(v_as_1777_);
lean_dec(v_baseStructName_1776_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1781_, lean_object* v_baseStructName_1782_, lean_object* v_structName_1783_, lean_object* v_path_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1781_, v_baseStructName_1782_, v_structName_1783_, v_path_1784_, v_a_1785_);
lean_dec(v_baseStructName_1782_);
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
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1794_, lean_object* v_baseStructName_1795_, lean_object* v_structName_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_getPathToBaseStructure_x3f(v_env_1794_, v_baseStructName_1795_, v_structName_1796_);
lean_dec(v_baseStructName_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1798_, lean_object* v_constName_1799_){
_start:
{
uint8_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = 0;
v___x_1801_ = l_Lean_Environment_find_x3f(v_env_1798_, v_constName_1799_, v___x_1800_);
if (lean_obj_tag(v___x_1801_) == 1)
{
lean_object* v_val_1802_; 
v_val_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_val_1802_);
lean_dec_ref(v___x_1801_);
if (lean_obj_tag(v_val_1802_) == 5)
{
lean_object* v_val_1803_; lean_object* v_numIndices_1804_; lean_object* v_ctors_1805_; uint8_t v_isRec_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_val_1803_ = lean_ctor_get(v_val_1802_, 0);
lean_inc_ref(v_val_1803_);
lean_dec_ref(v_val_1802_);
v_numIndices_1804_ = lean_ctor_get(v_val_1803_, 2);
lean_inc(v_numIndices_1804_);
v_ctors_1805_ = lean_ctor_get(v_val_1803_, 4);
lean_inc(v_ctors_1805_);
v_isRec_1806_ = lean_ctor_get_uint8(v_val_1803_, sizeof(void*)*6);
lean_dec_ref(v_val_1803_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v_numIndices_1804_, v___x_1807_);
lean_dec(v_numIndices_1804_);
if (v___x_1808_ == 0)
{
lean_dec(v_ctors_1805_);
return v___x_1800_;
}
else
{
if (lean_obj_tag(v_ctors_1805_) == 1)
{
lean_object* v_tail_1809_; 
v_tail_1809_ = lean_ctor_get(v_ctors_1805_, 1);
lean_inc(v_tail_1809_);
lean_dec_ref(v_ctors_1805_);
if (lean_obj_tag(v_tail_1809_) == 0)
{
if (v_isRec_1806_ == 0)
{
return v___x_1808_;
}
else
{
return v___x_1800_;
}
}
else
{
lean_dec(v_tail_1809_);
return v___x_1800_;
}
}
else
{
lean_dec(v_ctors_1805_);
return v___x_1800_;
}
}
}
else
{
lean_dec(v_val_1802_);
return v___x_1800_;
}
}
else
{
lean_dec(v___x_1801_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1810_, lean_object* v_constName_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Lean_isNonRecStructure(v_env_1810_, v_constName_1811_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_panic_fn_borrowed(v___x_1815_, v_msg_1814_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1818_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1819_ = lean_unsigned_to_nat(11u);
v___x_1820_ = lean_unsigned_to_nat(374u);
v___x_1821_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1822_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1823_ = l_mkPanicMessageWithDecl(v___x_1822_, v___x_1821_, v___x_1820_, v___x_1819_, v___x_1818_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1824_, lean_object* v_constName_1825_){
_start:
{
uint8_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = 0;
lean_inc_ref(v_env_1824_);
v___x_1830_ = l_Lean_Environment_find_x3f(v_env_1824_, v_constName_1825_, v___x_1829_);
if (lean_obj_tag(v___x_1830_) == 1)
{
lean_object* v_val_1831_; 
v_val_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_val_1831_);
lean_dec_ref(v___x_1830_);
if (lean_obj_tag(v_val_1831_) == 5)
{
lean_object* v_val_1832_; lean_object* v_numIndices_1833_; lean_object* v_ctors_1834_; uint8_t v_isRec_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_val_1832_ = lean_ctor_get(v_val_1831_, 0);
lean_inc_ref(v_val_1832_);
lean_dec_ref(v_val_1831_);
v_numIndices_1833_ = lean_ctor_get(v_val_1832_, 2);
lean_inc(v_numIndices_1833_);
v_ctors_1834_ = lean_ctor_get(v_val_1832_, 4);
lean_inc(v_ctors_1834_);
v_isRec_1835_ = lean_ctor_get_uint8(v_val_1832_, sizeof(void*)*6);
lean_dec_ref(v_val_1832_);
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v_numIndices_1833_, v___x_1836_);
lean_dec(v_numIndices_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec(v_ctors_1834_);
lean_dec_ref(v_env_1824_);
v___x_1838_ = lean_box(0);
return v___x_1838_;
}
else
{
if (lean_obj_tag(v_ctors_1834_) == 1)
{
lean_object* v_tail_1839_; 
v_tail_1839_ = lean_ctor_get(v_ctors_1834_, 1);
if (lean_obj_tag(v_tail_1839_) == 0)
{
if (v_isRec_1835_ == 0)
{
lean_object* v_head_1840_; lean_object* v___x_1841_; 
v_head_1840_ = lean_ctor_get(v_ctors_1834_, 0);
lean_inc(v_head_1840_);
lean_dec_ref(v_ctors_1834_);
v___x_1841_ = l_Lean_Environment_find_x3f(v_env_1824_, v_head_1840_, v_isRec_1835_);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_val_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
if (lean_obj_tag(v_val_1842_) == 6)
{
lean_object* v_val_1846_; lean_object* v___x_1848_; 
v_val_1846_ = lean_ctor_get(v_val_1842_, 0);
lean_inc_ref(v_val_1846_);
lean_dec_ref(v_val_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_val_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_val_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_del_object(v___x_1844_);
lean_dec(v_val_1842_);
goto v___jp_1826_;
}
}
}
else
{
lean_dec(v___x_1841_);
goto v___jp_1826_;
}
}
else
{
lean_object* v___x_1851_; 
lean_dec_ref(v_ctors_1834_);
lean_dec_ref(v_env_1824_);
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
}
else
{
lean_object* v___x_1852_; 
lean_dec_ref(v_ctors_1834_);
lean_dec_ref(v_env_1824_);
v___x_1852_ = lean_box(0);
return v___x_1852_;
}
}
else
{
lean_object* v___x_1853_; 
lean_dec(v_ctors_1834_);
lean_dec_ref(v_env_1824_);
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
}
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_val_1831_);
lean_dec_ref(v_env_1824_);
v___x_1854_ = lean_box(0);
return v___x_1854_;
}
}
else
{
lean_object* v___x_1855_; 
lean_dec(v___x_1830_);
lean_dec_ref(v_env_1824_);
v___x_1855_ = lean_box(0);
return v___x_1855_;
}
v___jp_1826_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1828_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1827_);
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1856_, lean_object* v_constName_1857_){
_start:
{
uint8_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = 0;
lean_inc_ref(v_env_1856_);
v___x_1859_ = l_Lean_Environment_find_x3f(v_env_1856_, v_constName_1857_, v___x_1858_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; 
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1860_);
lean_dec_ref(v___x_1859_);
if (lean_obj_tag(v_val_1860_) == 5)
{
lean_object* v_val_1861_; lean_object* v_numIndices_1862_; lean_object* v_ctors_1863_; uint8_t v_isRec_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_val_1861_ = lean_ctor_get(v_val_1860_, 0);
lean_inc_ref(v_val_1861_);
lean_dec_ref(v_val_1860_);
v_numIndices_1862_ = lean_ctor_get(v_val_1861_, 2);
lean_inc(v_numIndices_1862_);
v_ctors_1863_ = lean_ctor_get(v_val_1861_, 4);
lean_inc(v_ctors_1863_);
v_isRec_1864_ = lean_ctor_get_uint8(v_val_1861_, sizeof(void*)*6);
lean_dec_ref(v_val_1861_);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_nat_dec_eq(v_numIndices_1862_, v___x_1865_);
lean_dec(v_numIndices_1862_);
if (v___x_1866_ == 0)
{
lean_dec(v_ctors_1863_);
lean_dec_ref(v_env_1856_);
return v___x_1865_;
}
else
{
if (lean_obj_tag(v_ctors_1863_) == 1)
{
lean_object* v_tail_1867_; 
v_tail_1867_ = lean_ctor_get(v_ctors_1863_, 1);
if (lean_obj_tag(v_tail_1867_) == 0)
{
if (v_isRec_1864_ == 0)
{
lean_object* v_head_1868_; lean_object* v___x_1869_; 
v_head_1868_ = lean_ctor_get(v_ctors_1863_, 0);
lean_inc(v_head_1868_);
lean_dec_ref(v_ctors_1863_);
v___x_1869_ = l_Lean_Environment_find_x3f(v_env_1856_, v_head_1868_, v_isRec_1864_);
if (lean_obj_tag(v___x_1869_) == 1)
{
lean_object* v_val_1870_; 
v_val_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v___x_1869_);
if (lean_obj_tag(v_val_1870_) == 6)
{
lean_object* v_val_1871_; lean_object* v_numFields_1872_; 
v_val_1871_ = lean_ctor_get(v_val_1870_, 0);
lean_inc_ref(v_val_1871_);
lean_dec_ref(v_val_1870_);
v_numFields_1872_ = lean_ctor_get(v_val_1871_, 4);
lean_inc(v_numFields_1872_);
lean_dec_ref(v_val_1871_);
return v_numFields_1872_;
}
else
{
lean_dec(v_val_1870_);
return v___x_1865_;
}
}
else
{
lean_dec(v___x_1869_);
return v___x_1865_;
}
}
else
{
lean_dec_ref(v_ctors_1863_);
lean_dec_ref(v_env_1856_);
return v___x_1865_;
}
}
else
{
lean_dec_ref(v_ctors_1863_);
lean_dec_ref(v_env_1856_);
return v___x_1865_;
}
}
else
{
lean_dec(v_ctors_1863_);
lean_dec_ref(v_env_1856_);
return v___x_1865_;
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_val_1860_);
lean_dec_ref(v_env_1856_);
v___x_1873_ = lean_unsigned_to_nat(0u);
return v___x_1873_;
}
}
else
{
lean_object* v___x_1874_; 
lean_dec(v___x_1859_);
lean_dec_ref(v_env_1856_);
v___x_1874_ = lean_unsigned_to_nat(0u);
return v___x_1874_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_1883_);
return v_res_1885_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___f_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_1887_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1887_, 0, v___x_1886_);
return v___f_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___f_1889_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_box(1);
v___x_1892_ = l_Lean_registerEnvExtension___redArg(v___f_1889_, v___x_1890_, v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_1895_, lean_object* v_structName_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v_asyncMode_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1897_ = l_Lean_structureResolutionExt;
v_asyncMode_1898_ = lean_ctor_get(v___x_1897_, 2);
v___x_1899_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_1900_ = lean_box(0);
v___x_1901_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1899_, v___x_1897_, v_env_1895_, v_asyncMode_1898_, v___x_1900_);
v___x_1902_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_1901_, v_structName_1896_);
lean_dec(v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_1903_, lean_object* v_structName_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_1903_, v_structName_1904_);
lean_dec(v_structName_1904_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_1906_, lean_object* v___x_1907_, lean_object* v_structName_1908_, lean_object* v_resolutionOrder_1909_, lean_object* v_s_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1906_, v___x_1907_, v_s_1910_, v_structName_1908_, v_resolutionOrder_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_1912_, lean_object* v_env_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v_asyncMode_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = l_Lean_structureResolutionExt;
v_asyncMode_1915_ = lean_ctor_get(v___x_1914_, 2);
v___x_1916_ = lean_box(0);
v___x_1917_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1914_, v_env_1913_, v___f_1912_, v_asyncMode_1915_, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_1918_, lean_object* v_structName_1919_, lean_object* v_resolutionOrder_1920_){
_start:
{
lean_object* v_modifyEnv_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; 
v_modifyEnv_1921_ = lean_ctor_get(v_inst_1918_, 1);
lean_inc(v_modifyEnv_1921_);
lean_dec_ref(v_inst_1918_);
v___x_1922_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1923_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_1924_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1924_, 0, v___x_1922_);
lean_closure_set(v___f_1924_, 1, v___x_1923_);
lean_closure_set(v___f_1924_, 2, v_structName_1919_);
lean_closure_set(v___f_1924_, 3, v_resolutionOrder_1920_);
v___f_1925_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1925_, 0, v___f_1924_);
v___x_1926_ = lean_apply_1(v_modifyEnv_1921_, v___f_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_1927_, lean_object* v_inst_1928_, lean_object* v_structName_1929_, lean_object* v_resolutionOrder_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_1928_, v_structName_1929_, v_resolutionOrder_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_1949_, lean_object* v_resOrders_1950_, lean_object* v___x_1951_, lean_object* v_toPure_1952_, lean_object* v_____s_1953_){
_start:
{
lean_object* v_fst_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1969_; 
v_fst_1954_ = lean_ctor_get(v_____s_1953_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_____s_1953_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v_____s_1953_, 1);
lean_dec(v_unused_1970_);
v___x_1956_ = v_____s_1953_;
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_fst_1954_);
lean_dec(v_____s_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
if (lean_obj_tag(v_fst_1954_) == 0)
{
uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1958_ = 0;
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_array_get_borrowed(v___x_1949_, v_resOrders_1950_, v___x_1959_);
v___x_1961_ = lean_array_get_borrowed(v___x_1951_, v___x_1960_, v___x_1959_);
v___x_1962_ = lean_box(v___x_1958_);
lean_inc(v___x_1961_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1961_);
lean_ctor_set(v___x_1956_, 0, v___x_1962_);
v___x_1964_ = v___x_1956_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1961_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_apply_2(v_toPure_1952_, lean_box(0), v___x_1964_);
return v___x_1965_;
}
}
else
{
lean_object* v_val_1967_; lean_object* v___x_1968_; 
lean_del_object(v___x_1956_);
v_val_1967_ = lean_ctor_get(v_fst_1954_, 0);
lean_inc(v_val_1967_);
lean_dec_ref(v_fst_1954_);
v___x_1968_ = lean_apply_2(v_toPure_1952_, lean_box(0), v_val_1967_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_1971_, lean_object* v_resOrders_1972_, lean_object* v___x_1973_, lean_object* v_toPure_1974_, lean_object* v_____s_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_1971_, v_resOrders_1972_, v___x_1973_, v_toPure_1974_, v_____s_1975_);
lean_dec(v___x_1973_);
lean_dec_ref(v_resOrders_1972_);
lean_dec_ref(v___x_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_1977_, lean_object* v_____do__lift_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_apply_2(v_toPure_1977_, lean_box(0), v_____do__lift_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_1980_, lean_object* v_toPure_1981_, lean_object* v___x_1982_, lean_object* v_____s_1983_){
_start:
{
lean_object* v_fst_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2002_; 
v_fst_1984_ = lean_ctor_get(v_____s_1983_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_____s_1983_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v_____s_1983_, 1);
lean_dec(v_unused_2003_);
v___x_1986_ = v_____s_1983_;
v_isShared_1987_ = v_isSharedCheck_2002_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_fst_1984_);
lean_dec(v_____s_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2002_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
if (lean_obj_tag(v_fst_1984_) == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1980_);
v___x_1989_ = lean_apply_2(v_toPure_1981_, lean_box(0), v___x_1988_);
return v___x_1989_;
}
else
{
lean_object* v___x_1991_; 
lean_dec_ref(v___x_1980_);
lean_inc_ref(v_fst_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___x_1982_);
v___x_1991_ = v___x_1986_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_fst_1984_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1982_);
v___x_1991_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1999_; 
v_isSharedCheck_1999_ = !lean_is_exclusive(v_fst_1984_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v_fst_1984_, 0);
lean_dec(v_unused_2000_);
v___x_1993_ = v_fst_1984_;
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
else
{
lean_dec(v_fst_1984_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1991_);
v___x_1996_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_apply_2(v_toPure_1981_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2004_, lean_object* v_next_2005_, lean_object* v_G_2006_, lean_object* v_____do__lift_2007_){
_start:
{
if (lean_obj_tag(v_____do__lift_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
lean_dec(v_G_2006_);
v_a_2008_ = lean_ctor_get(v_____do__lift_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v_____do__lift_2007_);
v___x_2009_ = lean_apply_2(v_toPure_2004_, lean_box(0), v_a_2008_);
return v___x_2009_;
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_toPure_2004_);
v_a_2010_ = lean_ctor_get(v_____do__lift_2007_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v_____do__lift_2007_);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_nat_add(v_next_2005_, v___x_2011_);
v___x_2013_ = lean_apply_4(v_G_2006_, v___x_2012_, v_a_2010_, lean_box(0), lean_box(0));
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2014_, lean_object* v_next_2015_, lean_object* v_G_2016_, lean_object* v_____do__lift_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2014_, v_next_2015_, v_G_2016_, v_____do__lift_2017_);
lean_dec(v_next_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2019_, lean_object* v_v_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_name_eq(v_v_2020_, v___x_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2022_, lean_object* v_v_2023_){
_start:
{
uint8_t v_res_2024_; lean_object* v_r_2025_; 
v_res_2024_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2022_, v_v_2023_);
lean_dec(v_v_2023_);
lean_dec(v___x_2022_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2045_, lean_object* v___f_2046_, lean_object* v_resOrder_2047_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_array_2052_; lean_object* v_start_2053_; lean_object* v_stop_2054_; uint8_t v___x_2055_; lean_object* v___y_2057_; 
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = lean_array_get_size(v_resOrder_2047_);
v___x_2050_ = l_Array_toSubarray___redArg(v_resOrder_2047_, v___x_2048_, v___x_2049_);
v___x_2051_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2052_ = lean_ctor_get(v___x_2050_, 0);
lean_inc_ref(v_array_2052_);
v_start_2053_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_start_2053_);
v_stop_2054_ = lean_ctor_get(v___x_2050_, 2);
lean_inc(v_stop_2054_);
lean_dec_ref(v___x_2050_);
v___x_2055_ = lean_nat_dec_lt(v_start_2053_, v_stop_2054_);
if (v___x_2055_ == 0)
{
lean_dec(v_stop_2054_);
lean_dec(v_start_2053_);
lean_dec_ref(v_array_2052_);
lean_dec_ref(v___f_2046_);
return v___x_2045_;
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_array_get_size(v_array_2052_);
v___x_2065_ = lean_nat_dec_le(v_stop_2054_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec(v_stop_2054_);
v___y_2057_ = v___x_2064_;
goto v___jp_2056_;
}
else
{
v___y_2057_ = v_stop_2054_;
goto v___jp_2056_;
}
}
v___jp_2056_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_nat_dec_lt(v_start_2053_, v___y_2057_);
if (v___x_2058_ == 0)
{
lean_dec(v___y_2057_);
lean_dec(v_start_2053_);
lean_dec_ref(v_array_2052_);
lean_dec_ref(v___f_2046_);
return v___x_2055_;
}
else
{
size_t v___x_2059_; size_t v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2059_ = lean_usize_of_nat(v_start_2053_);
lean_dec(v_start_2053_);
v___x_2060_ = lean_usize_of_nat(v___y_2057_);
lean_dec(v___y_2057_);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2051_, v___f_2046_, v_array_2052_, v___x_2059_, v___x_2060_);
v___x_2062_ = lean_unbox(v___x_2061_);
lean_dec(v___x_2061_);
if (v___x_2062_ == 0)
{
return v___x_2058_;
}
else
{
uint8_t v___x_2063_; 
v___x_2063_ = 0;
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2066_, lean_object* v___f_2067_, lean_object* v_resOrder_2068_){
_start:
{
uint8_t v___x_1715__boxed_2069_; uint8_t v_res_2070_; lean_object* v_r_2071_; 
v___x_1715__boxed_2069_ = lean_unbox(v___x_2066_);
v_res_2070_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2069_, v___f_2067_, v_resOrder_2068_);
v_r_2071_ = lean_box(v_res_2070_);
return v_r_2071_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2072_, uint8_t v___y_2073_, lean_object* v_v_2074_){
_start:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_apply_1(v___f_2072_, v_v_2074_);
v___x_2076_ = lean_unbox(v___x_2075_);
if (v___x_2076_ == 0)
{
return v___y_2073_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = 0;
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2078_, lean_object* v___y_2079_, lean_object* v_v_2080_){
_start:
{
uint8_t v___y_1771__boxed_2081_; uint8_t v_res_2082_; lean_object* v_r_2083_; 
v___y_1771__boxed_2081_ = lean_unbox(v___y_2079_);
v_res_2082_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2078_, v___y_1771__boxed_2081_, v_v_2080_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2084_, uint8_t v___x_2085_, lean_object* v_v_2086_){
_start:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_apply_1(v___f_2084_, v_v_2086_);
v___x_2088_ = lean_unbox(v___x_2087_);
if (v___x_2088_ == 0)
{
return v___x_2085_;
}
else
{
uint8_t v___x_2089_; 
v___x_2089_ = 0;
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2090_, lean_object* v___x_2091_, lean_object* v_v_2092_){
_start:
{
uint8_t v___x_1783__boxed_2093_; uint8_t v_res_2094_; lean_object* v_r_2095_; 
v___x_1783__boxed_2093_ = lean_unbox(v___x_2091_);
v_res_2094_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2090_, v___x_1783__boxed_2093_, v_v_2092_);
v_r_2095_ = lean_box(v_res_2094_);
return v_r_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2096_, lean_object* v_toPure_2097_, lean_object* v___x_2098_, lean_object* v_resOrders_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_toBind_2102_, lean_object* v___f_2103_, lean_object* v___x_2104_, lean_object* v_next_2105_, lean_object* v___x_2106_, lean_object* v_next_2107_, lean_object* v_acc_2108_, lean_object* v_h_2109_, lean_object* v_G_2110_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_nat_dec_lt(v_next_2107_, v___x_2096_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v_G_2110_);
lean_dec(v_next_2107_);
lean_dec_ref(v___x_2104_);
lean_dec(v___f_2103_);
lean_dec(v_toBind_2102_);
lean_dec(v___x_2101_);
lean_dec_ref(v_resOrders_2099_);
lean_dec(v___x_2096_);
v___x_2112_ = lean_apply_2(v_toPure_2097_, lean_box(0), v_acc_2108_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_array_2117_; lean_object* v_start_2118_; lean_object* v_stop_2119_; lean_object* v___f_2120_; lean_object* v___y_2122_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; uint8_t v___y_2151_; uint8_t v___x_2163_; 
lean_dec_ref(v_acc_2108_);
v___x_2113_ = lean_array_get_borrowed(v___x_2098_, v_resOrders_2099_, v_next_2107_);
v___x_2114_ = lean_array_get(v___x_2100_, v___x_2113_, v___x_2101_);
lean_inc_n(v_next_2107_, 2);
lean_inc(v___x_2101_);
lean_inc_ref(v_resOrders_2099_);
v___x_2115_ = l_Array_toSubarray___redArg(v_resOrders_2099_, v___x_2101_, v_next_2107_);
v___x_2116_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2117_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_ref(v_array_2117_);
v_start_2118_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_start_2118_);
v_stop_2119_ = lean_ctor_get(v___x_2115_, 2);
lean_inc(v_stop_2119_);
lean_dec_ref(v___x_2115_);
lean_inc(v_toPure_2097_);
v___f_2120_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2120_, 0, v_toPure_2097_);
lean_closure_set(v___f_2120_, 1, v_next_2107_);
lean_closure_set(v___f_2120_, 2, v_G_2110_);
lean_inc(v___x_2114_);
v___f_2147_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2147_, 0, v___x_2114_);
v___x_2148_ = lean_box(v___x_2111_);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2149_, 0, v___x_2148_);
lean_closure_set(v___f_2149_, 1, v___f_2147_);
v___x_2163_ = lean_nat_dec_lt(v_start_2118_, v_stop_2119_);
if (v___x_2163_ == 0)
{
lean_dec(v_stop_2119_);
lean_dec(v_start_2118_);
lean_dec_ref(v_array_2117_);
v___y_2151_ = v___x_2111_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___y_2167_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2164_ = lean_box(v___x_2111_);
lean_inc_ref(v___f_2149_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2165_, 0, v___f_2149_);
lean_closure_set(v___f_2165_, 1, v___x_2164_);
v___x_2173_ = lean_array_get_size(v_array_2117_);
v___x_2174_ = lean_nat_dec_le(v_stop_2119_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec(v_stop_2119_);
v___y_2167_ = v___x_2173_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v_stop_2119_;
goto v___jp_2166_;
}
v___jp_2166_:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_nat_dec_lt(v_start_2118_, v___y_2167_);
if (v___x_2168_ == 0)
{
lean_dec(v___y_2167_);
lean_dec_ref(v___f_2165_);
lean_dec(v_start_2118_);
lean_dec_ref(v_array_2117_);
v___y_2151_ = v___x_2163_;
goto v___jp_2150_;
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2169_ = lean_usize_of_nat(v_start_2118_);
lean_dec(v_start_2118_);
v___x_2170_ = lean_usize_of_nat(v___y_2167_);
lean_dec(v___y_2167_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2116_, v___f_2165_, v_array_2117_, v___x_2169_, v___x_2170_);
v___x_2172_ = lean_unbox(v___x_2171_);
lean_dec(v___x_2171_);
if (v___x_2172_ == 0)
{
v___y_2151_ = v___x_2168_;
goto v___jp_2150_;
}
else
{
lean_dec_ref(v___f_2149_);
lean_dec(v___x_2114_);
lean_dec(v_next_2107_);
lean_dec(v___x_2101_);
lean_dec_ref(v_resOrders_2099_);
lean_dec(v___x_2096_);
goto v___jp_2125_;
}
}
}
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_inc(v_toBind_2102_);
v___x_2123_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v___y_2122_, v___f_2103_);
v___x_2124_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v___x_2123_, v___f_2120_);
return v___x_2124_;
}
v___jp_2125_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2104_);
v___x_2127_ = lean_apply_2(v_toPure_2097_, lean_box(0), v___x_2126_);
v___y_2122_ = v___x_2127_;
goto v___jp_2121_;
}
v___jp_2128_:
{
uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2129_ = lean_nat_dec_eq(v_next_2105_, v___x_2101_);
lean_dec(v___x_2101_);
v___x_2130_ = lean_box(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2114_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2106_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_apply_2(v_toPure_2097_, lean_box(0), v___x_2134_);
v___y_2122_ = v___x_2135_;
goto v___jp_2121_;
}
v___jp_2136_:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_nat_dec_lt(v___y_2140_, v___y_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___x_2104_);
goto v___jp_2128_;
}
else
{
size_t v___x_2143_; size_t v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2143_ = lean_usize_of_nat(v___y_2140_);
lean_dec(v___y_2140_);
v___x_2144_ = lean_usize_of_nat(v___y_2141_);
lean_dec(v___y_2141_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2139_, v___y_2137_, v___y_2138_, v___x_2143_, v___x_2144_);
v___x_2146_ = lean_unbox(v___x_2145_);
lean_dec(v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec_ref(v___x_2104_);
goto v___jp_2128_;
}
else
{
lean_dec(v___x_2114_);
lean_dec(v___x_2101_);
goto v___jp_2125_;
}
}
}
v___jp_2150_:
{
if (v___y_2151_ == 0)
{
lean_dec_ref(v___f_2149_);
lean_dec(v___x_2114_);
lean_dec(v_next_2107_);
lean_dec(v___x_2101_);
lean_dec_ref(v_resOrders_2099_);
lean_dec(v___x_2096_);
goto v___jp_2125_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_array_2155_; lean_object* v_start_2156_; lean_object* v_stop_2157_; uint8_t v___x_2158_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_add(v_next_2107_, v___x_2152_);
lean_dec(v_next_2107_);
v___x_2154_ = l_Array_toSubarray___redArg(v_resOrders_2099_, v___x_2153_, v___x_2096_);
v_array_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc_ref(v_array_2155_);
v_start_2156_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_start_2156_);
v_stop_2157_ = lean_ctor_get(v___x_2154_, 2);
lean_inc(v_stop_2157_);
lean_dec_ref(v___x_2154_);
v___x_2158_ = lean_nat_dec_lt(v_start_2156_, v_stop_2157_);
if (v___x_2158_ == 0)
{
lean_dec(v_stop_2157_);
lean_dec(v_start_2156_);
lean_dec_ref(v_array_2155_);
lean_dec_ref(v___f_2149_);
lean_dec_ref(v___x_2104_);
goto v___jp_2128_;
}
else
{
lean_object* v___x_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2159_ = lean_box(v___y_2151_);
v___f_2160_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2160_, 0, v___f_2149_);
lean_closure_set(v___f_2160_, 1, v___x_2159_);
v___x_2161_ = lean_array_get_size(v_array_2155_);
v___x_2162_ = lean_nat_dec_le(v_stop_2157_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec(v_stop_2157_);
v___y_2137_ = v___f_2160_;
v___y_2138_ = v_array_2155_;
v___y_2139_ = v___x_2116_;
v___y_2140_ = v_start_2156_;
v___y_2141_ = v___x_2161_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v___f_2160_;
v___y_2138_ = v_array_2155_;
v___y_2139_ = v___x_2116_;
v___y_2140_ = v_start_2156_;
v___y_2141_ = v_stop_2157_;
goto v___jp_2136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2175_, lean_object* v_toPure_2176_, lean_object* v___x_2177_, lean_object* v_resOrders_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v_toBind_2181_, lean_object* v___f_2182_, lean_object* v___x_2183_, lean_object* v_next_2184_, lean_object* v___x_2185_, lean_object* v_next_2186_, lean_object* v_acc_2187_, lean_object* v_h_2188_, lean_object* v_G_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2175_, v_toPure_2176_, v___x_2177_, v_resOrders_2178_, v___x_2179_, v___x_2180_, v_toBind_2181_, v___f_2182_, v___x_2183_, v_next_2184_, v___x_2185_, v_next_2186_, v_acc_2187_, v_h_2188_, v_G_2189_);
lean_dec(v_next_2184_);
lean_dec(v___x_2179_);
lean_dec_ref(v___x_2177_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2191_, lean_object* v_toPure_2192_, lean_object* v___x_2193_, lean_object* v_resOrders_2194_, lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v_toBind_2197_, lean_object* v___f_2198_, lean_object* v___x_2199_, lean_object* v___x_2200_, lean_object* v___f_2201_, lean_object* v___f_2202_, lean_object* v_next_2203_, lean_object* v_acc_2204_, lean_object* v_h_2205_, lean_object* v_G_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_nat_dec_lt(v_next_2203_, v___x_2191_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_G_2206_);
lean_dec(v_next_2203_);
lean_dec(v___f_2202_);
lean_dec(v___f_2201_);
lean_dec_ref(v___x_2199_);
lean_dec(v___f_2198_);
lean_dec(v_toBind_2197_);
lean_dec(v___x_2196_);
lean_dec(v___x_2195_);
lean_dec_ref(v_resOrders_2194_);
lean_dec_ref(v___x_2193_);
v___x_2208_ = lean_apply_2(v_toPure_2192_, lean_box(0), v_acc_2204_);
return v___x_2208_;
}
else
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v_acc_2204_);
lean_inc(v_next_2203_);
lean_inc(v_toPure_2192_);
v___f_2209_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2209_, 0, v_toPure_2192_);
lean_closure_set(v___f_2209_, 1, v_next_2203_);
lean_closure_set(v___f_2209_, 2, v_G_2206_);
v___x_2210_ = lean_nat_sub(v___x_2191_, v_next_2203_);
lean_inc_ref(v___x_2199_);
lean_inc_n(v_toBind_2197_, 3);
lean_inc(v___x_2196_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2211_, 0, v___x_2210_);
lean_closure_set(v___f_2211_, 1, v_toPure_2192_);
lean_closure_set(v___f_2211_, 2, v___x_2193_);
lean_closure_set(v___f_2211_, 3, v_resOrders_2194_);
lean_closure_set(v___f_2211_, 4, v___x_2195_);
lean_closure_set(v___f_2211_, 5, v___x_2196_);
lean_closure_set(v___f_2211_, 6, v_toBind_2197_);
lean_closure_set(v___f_2211_, 7, v___f_2198_);
lean_closure_set(v___f_2211_, 8, v___x_2199_);
lean_closure_set(v___f_2211_, 9, v_next_2203_);
lean_closure_set(v___f_2211_, 10, v___x_2200_);
v___x_2212_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2211_, v___x_2196_, v___x_2199_, lean_box(0));
v___x_2213_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v___x_2212_, v___f_2201_);
v___x_2214_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v___x_2213_, v___f_2202_);
v___x_2215_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v___x_2214_, v___f_2209_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2216_, lean_object* v_toPure_2217_, lean_object* v___x_2218_, lean_object* v_resOrders_2219_, lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v_toBind_2222_, lean_object* v___f_2223_, lean_object* v___x_2224_, lean_object* v___x_2225_, lean_object* v___f_2226_, lean_object* v___f_2227_, lean_object* v_next_2228_, lean_object* v_acc_2229_, lean_object* v_h_2230_, lean_object* v_G_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2216_, v_toPure_2217_, v___x_2218_, v_resOrders_2219_, v___x_2220_, v___x_2221_, v_toBind_2222_, v___f_2223_, v___x_2224_, v___x_2225_, v___f_2226_, v___f_2227_, v_next_2228_, v_acc_2229_, v_h_2230_, v_G_2231_);
lean_dec(v___x_2216_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Array_instInhabited(lean_box(0));
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2237_, lean_object* v_resOrders_2238_){
_start:
{
lean_object* v_toApplicative_2239_; lean_object* v_toBind_2240_; lean_object* v_toPure_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___f_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_toApplicative_2239_ = lean_ctor_get(v_inst_2237_, 0);
lean_inc_ref(v_toApplicative_2239_);
v_toBind_2240_ = lean_ctor_get(v_inst_2237_, 1);
lean_inc_n(v_toBind_2240_, 2);
lean_dec_ref(v_inst_2237_);
v_toPure_2241_ = lean_ctor_get(v_toApplicative_2239_, 1);
lean_inc_n(v_toPure_2241_, 4);
lean_dec_ref(v_toApplicative_2239_);
v___x_2242_ = lean_box(0);
v___x_2243_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2244_ = lean_array_get_size(v_resOrders_2238_);
lean_inc_ref(v_resOrders_2238_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2245_, 0, v___x_2243_);
lean_closure_set(v___f_2245_, 1, v_resOrders_2238_);
lean_closure_set(v___f_2245_, 2, v___x_2242_);
lean_closure_set(v___f_2245_, 3, v_toPure_2241_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2246_, 0, v_toPure_2241_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = lean_box(0);
v___x_2249_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2250_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2250_, 0, v___x_2249_);
lean_closure_set(v___f_2250_, 1, v_toPure_2241_);
lean_closure_set(v___f_2250_, 2, v___x_2248_);
lean_inc_ref(v___f_2246_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2251_, 0, v___x_2244_);
lean_closure_set(v___f_2251_, 1, v_toPure_2241_);
lean_closure_set(v___f_2251_, 2, v___x_2243_);
lean_closure_set(v___f_2251_, 3, v_resOrders_2238_);
lean_closure_set(v___f_2251_, 4, v___x_2242_);
lean_closure_set(v___f_2251_, 5, v___x_2247_);
lean_closure_set(v___f_2251_, 6, v_toBind_2240_);
lean_closure_set(v___f_2251_, 7, v___f_2246_);
lean_closure_set(v___f_2251_, 8, v___x_2249_);
lean_closure_set(v___f_2251_, 9, v___x_2248_);
lean_closure_set(v___f_2251_, 10, v___f_2250_);
lean_closure_set(v___f_2251_, 11, v___f_2246_);
v___x_2252_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2251_, v___x_2247_, v___x_2249_, lean_box(0));
v___x_2253_ = lean_apply_4(v_toBind_2240_, lean_box(0), lean_box(0), v___x_2252_, v___f_2245_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2254_, lean_object* v_inst_2255_, lean_object* v_resOrders_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2255_, v_resOrders_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2258_){
_start:
{
lean_object* v_structName_2259_; 
v_structName_2259_ = lean_ctor_get(v_x_2258_, 0);
lean_inc(v_structName_2259_);
return v_structName_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2260_);
lean_dec_ref(v_x_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2262_, lean_object* v_result_2263_, lean_object* v_____r_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_apply_2(v_toPure_2262_, lean_box(0), v_result_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2266_, lean_object* v_inst_2267_, lean_object* v_structName_2268_, lean_object* v_toBind_2269_, lean_object* v_result_2270_){
_start:
{
lean_object* v_resolutionOrder_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_resolutionOrder_2271_ = lean_ctor_get(v_result_2270_, 0);
lean_inc_ref(v_resolutionOrder_2271_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2272_, 0, v_toPure_2266_);
lean_closure_set(v___f_2272_, 1, v_result_2270_);
v___x_2273_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2267_, v_structName_2268_, v_resolutionOrder_2271_);
v___x_2274_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2273_, v___f_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v___x_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_array_get_borrowed(v___x_2277_, v_x_2276_, v___x_2275_);
lean_inc(v___x_2278_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object* v___x_2279_, lean_object* v_x_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__5(v___x_2279_, v_x_2280_);
lean_dec_ref(v_x_2280_);
lean_dec(v___x_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_snd_2282_, lean_object* v_x1_2283_, lean_object* v_x2_2284_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_name_eq(v_x2_2284_, v_snd_2282_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_array_push(v_x1_2283_, v_x2_2284_);
return v___x_2286_;
}
else
{
lean_dec(v_x2_2284_);
return v_x1_2283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v_snd_2287_, lean_object* v_x1_2288_, lean_object* v_x2_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v_snd_2287_, v_x1_2288_, v_x2_2289_);
lean_dec(v_snd_2287_);
return v_res_2290_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v_snd_2291_, lean_object* v_x_2292_){
_start:
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_name_eq(v_x_2292_, v_snd_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v_snd_2294_, lean_object* v_x_2295_){
_start:
{
uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_res_2296_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v_snd_2294_, v_x_2295_);
lean_dec(v_x_2295_);
lean_dec(v_snd_2294_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2298_, lean_object* v_parentNames_2299_, lean_object* v_x_2300_){
_start:
{
uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_inc(v_x_2300_);
v___x_2301_ = l_Array_contains___redArg(v___x_2298_, v_parentNames_2299_, v_x_2300_);
v___x_2302_ = lean_box(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_x_2300_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2304_, lean_object* v___f_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2307_ = lean_array_get_size(v_x_2306_);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2304_);
v___x_2309_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2310_ = lean_nat_dec_lt(v___x_2304_, v___x_2307_);
if (v___x_2310_ == 0)
{
lean_dec_ref(v_x_2306_);
lean_dec_ref(v___f_2305_);
return v___x_2308_;
}
else
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_le(v___x_2307_, v___x_2307_);
if (v___x_2311_ == 0)
{
if (v___x_2310_ == 0)
{
lean_dec_ref(v_x_2306_);
lean_dec_ref(v___f_2305_);
return v___x_2308_;
}
else
{
size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = lean_usize_of_nat(v___x_2307_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2309_, v___f_2305_, v_x_2306_, v___x_2312_, v___x_2313_, v___x_2308_);
return v___x_2314_;
}
}
else
{
size_t v___x_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = lean_usize_of_nat(v___x_2307_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2309_, v___f_2305_, v_x_2306_, v___x_2315_, v___x_2316_, v___x_2308_);
return v___x_2317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2318_, lean_object* v___f_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2318_, v___f_2319_, v_x_2320_);
lean_dec(v___x_2318_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v___f_2322_, lean_object* v_x1_2323_, lean_object* v_x2_2324_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_array_2329_; lean_object* v_start_2330_; lean_object* v_stop_2331_; lean_object* v___y_2333_; uint8_t v___x_2340_; 
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_array_get_size(v_x2_2324_);
lean_inc_ref(v_x2_2324_);
v___x_2327_ = l_Array_toSubarray___redArg(v_x2_2324_, v___x_2325_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_ref(v_array_2329_);
v_start_2330_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_start_2330_);
v_stop_2331_ = lean_ctor_get(v___x_2327_, 2);
lean_inc(v_stop_2331_);
lean_dec_ref(v___x_2327_);
v___x_2340_ = lean_nat_dec_lt(v_start_2330_, v_stop_2331_);
if (v___x_2340_ == 0)
{
lean_dec(v_stop_2331_);
lean_dec(v_start_2330_);
lean_dec_ref(v_array_2329_);
lean_dec_ref(v_x2_2324_);
lean_dec_ref(v___f_2322_);
return v_x1_2323_;
}
else
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = lean_array_get_size(v_array_2329_);
v___x_2342_ = lean_nat_dec_le(v_stop_2331_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_dec(v_stop_2331_);
v___y_2333_ = v___x_2341_;
goto v___jp_2332_;
}
else
{
v___y_2333_ = v_stop_2331_;
goto v___jp_2332_;
}
}
v___jp_2332_:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_nat_dec_lt(v_start_2330_, v___y_2333_);
if (v___x_2334_ == 0)
{
lean_dec(v___y_2333_);
lean_dec(v_start_2330_);
lean_dec_ref(v_array_2329_);
lean_dec_ref(v_x2_2324_);
lean_dec_ref(v___f_2322_);
return v_x1_2323_;
}
else
{
size_t v___x_2335_; size_t v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2335_ = lean_usize_of_nat(v_start_2330_);
lean_dec(v_start_2330_);
v___x_2336_ = lean_usize_of_nat(v___y_2333_);
lean_dec(v___y_2333_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2328_, v___f_2322_, v_array_2329_, v___x_2335_, v___x_2336_);
v___x_2338_ = lean_unbox(v___x_2337_);
lean_dec(v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v_x2_2324_);
return v_x1_2323_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_array_push(v_x1_2323_, v_x2_2324_);
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v_toPure_2344_, lean_object* v___x_2345_, lean_object* v_fst_2346_, lean_object* v_fst_2347_, lean_object* v___f_2348_, uint8_t v_relaxed_2349_, lean_object* v_parentNames_2350_, lean_object* v_snd_2351_, lean_object* v___f_2352_, lean_object* v_____x_2353_){
_start:
{
lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v_fst_2362_; lean_object* v_snd_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v_defects_2367_; uint8_t v___x_2381_; 
v_fst_2362_ = lean_ctor_get(v_____x_2353_, 0);
lean_inc(v_fst_2362_);
v_snd_2363_ = lean_ctor_get(v_____x_2353_, 1);
lean_inc_n(v_snd_2363_, 2);
lean_dec_ref(v_____x_2353_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2364_, 0, v_snd_2363_);
lean_inc(v___x_2345_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2365_, 0, v___x_2345_);
lean_closure_set(v___f_2365_, 1, v___f_2364_);
v___x_2381_ = lean_unbox(v_fst_2362_);
lean_dec(v_fst_2362_);
if (v___x_2381_ == 0)
{
if (v_relaxed_2349_ == 0)
{
lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v___y_2385_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2409_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2382_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2350_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2383_, 0, v___x_2382_);
lean_closure_set(v___f_2383_, 1, v_parentNames_2350_);
v___x_2420_ = lean_array_get_size(v_fst_2347_);
v___x_2421_ = lean_mk_empty_array_with_capacity(v___x_2345_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2423_ = lean_nat_dec_lt(v___x_2345_, v___x_2420_);
if (v___x_2423_ == 0)
{
v___y_2409_ = v___x_2421_;
goto v___jp_2408_;
}
else
{
lean_object* v___f_2424_; lean_object* v___f_2425_; uint8_t v___x_2426_; 
lean_inc(v_snd_2363_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_2424_, 0, v_snd_2363_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10), 3, 1);
lean_closure_set(v___f_2425_, 0, v___f_2424_);
v___x_2426_ = lean_nat_dec_le(v___x_2420_, v___x_2420_);
if (v___x_2426_ == 0)
{
if (v___x_2423_ == 0)
{
lean_dec_ref(v___f_2425_);
v___y_2409_ = v___x_2421_;
goto v___jp_2408_;
}
else
{
size_t v___x_2427_; size_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = lean_usize_of_nat(v___x_2420_);
lean_inc(v_fst_2347_);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2422_, v___f_2425_, v_fst_2347_, v___x_2427_, v___x_2428_, v___x_2421_);
v___y_2409_ = v___x_2429_;
goto v___jp_2408_;
}
}
else
{
size_t v___x_2430_; size_t v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = ((size_t)0ULL);
v___x_2431_ = lean_usize_of_nat(v___x_2420_);
lean_inc(v_fst_2347_);
v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2422_, v___f_2425_, v_fst_2347_, v___x_2430_, v___x_2431_, v___x_2421_);
v___y_2409_ = v___x_2432_;
goto v___jp_2408_;
}
}
v___jp_2384_:
{
lean_object* v_conflicts_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; size_t v_sz_2389_; size_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_defects_2393_; 
v_conflicts_2386_ = l_Array_eraseReps___redArg(v___x_2382_, v___y_2385_);
lean_inc_n(v_snd_2363_, 2);
v___x_2387_ = l_Array_contains___redArg(v___x_2382_, v_parentNames_2350_, v_snd_2363_);
v___x_2388_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2389_ = lean_array_size(v_conflicts_2386_);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2388_, v___f_2383_, v_sz_2389_, v___x_2390_, v_conflicts_2386_);
v___x_2392_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2392_, 0, v_snd_2363_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*2, v___x_2387_);
v_defects_2393_ = lean_array_push(v_snd_2351_, v___x_2392_);
v_defects_2367_ = v_defects_2393_;
goto v___jp_2366_;
}
v___jp_2394_:
{
lean_object* v___x_2400_; 
lean_inc_ref(v___y_2396_);
v___x_2400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2396_, v___y_2395_, v___y_2397_, v___y_2398_, v___y_2399_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2399_);
lean_dec(v___y_2395_);
v___y_2385_ = v___x_2400_;
goto v___jp_2384_;
}
v___jp_2401_:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_le(v___y_2406_, v___y_2404_);
if (v___x_2407_ == 0)
{
lean_dec(v___y_2404_);
lean_inc(v___y_2406_);
v___y_2395_ = v___y_2402_;
v___y_2396_ = v___y_2403_;
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2406_;
v___y_2399_ = v___y_2406_;
goto v___jp_2394_;
}
else
{
v___y_2395_ = v___y_2402_;
v___y_2396_ = v___y_2403_;
v___y_2397_ = v___y_2405_;
v___y_2398_ = v___y_2406_;
v___y_2399_ = v___y_2404_;
goto v___jp_2394_;
}
}
v___jp_2408_:
{
lean_object* v___x_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2411_ = lean_array_size(v___y_2409_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2410_, v___f_2352_, v_sz_2411_, v___x_2412_, v___y_2409_);
v___x_2414_ = lean_array_get_size(v___x_2413_);
v___x_2415_ = lean_nat_dec_eq(v___x_2414_, v___x_2345_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2416_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0));
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_nat_sub(v___x_2414_, v___x_2417_);
v___x_2419_ = lean_nat_dec_le(v___x_2345_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_inc(v___x_2418_);
v___y_2402_ = v___x_2414_;
v___y_2403_ = v___x_2416_;
v___y_2404_ = v___x_2418_;
v___y_2405_ = v___x_2413_;
v___y_2406_ = v___x_2418_;
goto v___jp_2401_;
}
else
{
lean_inc(v___x_2345_);
v___y_2402_ = v___x_2414_;
v___y_2403_ = v___x_2416_;
v___y_2404_ = v___x_2418_;
v___y_2405_ = v___x_2413_;
v___y_2406_ = v___x_2345_;
goto v___jp_2401_;
}
}
else
{
v___y_2385_ = v___x_2413_;
goto v___jp_2384_;
}
}
}
else
{
lean_dec_ref(v___f_2352_);
lean_dec_ref(v_parentNames_2350_);
v_defects_2367_ = v_snd_2351_;
goto v___jp_2366_;
}
}
else
{
lean_dec_ref(v___f_2352_);
lean_dec_ref(v_parentNames_2350_);
v_defects_2367_ = v_snd_2351_;
goto v___jp_2366_;
}
v___jp_2354_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2356_);
lean_ctor_set(v___x_2358_, 1, v___y_2355_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___y_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___x_2361_ = lean_apply_2(v_toPure_2344_, lean_box(0), v___x_2360_);
return v___x_2361_;
}
v___jp_2366_:
{
lean_object* v_resOrder_2368_; lean_object* v___x_2369_; size_t v_sz_2370_; size_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_resOrder_2368_ = lean_array_push(v_fst_2346_, v_snd_2363_);
v___x_2369_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2370_ = lean_array_size(v_fst_2347_);
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2369_, v___f_2365_, v_sz_2370_, v___x_2371_, v_fst_2347_);
v___x_2373_ = lean_array_get_size(v___x_2372_);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2345_);
v___x_2375_ = lean_nat_dec_lt(v___x_2345_, v___x_2373_);
lean_dec(v___x_2345_);
if (v___x_2375_ == 0)
{
lean_dec(v___x_2372_);
lean_dec_ref(v___f_2348_);
v___y_2355_ = v_defects_2367_;
v___y_2356_ = v_resOrder_2368_;
v___y_2357_ = v___x_2374_;
goto v___jp_2354_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_nat_dec_le(v___x_2373_, v___x_2373_);
if (v___x_2376_ == 0)
{
if (v___x_2375_ == 0)
{
lean_dec(v___x_2372_);
lean_dec_ref(v___f_2348_);
v___y_2355_ = v_defects_2367_;
v___y_2356_ = v_resOrder_2368_;
v___y_2357_ = v___x_2374_;
goto v___jp_2354_;
}
else
{
size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_usize_of_nat(v___x_2373_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2369_, v___f_2348_, v___x_2372_, v___x_2371_, v___x_2377_, v___x_2374_);
v___y_2355_ = v_defects_2367_;
v___y_2356_ = v_resOrder_2368_;
v___y_2357_ = v___x_2378_;
goto v___jp_2354_;
}
}
else
{
size_t v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_usize_of_nat(v___x_2373_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2369_, v___f_2348_, v___x_2372_, v___x_2371_, v___x_2379_, v___x_2374_);
v___y_2355_ = v_defects_2367_;
v___y_2356_ = v_resOrder_2368_;
v___y_2357_ = v___x_2380_;
goto v___jp_2354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object* v_toPure_2433_, lean_object* v___x_2434_, lean_object* v_fst_2435_, lean_object* v_fst_2436_, lean_object* v___f_2437_, lean_object* v_relaxed_2438_, lean_object* v_parentNames_2439_, lean_object* v_snd_2440_, lean_object* v___f_2441_, lean_object* v_____x_2442_){
_start:
{
uint8_t v_relaxed_boxed_2443_; lean_object* v_res_2444_; 
v_relaxed_boxed_2443_ = lean_unbox(v_relaxed_2438_);
v_res_2444_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__11(v_toPure_2433_, v___x_2434_, v_fst_2435_, v_fst_2436_, v___f_2437_, v_relaxed_boxed_2443_, v_parentNames_2439_, v_snd_2440_, v___f_2441_, v_____x_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v___x_2445_, lean_object* v_toPure_2446_, lean_object* v___f_2447_, uint8_t v_relaxed_2448_, lean_object* v_parentNames_2449_, lean_object* v___f_2450_, lean_object* v_inst_2451_, lean_object* v_toBind_2452_, lean_object* v_x_2453_, lean_object* v_____s_2454_){
_start:
{
lean_object* v_snd_2455_; lean_object* v_fst_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2480_; 
v_snd_2455_ = lean_ctor_get(v_____s_2454_, 1);
v_fst_2456_ = lean_ctor_get(v_____s_2454_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_____s_2454_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2458_ = v_____s_2454_;
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_snd_2455_);
lean_inc(v_fst_2456_);
lean_dec(v_____s_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_fst_2460_; lean_object* v_snd_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2479_; 
v_fst_2460_ = lean_ctor_get(v_snd_2455_, 0);
v_snd_2461_ = lean_ctor_get(v_snd_2455_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_snd_2455_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2463_ = v_snd_2455_;
v_isShared_2464_ = v_isSharedCheck_2479_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_snd_2461_);
lean_inc(v_fst_2460_);
lean_dec(v_snd_2455_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2479_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = lean_array_get_size(v_fst_2456_);
v___x_2466_ = lean_nat_dec_eq(v___x_2465_, v___x_2445_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_del_object(v___x_2463_);
lean_del_object(v___x_2458_);
v___x_2467_ = lean_box(v_relaxed_2448_);
lean_inc(v_fst_2456_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_2468_, 0, v_toPure_2446_);
lean_closure_set(v___f_2468_, 1, v___x_2445_);
lean_closure_set(v___f_2468_, 2, v_fst_2460_);
lean_closure_set(v___f_2468_, 3, v_fst_2456_);
lean_closure_set(v___f_2468_, 4, v___f_2447_);
lean_closure_set(v___f_2468_, 5, v___x_2467_);
lean_closure_set(v___f_2468_, 6, v_parentNames_2449_);
lean_closure_set(v___f_2468_, 7, v_snd_2461_);
lean_closure_set(v___f_2468_, 8, v___f_2450_);
v___x_2469_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2451_, v_fst_2456_);
v___x_2470_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v___x_2469_, v___f_2468_);
return v___x_2470_;
}
else
{
lean_object* v___x_2472_; 
lean_dec(v_toBind_2452_);
lean_dec_ref(v_inst_2451_);
lean_dec_ref(v___f_2450_);
lean_dec_ref(v_parentNames_2449_);
lean_dec_ref(v___f_2447_);
lean_dec(v___x_2445_);
if (v_isShared_2464_ == 0)
{
v___x_2472_ = v___x_2463_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_fst_2460_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_snd_2461_);
v___x_2472_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2472_);
v___x_2474_ = v___x_2458_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_fst_2456_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___x_2476_ = lean_apply_2(v_toPure_2446_, lean_box(0), v___x_2475_);
return v___x_2476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v___x_2481_, lean_object* v_toPure_2482_, lean_object* v___f_2483_, lean_object* v_relaxed_2484_, lean_object* v_parentNames_2485_, lean_object* v___f_2486_, lean_object* v_inst_2487_, lean_object* v_toBind_2488_, lean_object* v_x_2489_, lean_object* v_____s_2490_){
_start:
{
uint8_t v_relaxed_boxed_2491_; lean_object* v_res_2492_; 
v_relaxed_boxed_2491_ = lean_unbox(v_relaxed_2484_);
v_res_2492_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v___x_2481_, v_toPure_2482_, v___f_2483_, v_relaxed_boxed_2491_, v_parentNames_2485_, v___f_2486_, v_inst_2487_, v_toBind_2488_, v_x_2489_, v_____s_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v_toPure_2497_, lean_object* v___f_2498_, uint8_t v_relaxed_2499_, lean_object* v_parentNames_2500_, lean_object* v_inst_2501_, lean_object* v_toBind_2502_, lean_object* v_structName_2503_, lean_object* v___f_2504_, lean_object* v___f_2505_, lean_object* v_parentResOrders_2506_){
_start:
{
lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___f_2510_; lean_object* v___y_2512_; lean_object* v_j_2521_; lean_object* v_as_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v___f_2508_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0));
v___x_2509_ = lean_box(v_relaxed_2499_);
lean_inc(v_toBind_2502_);
lean_inc_ref(v_inst_2501_);
lean_inc_ref(v_parentNames_2500_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2510_, 0, v___x_2507_);
lean_closure_set(v___f_2510_, 1, v_toPure_2497_);
lean_closure_set(v___f_2510_, 2, v___f_2498_);
lean_closure_set(v___f_2510_, 3, v___x_2509_);
lean_closure_set(v___f_2510_, 4, v_parentNames_2500_);
lean_closure_set(v___f_2510_, 5, v___f_2508_);
lean_closure_set(v___f_2510_, 6, v_inst_2501_);
lean_closure_set(v___f_2510_, 7, v_toBind_2502_);
v_j_2521_ = lean_array_get_size(v_parentResOrders_2506_);
v_as_2522_ = lean_array_push(v_parentResOrders_2506_, v_parentNames_2500_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2507_, v_as_2522_, v_j_2521_);
v___x_2524_ = lean_array_get_size(v___x_2523_);
v___x_2525_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2526_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2527_ = lean_nat_dec_lt(v___x_2507_, v___x_2524_);
if (v___x_2527_ == 0)
{
lean_dec_ref(v___x_2523_);
lean_dec_ref(v___f_2505_);
v___y_2512_ = v___x_2525_;
goto v___jp_2511_;
}
else
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_le(v___x_2524_, v___x_2524_);
if (v___x_2528_ == 0)
{
if (v___x_2527_ == 0)
{
lean_dec_ref(v___x_2523_);
lean_dec_ref(v___f_2505_);
v___y_2512_ = v___x_2525_;
goto v___jp_2511_;
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2524_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2526_, v___f_2505_, v___x_2523_, v___x_2529_, v___x_2530_, v___x_2525_);
v___y_2512_ = v___x_2531_;
goto v___jp_2511_;
}
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2524_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2526_, v___f_2505_, v___x_2523_, v___x_2532_, v___x_2533_, v___x_2525_);
v___y_2512_ = v___x_2534_;
goto v___jp_2511_;
}
}
v___jp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_resOrder_2515_; lean_object* v_defects_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2513_);
v_resOrder_2515_ = lean_array_push(v___x_2514_, v_structName_2503_);
v_defects_2516_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_resOrder_2515_);
lean_ctor_set(v___x_2517_, 1, v_defects_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2512_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_2501_, v___f_2510_, v___x_2518_);
v___x_2520_ = lean_apply_4(v_toBind_2502_, lean_box(0), lean_box(0), v___x_2519_, v___f_2504_);
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v_toPure_2535_, lean_object* v___f_2536_, lean_object* v_relaxed_2537_, lean_object* v_parentNames_2538_, lean_object* v_inst_2539_, lean_object* v_toBind_2540_, lean_object* v_structName_2541_, lean_object* v___f_2542_, lean_object* v___f_2543_, lean_object* v_parentResOrders_2544_){
_start:
{
uint8_t v_relaxed_boxed_2545_; lean_object* v_res_2546_; 
v_relaxed_boxed_2545_ = lean_unbox(v_relaxed_2537_);
v_res_2546_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v_toPure_2535_, v___f_2536_, v_relaxed_boxed_2545_, v_parentNames_2538_, v_inst_2539_, v_toBind_2540_, v_structName_2541_, v___f_2542_, v___f_2543_, v_parentResOrders_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2547_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = lean_array_get_size(v_x_2547_);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_nat_dec_eq(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
uint8_t v___x_2551_; 
v___x_2551_ = 1;
return v___x_2551_;
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = 0;
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2553_){
_start:
{
uint8_t v_res_2554_; lean_object* v_r_2555_; 
v_res_2554_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2553_);
lean_dec_ref(v_x_2553_);
v_r_2555_ = lean_box(v_res_2554_);
return v_r_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2556_, lean_object* v_x1_2557_, lean_object* v_x2_2558_){
_start:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; 
lean_inc_ref(v_x2_2558_);
v___x_2559_ = lean_apply_1(v___f_2556_, v_x2_2558_);
v___x_2560_ = lean_unbox(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_dec_ref(v_x2_2558_);
return v_x1_2557_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_array_push(v_x1_2557_, v_x2_2558_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2562_, lean_object* v_____s_2563_){
_start:
{
lean_object* v_snd_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2574_; 
v_snd_2564_ = lean_ctor_get(v_____s_2563_, 1);
lean_inc(v_snd_2564_);
lean_dec_ref(v_____s_2563_);
v_fst_2565_ = lean_ctor_get(v_snd_2564_, 0);
v_snd_2566_ = lean_ctor_get(v_snd_2564_, 1);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_snd_2564_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2568_ = v_snd_2564_;
v_isShared_2569_ = v_isSharedCheck_2574_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_snd_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2574_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_fst_2565_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_snd_2566_);
v___x_2571_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_apply_2(v_toPure_2562_, lean_box(0), v___x_2571_);
return v___x_2572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2575_, lean_object* v_____do__lift_2576_){
_start:
{
lean_object* v_resolutionOrder_2577_; lean_object* v___x_2578_; 
v_resolutionOrder_2577_ = lean_ctor_get(v_____do__lift_2576_, 0);
lean_inc_ref(v_resolutionOrder_2577_);
lean_dec_ref(v_____do__lift_2576_);
v___x_2578_ = lean_apply_2(v_toPure_2575_, lean_box(0), v_resolutionOrder_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_structName_2585_, lean_object* v_parentNames_2586_, uint8_t v_relaxed_2587_){
_start:
{
lean_object* v_toApplicative_2588_; lean_object* v_toBind_2589_; lean_object* v_toPure_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; size_t v_sz_2597_; size_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_toApplicative_2588_ = lean_ctor_get(v_inst_2583_, 0);
v_toBind_2589_ = lean_ctor_get(v_inst_2583_, 1);
lean_inc_n(v_toBind_2589_, 3);
v_toPure_2590_ = lean_ctor_get(v_toApplicative_2588_, 1);
v___f_2591_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc_n(v_toPure_2590_, 3);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2592_, 0, v_toPure_2590_);
lean_inc_ref_n(v_inst_2583_, 2);
v___f_2593_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2593_, 0, v_inst_2583_);
lean_closure_set(v___f_2593_, 1, v_inst_2584_);
lean_closure_set(v___f_2593_, 2, v_toBind_2589_);
lean_closure_set(v___f_2593_, 3, v___f_2592_);
v___f_2594_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2594_, 0, v_toPure_2590_);
v___x_2595_ = lean_box(v_relaxed_2587_);
lean_inc_ref(v_parentNames_2586_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 10, 9);
lean_closure_set(v___f_2596_, 0, v_toPure_2590_);
lean_closure_set(v___f_2596_, 1, v___f_2591_);
lean_closure_set(v___f_2596_, 2, v___x_2595_);
lean_closure_set(v___f_2596_, 3, v_parentNames_2586_);
lean_closure_set(v___f_2596_, 4, v_inst_2583_);
lean_closure_set(v___f_2596_, 5, v_toBind_2589_);
lean_closure_set(v___f_2596_, 6, v_structName_2585_);
lean_closure_set(v___f_2596_, 7, v___f_2594_);
lean_closure_set(v___f_2596_, 8, v___f_2591_);
v_sz_2597_ = lean_array_size(v_parentNames_2586_);
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2583_, v___f_2593_, v_sz_2597_, v___x_2598_, v_parentNames_2586_);
v___x_2600_ = lean_apply_4(v_toBind_2589_, lean_box(0), lean_box(0), v___x_2599_, v___f_2596_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2601_, lean_object* v_toPure_2602_, lean_object* v___f_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, uint8_t v_relaxed_2606_, lean_object* v_toBind_2607_, lean_object* v___f_2608_, lean_object* v_env_2609_){
_start:
{
lean_object* v___x_2610_; 
lean_inc_ref(v_env_2609_);
v___x_2610_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2609_, v_structName_2601_);
if (lean_obj_tag(v___x_2610_) == 1)
{
lean_object* v_val_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v_env_2609_);
lean_dec(v___f_2608_);
lean_dec(v_toBind_2607_);
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
lean_dec_ref(v___f_2603_);
lean_dec(v_structName_2601_);
v_val_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_val_2611_);
lean_dec_ref(v___x_2610_);
v___x_2612_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_val_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_apply_2(v_toPure_2602_, lean_box(0), v___x_2613_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; size_t v_sz_2617_; size_t v___x_2618_; lean_object* v_parentNames_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec(v___x_2610_);
lean_dec(v_toPure_2602_);
lean_inc(v_structName_2601_);
v___x_2615_ = l_Lean_getStructureParentInfo(v_env_2609_, v_structName_2601_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2617_ = lean_array_size(v___x_2615_);
v___x_2618_ = ((size_t)0ULL);
v_parentNames_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2616_, v___f_2603_, v_sz_2617_, v___x_2618_, v___x_2615_);
v___x_2620_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2604_, v_inst_2605_, v_structName_2601_, v_parentNames_2619_, v_relaxed_2606_);
v___x_2621_ = lean_apply_4(v_toBind_2607_, lean_box(0), lean_box(0), v___x_2620_, v___f_2608_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2622_, lean_object* v_toPure_2623_, lean_object* v___f_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_relaxed_2627_, lean_object* v_toBind_2628_, lean_object* v___f_2629_, lean_object* v_env_2630_){
_start:
{
uint8_t v_relaxed_boxed_2631_; lean_object* v_res_2632_; 
v_relaxed_boxed_2631_ = lean_unbox(v_relaxed_2627_);
v_res_2632_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2622_, v_toPure_2623_, v___f_2624_, v_inst_2625_, v_inst_2626_, v_relaxed_boxed_2631_, v_toBind_2628_, v___f_2629_, v_env_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_structName_2635_, uint8_t v_relaxed_2636_){
_start:
{
lean_object* v_toApplicative_2637_; lean_object* v_toBind_2638_; lean_object* v_getEnv_2639_; lean_object* v_toPure_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v___f_2644_; lean_object* v___x_2645_; 
v_toApplicative_2637_ = lean_ctor_get(v_inst_2633_, 0);
v_toBind_2638_ = lean_ctor_get(v_inst_2633_, 1);
lean_inc_n(v_toBind_2638_, 3);
v_getEnv_2639_ = lean_ctor_get(v_inst_2634_, 0);
lean_inc(v_getEnv_2639_);
v_toPure_2640_ = lean_ctor_get(v_toApplicative_2637_, 1);
lean_inc_n(v_toPure_2640_, 2);
v___f_2641_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2635_);
lean_inc_ref(v_inst_2634_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2642_, 0, v_toPure_2640_);
lean_closure_set(v___f_2642_, 1, v_inst_2634_);
lean_closure_set(v___f_2642_, 2, v_structName_2635_);
lean_closure_set(v___f_2642_, 3, v_toBind_2638_);
v___x_2643_ = lean_box(v_relaxed_2636_);
v___f_2644_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2644_, 0, v_structName_2635_);
lean_closure_set(v___f_2644_, 1, v_toPure_2640_);
lean_closure_set(v___f_2644_, 2, v___f_2641_);
lean_closure_set(v___f_2644_, 3, v_inst_2633_);
lean_closure_set(v___f_2644_, 4, v_inst_2634_);
lean_closure_set(v___f_2644_, 5, v___x_2643_);
lean_closure_set(v___f_2644_, 6, v_toBind_2638_);
lean_closure_set(v___f_2644_, 7, v___f_2642_);
v___x_2645_ = lean_apply_4(v_toBind_2638_, lean_box(0), lean_box(0), v_getEnv_2639_, v___f_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_toBind_2648_, lean_object* v___f_2649_, lean_object* v_parentName_2650_){
_start:
{
uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = 1;
v___x_2652_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2646_, v_inst_2647_, v_parentName_2650_, v___x_2651_);
v___x_2653_ = lean_apply_4(v_toBind_2648_, lean_box(0), lean_box(0), v___x_2652_, v___f_2649_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_structName_2656_, lean_object* v_relaxed_2657_){
_start:
{
uint8_t v_relaxed_boxed_2658_; lean_object* v_res_2659_; 
v_relaxed_boxed_2658_ = lean_unbox(v_relaxed_2657_);
v_res_2659_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2654_, v_inst_2655_, v_structName_2656_, v_relaxed_boxed_2658_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_structName_2662_, lean_object* v_parentNames_2663_, lean_object* v_relaxed_2664_){
_start:
{
uint8_t v_relaxed_boxed_2665_; lean_object* v_res_2666_; 
v_relaxed_boxed_2665_ = lean_unbox(v_relaxed_2664_);
v_res_2666_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2660_, v_inst_2661_, v_structName_2662_, v_parentNames_2663_, v_relaxed_boxed_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_structName_2670_, uint8_t v_relaxed_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2668_, v_inst_2669_, v_structName_2670_, v_relaxed_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_structName_2676_, lean_object* v_relaxed_2677_){
_start:
{
uint8_t v_relaxed_boxed_2678_; lean_object* v_res_2679_; 
v_relaxed_boxed_2678_ = lean_unbox(v_relaxed_2677_);
v_res_2679_ = l_Lean_computeStructureResolutionOrder(v_m_2673_, v_inst_2674_, v_inst_2675_, v_structName_2676_, v_relaxed_boxed_2678_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_structName_2683_, lean_object* v_parentNames_2684_, uint8_t v_relaxed_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2681_, v_inst_2682_, v_structName_2683_, v_parentNames_2684_, v_relaxed_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_structName_2690_, lean_object* v_parentNames_2691_, lean_object* v_relaxed_2692_){
_start:
{
uint8_t v_relaxed_boxed_2693_; lean_object* v_res_2694_; 
v_relaxed_boxed_2693_ = lean_unbox(v_relaxed_2692_);
v_res_2694_ = l_Lean_mergeStructureResolutionOrders(v_m_2687_, v_inst_2688_, v_inst_2689_, v_structName_2690_, v_parentNames_2691_, v_relaxed_boxed_2693_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2695_){
_start:
{
lean_object* v_resolutionOrder_2696_; 
v_resolutionOrder_2696_ = lean_ctor_get(v_x_2695_, 0);
lean_inc_ref(v_resolutionOrder_2696_);
return v_resolutionOrder_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2697_);
lean_dec_ref(v_x_2697_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_structName_2702_){
_start:
{
lean_object* v_toApplicative_2703_; lean_object* v_toFunctor_2704_; lean_object* v_map_2705_; lean_object* v___f_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_toApplicative_2703_ = lean_ctor_get(v_inst_2700_, 0);
v_toFunctor_2704_ = lean_ctor_get(v_toApplicative_2703_, 0);
v_map_2705_ = lean_ctor_get(v_toFunctor_2704_, 0);
lean_inc(v_map_2705_);
v___f_2706_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2707_ = 1;
v___x_2708_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2700_, v_inst_2701_, v_structName_2702_, v___x_2707_);
v___x_2709_ = lean_apply_4(v_map_2705_, lean_box(0), lean_box(0), v___f_2706_, v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_structName_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2711_, v_inst_2712_, v_structName_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2715_, lean_object* v_structName_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Array_erase___redArg(v___x_2715_, v_x_2717_, v_structName_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_structName_2721_){
_start:
{
lean_object* v_toApplicative_2722_; lean_object* v_toFunctor_2723_; lean_object* v_map_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_toApplicative_2722_ = lean_ctor_get(v_inst_2719_, 0);
v_toFunctor_2723_ = lean_ctor_get(v_toApplicative_2722_, 0);
v_map_2724_ = lean_ctor_get(v_toFunctor_2723_, 0);
lean_inc(v_map_2724_);
v___x_2725_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2721_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2726_, 0, v___x_2725_);
lean_closure_set(v___f_2726_, 1, v_structName_2721_);
v___x_2727_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2719_, v_inst_2720_, v_structName_2721_);
v___x_2728_ = lean_apply_4(v_map_2724_, lean_box(0), lean_box(0), v___f_2726_, v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_structName_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_getAllParentStructures___redArg(v_inst_2730_, v_inst_2731_, v_structName_2732_);
return v___x_2733_;
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
