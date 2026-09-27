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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
v___x_221_ = lean_box(0);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v___x_218_, v___x_222_);
v___x_224_ = lean_nat_dec_le(v___x_217_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v___x_223_);
return v___x_221_;
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
lean_ctor_set(v___x_228_, 2, v___x_221_);
lean_ctor_set(v___x_228_, 3, v___x_221_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*4, v___x_227_);
v___x_229_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_213_, v___x_228_, v___x_217_, v___x_223_);
lean_dec_ref_known(v___x_228_, 4);
if (lean_obj_tag(v___x_229_) == 0)
{
return v___x_221_;
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
v___x_254_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_516_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1800__boxed_623_; size_t v_x_1801__boxed_624_; lean_object* v_res_625_; 
v_x_1800__boxed_623_ = lean_unbox_usize(v_x_619_);
lean_dec(v_x_619_);
v_x_1801__boxed_624_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_res_625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_618_, v_x_1800__boxed_623_, v_x_1801__boxed_624_, v_x_621_, v_x_622_);
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
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_702_ = 0;
v___x_703_ = lean_box(0);
v___x_704_ = lean_box(2);
v___f_705_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_706_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_707_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_708_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_709_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_710_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_711_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___f_709_);
lean_ctor_set(v___x_711_, 2, v___f_708_);
lean_ctor_set(v___x_711_, 3, v___f_707_);
lean_ctor_set(v___x_711_, 4, v___f_706_);
lean_ctor_set(v___x_711_, 5, v___f_705_);
lean_ctor_set(v___x_711_, 6, v___x_704_);
lean_ctor_set(v___x_711_, 7, v___x_703_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*8, v___x_702_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___f_712_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_713_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___f_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_717_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_720_, lean_object* v_m_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_723_, lean_object* v_m_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_723_, v_m_724_);
lean_dec_ref(v_m_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_726_, lean_object* v_as_727_, lean_object* v_lo_728_, lean_object* v_hi_729_, lean_object* v_w_730_, lean_object* v_hlo_731_, lean_object* v_hhi_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_n_726_, v_as_727_, v_lo_728_, v_hi_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_734_, lean_object* v_as_735_, lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_w_738_, lean_object* v_hlo_739_, lean_object* v_hhi_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_734_, v_as_735_, v_lo_736_, v_hi_737_, v_w_738_, v_hlo_739_, v_hhi_740_);
lean_dec(v_hi_737_);
lean_dec(v_n_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_743_, v_x_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_747_, lean_object* v_00_u03b2_748_, lean_object* v_map_749_, lean_object* v_f_750_, lean_object* v_init_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_749_, v_f_750_, v_init_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_753_, lean_object* v_00_u03b2_754_, lean_object* v_map_755_, lean_object* v_f_756_, lean_object* v_init_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_753_, v_00_u03b2_754_, v_map_755_, v_f_756_, v_init_757_);
lean_dec_ref(v_map_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_759_, lean_object* v_lo_760_, lean_object* v_hi_761_, lean_object* v_hhi_762_, lean_object* v_pivot_763_, lean_object* v_as_764_, lean_object* v_i_765_, lean_object* v_k_766_, lean_object* v_ilo_767_, lean_object* v_ik_768_, lean_object* v_w_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_761_, v_pivot_763_, v_as_764_, v_i_765_, v_k_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_771_, lean_object* v_lo_772_, lean_object* v_hi_773_, lean_object* v_hhi_774_, lean_object* v_pivot_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_k_778_, lean_object* v_ilo_779_, lean_object* v_ik_780_, lean_object* v_w_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2_spec__3(v_n_771_, v_lo_772_, v_hi_773_, v_hhi_774_, v_pivot_775_, v_as_776_, v_i_777_, v_k_778_, v_ilo_779_, v_ik_780_, v_w_781_);
lean_dec_ref(v_pivot_775_);
lean_dec(v_hi_773_);
lean_dec(v_lo_772_);
lean_dec(v_n_771_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, size_t v_x_785_, size_t v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_784_, v_x_785_, v_x_786_, v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
size_t v_x_2191__boxed_796_; size_t v_x_2192__boxed_797_; lean_object* v_res_798_; 
v_x_2191__boxed_796_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_x_2192__boxed_797_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_res_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_790_, v_x_791_, v_x_2191__boxed_796_, v_x_2192__boxed_797_, v_x_794_, v_x_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_799_, lean_object* v_f_800_, lean_object* v_init_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_800_, v_map_799_, v_init_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_803_, lean_object* v_f_804_, lean_object* v_init_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_803_, v_f_804_, v_init_805_);
lean_dec_ref(v_map_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_807_, lean_object* v_00_u03b2_808_, lean_object* v_map_809_, lean_object* v_f_810_, lean_object* v_init_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_810_, v_map_809_, v_init_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_813_, lean_object* v_00_u03b2_814_, lean_object* v_map_815_, lean_object* v_f_816_, lean_object* v_init_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_813_, v_00_u03b2_814_, v_map_815_, v_f_816_, v_init_817_);
lean_dec_ref(v_map_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_819_, lean_object* v_n_820_, lean_object* v_k_821_, lean_object* v_v_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_820_, v_k_821_, v_v_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_824_, size_t v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_825_, v_keys_826_, v_vals_827_, v_i_829_, v_entries_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_832_, lean_object* v_depth_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_entries_838_){
_start:
{
size_t v_depth_boxed_839_; lean_object* v_res_840_; 
v_depth_boxed_839_ = lean_unbox_usize(v_depth_833_);
lean_dec(v_depth_833_);
v_res_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_832_, v_depth_boxed_839_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_entries_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_841_, lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_f_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_844_, v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_848_, lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_f_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_848_, v_00_u03b1_849_, v_00_u03b2_850_, v_f_851_, v_x_852_, v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_00_u03c3_863_, lean_object* v_f_864_, lean_object* v_as_865_, size_t v_i_866_, size_t v_stop_867_, lean_object* v_b_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_864_, v_as_865_, v_i_866_, v_stop_867_, v_b_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_00_u03c3_872_, lean_object* v_f_873_, lean_object* v_as_874_, lean_object* v_i_875_, lean_object* v_stop_876_, lean_object* v_b_877_){
_start:
{
size_t v_i_boxed_878_; size_t v_stop_boxed_879_; lean_object* v_res_880_; 
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_stop_boxed_879_ = lean_unbox_usize(v_stop_876_);
lean_dec(v_stop_876_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_870_, v_00_u03b2_871_, v_00_u03c3_872_, v_f_873_, v_as_874_, v_i_boxed_878_, v_stop_boxed_879_, v_b_877_);
lean_dec_ref(v_as_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_881_, lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_f_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_heq_887_, lean_object* v_i_888_, lean_object* v_acc_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_884_, v_keys_885_, v_vals_886_, v_i_888_, v_acc_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_891_, lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_f_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_acc_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_891_, v_00_u03b1_892_, v_00_u03b2_893_, v_f_894_, v_keys_895_, v_vals_896_, v_heq_897_, v_i_898_, v_acc_899_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_908_, size_t v_i_909_, lean_object* v_bs_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_909_, v_sz_908_);
if (v___x_911_ == 0)
{
return v_bs_910_;
}
else
{
lean_object* v_v_912_; lean_object* v_fieldName_913_; lean_object* v___x_914_; lean_object* v_bs_x27_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_v_912_ = lean_array_uget_borrowed(v_bs_910_, v_i_909_);
v_fieldName_913_ = lean_ctor_get(v_v_912_, 0);
lean_inc(v_fieldName_913_);
v___x_914_ = lean_unsigned_to_nat(0u);
v_bs_x27_915_ = lean_array_uset(v_bs_910_, v_i_909_, v___x_914_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_909_, v___x_916_);
v___x_918_ = lean_array_uset(v_bs_x27_915_, v_i_909_, v_fieldName_913_);
v_i_909_ = v___x_917_;
v_bs_910_ = v___x_918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_923_, v_i_boxed_924_, v_bs_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(lean_object* v_hi_926_, lean_object* v_pivot_927_, lean_object* v_as_928_, lean_object* v_i_929_, lean_object* v_k_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_lt(v_k_930_, v_hi_926_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_k_930_);
v___x_932_ = lean_array_fswap(v_as_928_, v_i_929_, v_hi_926_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_i_929_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_array_fget_borrowed(v_as_928_, v_k_930_);
v___x_935_ = l_Lean_StructureFieldInfo_lt(v___x_934_, v_pivot_927_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_k_930_, v___x_936_);
lean_dec(v_k_930_);
v_k_930_ = v___x_937_;
goto _start;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = lean_array_fswap(v_as_928_, v_i_929_, v_k_930_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_i_929_, v___x_940_);
lean_dec(v_i_929_);
v___x_942_ = lean_nat_add(v_k_930_, v___x_940_);
lean_dec(v_k_930_);
v_as_928_ = v___x_939_;
v_i_929_ = v___x_941_;
v_k_930_ = v___x_942_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg___boxed(lean_object* v_hi_944_, lean_object* v_pivot_945_, lean_object* v_as_946_, lean_object* v_i_947_, lean_object* v_k_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_944_, v_pivot_945_, v_as_946_, v_i_947_, v_k_948_);
lean_dec_ref(v_pivot_945_);
lean_dec(v_hi_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_n_950_, lean_object* v_as_951_, lean_object* v_lo_952_, lean_object* v_hi_953_){
_start:
{
lean_object* v___y_955_; uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_lt(v_lo_952_, v_hi_953_);
if (v___x_965_ == 0)
{
lean_dec(v_lo_952_);
return v_as_951_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_mid_968_; lean_object* v___y_970_; lean_object* v___y_976_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_966_ = lean_nat_add(v_lo_952_, v_hi_953_);
v___x_967_ = lean_unsigned_to_nat(1u);
v_mid_968_ = lean_nat_shiftr(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
v___x_981_ = lean_array_fget_borrowed(v_as_951_, v_mid_968_);
v___x_982_ = lean_array_fget_borrowed(v_as_951_, v_lo_952_);
v___x_983_ = l_Lean_StructureFieldInfo_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
v___y_976_ = v_as_951_;
goto v___jp_975_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = lean_array_fswap(v_as_951_, v_lo_952_, v_mid_968_);
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_fget_borrowed(v___y_970_, v_mid_968_);
v___x_972_ = lean_array_fget_borrowed(v___y_970_, v_hi_953_);
v___x_973_ = l_Lean_StructureFieldInfo_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v_mid_968_);
v___y_955_ = v___y_970_;
goto v___jp_954_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_fswap(v___y_970_, v_mid_968_, v_hi_953_);
lean_dec(v_mid_968_);
v___y_955_ = v___x_974_;
goto v___jp_954_;
}
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_array_fget_borrowed(v___y_976_, v_hi_953_);
v___x_978_ = lean_array_fget_borrowed(v___y_976_, v_lo_952_);
v___x_979_ = l_Lean_StructureFieldInfo_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
v___y_970_ = v___y_976_;
goto v___jp_969_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_array_fswap(v___y_976_, v_lo_952_, v_hi_953_);
v___y_970_ = v___x_980_;
goto v___jp_969_;
}
}
}
v___jp_954_:
{
lean_object* v_pivot_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; uint8_t v___x_960_; 
v_pivot_956_ = lean_array_fget(v___y_955_, v_hi_953_);
lean_inc_n(v_lo_952_, 2);
v___x_957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_953_, v_pivot_956_, v___y_955_, v_lo_952_, v_lo_952_);
lean_dec(v_pivot_956_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_957_);
v___x_960_ = lean_nat_dec_le(v_hi_953_, v_fst_958_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_950_, v_snd_959_, v_lo_952_, v_fst_958_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_fst_958_, v___x_962_);
lean_dec(v_fst_958_);
v_as_951_ = v___x_961_;
v_lo_952_ = v___x_963_;
goto _start;
}
else
{
lean_dec(v_fst_958_);
lean_dec(v_lo_952_);
return v_snd_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_n_985_, lean_object* v_as_986_, lean_object* v_lo_987_, lean_object* v_hi_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_985_, v_as_986_, v_lo_987_, v_hi_988_);
lean_dec(v_hi_988_);
lean_dec(v_n_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_992_, lean_object* v_e_993_){
_start:
{
lean_object* v_structName_994_; lean_object* v_fields_995_; lean_object* v___x_996_; size_t v_sz_997_; size_t v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_structName_994_ = lean_ctor_get(v_e_993_, 0);
lean_inc(v_structName_994_);
v_fields_995_ = lean_ctor_get(v_e_993_, 1);
lean_inc_ref_n(v_fields_995_, 2);
lean_dec_ref(v_e_993_);
v___x_996_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_997_ = lean_array_size(v_fields_995_);
v___x_998_ = ((size_t)0ULL);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_997_, v___x_998_, v_fields_995_);
v___x_1008_ = lean_array_get_size(v_fields_995_);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_dec_eq(v___x_1008_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___y_1018_; uint8_t v___x_1020_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_sub(v___x_1008_, v___x_1015_);
v___x_1020_ = lean_nat_dec_le(v___x_1013_, v___x_1016_);
if (v___x_1020_ == 0)
{
lean_inc(v___x_1016_);
v___y_1018_ = v___x_1016_;
goto v___jp_1017_;
}
else
{
v___y_1018_ = v___x_1013_;
goto v___jp_1017_;
}
v___jp_1017_:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v___y_1018_, v___x_1016_);
if (v___x_1019_ == 0)
{
lean_dec(v___x_1016_);
lean_inc(v___y_1018_);
v___y_1010_ = v___y_1018_;
v___y_1011_ = v___y_1018_;
goto v___jp_1009_;
}
else
{
v___y_1010_ = v___y_1018_;
v___y_1011_ = v___x_1016_;
goto v___jp_1009_;
}
}
}
else
{
v___y_1001_ = v_fields_995_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v_toEnvExtension_1002_; lean_object* v_asyncMode_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_toEnvExtension_1002_ = lean_ctor_get(v___x_996_, 0);
v_asyncMode_1003_ = lean_ctor_get(v_toEnvExtension_1002_, 2);
v___x_1004_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_1005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1005_, 0, v_structName_994_);
lean_ctor_set(v___x_1005_, 1, v___x_999_);
lean_ctor_set(v___x_1005_, 2, v___y_1001_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_996_, v_env_992_, v___x_1005_, v_asyncMode_1003_, v___x_1006_);
return v___x_1007_;
}
v___jp_1009_:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v___x_1008_, v_fields_995_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
v___y_1001_ = v___x_1012_;
goto v___jp_1000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_1021_, lean_object* v_as_1022_, lean_object* v_lo_1023_, lean_object* v_hi_1024_, lean_object* v_w_1025_, lean_object* v_hlo_1026_, lean_object* v_hhi_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_n_1021_, v_as_1022_, v_lo_1023_, v_hi_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_1029_, lean_object* v_as_1030_, lean_object* v_lo_1031_, lean_object* v_hi_1032_, lean_object* v_w_1033_, lean_object* v_hlo_1034_, lean_object* v_hhi_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_1029_, v_as_1030_, v_lo_1031_, v_hi_1032_, v_w_1033_, v_hlo_1034_, v_hhi_1035_);
lean_dec(v_hi_1032_);
lean_dec(v_n_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(lean_object* v_n_1037_, lean_object* v_lo_1038_, lean_object* v_hi_1039_, lean_object* v_hhi_1040_, lean_object* v_pivot_1041_, lean_object* v_as_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_, lean_object* v_ilo_1045_, lean_object* v_ik_1046_, lean_object* v_w_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___redArg(v_hi_1039_, v_pivot_1041_, v_as_1042_, v_i_1043_, v_k_1044_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1___boxed(lean_object* v_n_1049_, lean_object* v_lo_1050_, lean_object* v_hi_1051_, lean_object* v_hhi_1052_, lean_object* v_pivot_1053_, lean_object* v_as_1054_, lean_object* v_i_1055_, lean_object* v_k_1056_, lean_object* v_ilo_1057_, lean_object* v_ik_1058_, lean_object* v_w_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1_spec__1(v_n_1049_, v_lo_1050_, v_hi_1051_, v_hhi_1052_, v_pivot_1053_, v_as_1054_, v_i_1055_, v_k_1056_, v_ilo_1057_, v_ik_1058_, v_w_1059_);
lean_dec_ref(v_pivot_1053_);
lean_dec(v_hi_1051_);
lean_dec(v_lo_1050_);
lean_dec(v_n_1049_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_1061_, lean_object* v_parentInfo_1062_, lean_object* v___x_1063_, lean_object* v_asyncMode_1064_, lean_object* v___x_1065_, lean_object* v_env_1066_){
_start:
{
lean_object* v_structName_1067_; lean_object* v_fieldNames_1068_; lean_object* v_fieldInfo_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1077_; 
v_structName_1067_ = lean_ctor_get(v_val_1061_, 0);
v_fieldNames_1068_ = lean_ctor_get(v_val_1061_, 1);
v_fieldInfo_1069_ = lean_ctor_get(v_val_1061_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_val_1061_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_val_1061_, 3);
lean_dec(v_unused_1078_);
v___x_1071_ = v_val_1061_;
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_fieldInfo_1069_);
lean_inc(v_fieldNames_1068_);
lean_inc(v_structName_1067_);
lean_dec(v_val_1061_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 3, v_parentInfo_1062_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_structName_1067_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_fieldNames_1068_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_fieldInfo_1069_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_parentInfo_1062_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1063_, v_env_1066_, v___x_1074_, v_asyncMode_1064_, v___x_1065_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_1079_, lean_object* v_parentInfo_1080_, lean_object* v___x_1081_, lean_object* v_asyncMode_1082_, lean_object* v___x_1083_, lean_object* v_env_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_setStructureParents___redArg___lam__0(v_val_1079_, v_parentInfo_1080_, v___x_1081_, v_asyncMode_1082_, v___x_1083_, v_env_1084_);
lean_dec(v_asyncMode_1082_);
return v_res_1085_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v_structName_1095_, lean_object* v_parentInfo_1096_, lean_object* v_modifyEnv_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_____do__lift_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v_toEnvExtension_1102_; lean_object* v_asyncMode_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_snd_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1122_; 
v___x_1101_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1102_ = lean_ctor_get(v___x_1101_, 0);
v_asyncMode_1103_ = lean_ctor_get(v_toEnvExtension_1102_, 2);
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1092_, v___x_1101_, v_____do__lift_1100_, v_asyncMode_1103_, v___x_1104_);
v_snd_1106_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1105_, 0);
lean_dec(v_unused_1123_);
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1122_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snd_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1122_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; 
lean_inc(v_structName_1095_);
v___x_1110_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1093_, v___x_1094_, v_snd_1106_, v_structName_1095_);
lean_dec(v_snd_1106_);
if (lean_obj_tag(v___x_1110_) == 1)
{
lean_object* v_val_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; 
lean_del_object(v___x_1108_);
lean_dec_ref(v_inst_1099_);
lean_dec_ref(v_inst_1098_);
lean_dec(v_structName_1095_);
v_val_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v___x_1110_, 1);
lean_inc(v_asyncMode_1103_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1112_, 0, v_val_1111_);
lean_closure_set(v___f_1112_, 1, v_parentInfo_1096_);
lean_closure_set(v___f_1112_, 2, v___x_1101_);
lean_closure_set(v___f_1112_, 3, v_asyncMode_1103_);
lean_closure_set(v___f_1112_, 4, v___x_1104_);
v___x_1113_ = lean_apply_1(v_modifyEnv_1097_, v___f_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_dec(v___x_1110_);
lean_dec(v_modifyEnv_1097_);
lean_dec_ref(v_parentInfo_1096_);
v___x_1114_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_1115_ = l_Lean_MessageData_ofName(v_structName_1095_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 7);
lean_ctor_set(v___x_1108_, 1, v___x_1115_);
lean_ctor_set(v___x_1108_, 0, v___x_1114_);
v___x_1117_ = v___x_1108_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_throwError___redArg(v_inst_1098_, v_inst_1099_, v___x_1119_);
return v___x_1120_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_instInhabitedStructureState_default;
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_structName_1132_, lean_object* v_parentInfo_1133_){
_start:
{
lean_object* v_toBind_1134_; lean_object* v_getEnv_1135_; lean_object* v_modifyEnv_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v_toBind_1134_ = lean_ctor_get(v_inst_1129_, 1);
lean_inc(v_toBind_1134_);
v_getEnv_1135_ = lean_ctor_get(v_inst_1130_, 0);
lean_inc(v_getEnv_1135_);
v_modifyEnv_1136_ = lean_ctor_get(v_inst_1130_, 1);
lean_inc(v_modifyEnv_1136_);
lean_dec_ref(v_inst_1130_);
v___x_1137_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1138_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1139_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1140_, 0, v___x_1139_);
lean_closure_set(v___f_1140_, 1, v___x_1137_);
lean_closure_set(v___f_1140_, 2, v___x_1138_);
lean_closure_set(v___f_1140_, 3, v_structName_1132_);
lean_closure_set(v___f_1140_, 4, v_parentInfo_1133_);
lean_closure_set(v___f_1140_, 5, v_modifyEnv_1136_);
lean_closure_set(v___f_1140_, 6, v_inst_1129_);
lean_closure_set(v___f_1140_, 7, v_inst_1131_);
v___x_1141_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v_getEnv_1135_, v___f_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_structName_1146_, lean_object* v_parentInfo_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_setStructureParents___redArg(v_inst_1143_, v_inst_1144_, v_inst_1145_, v_structName_1146_, v_parentInfo_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1149_, lean_object* v_k_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_m_1155_; lean_object* v_a_1156_; uint8_t v___x_1157_; 
v___x_1153_ = lean_nat_add(v_x_1151_, v_x_1152_);
v___x_1154_ = lean_unsigned_to_nat(1u);
v_m_1155_ = lean_nat_shiftr(v___x_1153_, v___x_1154_);
lean_dec(v___x_1153_);
v_a_1156_ = lean_array_fget_borrowed(v_as_1149_, v_m_1155_);
v___x_1157_ = l_Lean_StructureInfo_lt(v_a_1156_, v_k_1150_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; 
lean_dec(v_x_1152_);
v___x_1158_ = l_Lean_StructureInfo_lt(v_k_1150_, v_a_1156_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_m_1155_);
lean_dec(v_x_1151_);
lean_inc(v_a_1156_);
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_a_1156_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; uint8_t v___y_1164_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_nat_dec_eq(v_m_1155_, v___x_1160_);
v___x_1162_ = lean_nat_sub(v_m_1155_, v___x_1154_);
lean_dec(v_m_1155_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_nat_dec_lt(v___x_1162_, v_x_1151_);
v___y_1164_ = v___x_1167_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v___x_1161_;
goto v___jp_1163_;
}
v___jp_1163_:
{
if (v___y_1164_ == 0)
{
v_x_1152_ = v___x_1162_;
goto _start;
}
else
{
lean_object* v___x_1166_; 
lean_dec(v___x_1162_);
lean_dec(v_x_1151_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
}
}
}
else
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
lean_dec(v_x_1151_);
v___x_1168_ = lean_nat_add(v_m_1155_, v___x_1154_);
lean_dec(v_m_1155_);
v___x_1169_ = lean_nat_dec_le(v___x_1168_, v_x_1152_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
lean_dec(v___x_1168_);
lean_dec(v_x_1152_);
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
else
{
v_x_1151_ = v___x_1168_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1172_, lean_object* v_k_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1172_, v_k_1173_, v_x_1174_, v_x_1175_);
lean_dec_ref(v_k_1173_);
lean_dec_ref(v_as_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1177_, lean_object* v_vals_1178_, lean_object* v_i_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_keys_1177_);
v___x_1182_ = lean_nat_dec_lt(v_i_1179_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_i_1179_);
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v_k_x27_1184_; uint8_t v___x_1185_; 
v_k_x27_1184_ = lean_array_fget_borrowed(v_keys_1177_, v_i_1179_);
v___x_1185_ = lean_name_eq(v_k_1180_, v_k_x27_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_i_1179_, v___x_1186_);
lean_dec(v_i_1179_);
v_i_1179_ = v___x_1187_;
goto _start;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_array_fget_borrowed(v_vals_1178_, v_i_1179_);
lean_dec(v_i_1179_);
lean_inc(v___x_1189_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1191_, lean_object* v_vals_1192_, lean_object* v_i_1193_, lean_object* v_k_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1191_, v_vals_1192_, v_i_1193_, v_k_1194_);
lean_dec(v_k_1194_);
lean_dec_ref(v_vals_1192_);
lean_dec_ref(v_keys_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1196_, size_t v_x_1197_, lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
lean_object* v_es_1199_; lean_object* v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; lean_object* v_j_1203_; lean_object* v___x_1204_; 
v_es_1199_ = lean_ctor_get(v_x_1196_, 0);
v___x_1200_ = lean_box(2);
v___x_1201_ = ((size_t)31ULL);
v___x_1202_ = lean_usize_land(v_x_1197_, v___x_1201_);
v_j_1203_ = lean_usize_to_nat(v___x_1202_);
v___x_1204_ = lean_array_get_borrowed(v___x_1200_, v_es_1199_, v_j_1203_);
lean_dec(v_j_1203_);
switch(lean_obj_tag(v___x_1204_))
{
case 0:
{
lean_object* v_key_1205_; lean_object* v_val_1206_; uint8_t v___x_1207_; 
v_key_1205_ = lean_ctor_get(v___x_1204_, 0);
v_val_1206_ = lean_ctor_get(v___x_1204_, 1);
v___x_1207_ = lean_name_eq(v_x_1198_, v_key_1205_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; 
lean_inc(v_val_1206_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_val_1206_);
return v___x_1209_;
}
}
case 1:
{
lean_object* v_node_1210_; size_t v___x_1211_; size_t v___x_1212_; 
v_node_1210_ = lean_ctor_get(v___x_1204_, 0);
v___x_1211_ = ((size_t)5ULL);
v___x_1212_ = lean_usize_shift_right(v_x_1197_, v___x_1211_);
v_x_1196_ = v_node_1210_;
v_x_1197_ = v___x_1212_;
goto _start;
}
default: 
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_box(0);
return v___x_1214_;
}
}
}
else
{
lean_object* v_ks_1215_; lean_object* v_vs_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_ks_1215_ = lean_ctor_get(v_x_1196_, 0);
v_vs_1216_ = lean_ctor_get(v_x_1196_, 1);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1215_, v_vs_1216_, v___x_1217_, v_x_1198_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_){
_start:
{
size_t v_x_412__boxed_1222_; lean_object* v_res_1223_; 
v_x_412__boxed_1222_ = lean_unbox_usize(v_x_1220_);
lean_dec(v_x_1220_);
v_res_1223_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1219_, v_x_412__boxed_1222_, v_x_1221_);
lean_dec(v_x_1221_);
lean_dec_ref(v_x_1219_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
uint64_t v___y_1227_; 
if (lean_obj_tag(v_x_1225_) == 0)
{
uint64_t v___x_1230_; 
v___x_1230_ = 1723ULL;
v___y_1227_ = v___x_1230_;
goto v___jp_1226_;
}
else
{
uint64_t v_hash_1231_; 
v_hash_1231_ = lean_ctor_get_uint64(v_x_1225_, sizeof(void*)*2);
v___y_1227_ = v_hash_1231_;
goto v___jp_1226_;
}
v___jp_1226_:
{
size_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_uint64_to_usize(v___y_1227_);
v___x_1229_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1224_, v___x_1228_, v_x_1225_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1232_, v_x_1233_);
lean_dec(v_x_1233_);
lean_dec_ref(v_x_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1235_, lean_object* v_structName_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1238_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1235_, v_structName_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; lean_object* v_toEnvExtension_1240_; lean_object* v_asyncMode_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_snd_1244_; lean_object* v___x_1245_; 
v___x_1239_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1240_ = lean_ctor_get(v___x_1239_, 0);
v_asyncMode_1241_ = lean_ctor_get(v_toEnvExtension_1240_, 2);
v___x_1242_ = lean_box(0);
v___x_1243_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1237_, v___x_1239_, v_env_1235_, v_asyncMode_1241_, v___x_1242_);
v_snd_1244_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1244_);
lean_dec(v___x_1243_);
v___x_1245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1244_, v_structName_1236_);
lean_dec(v_structName_1236_);
lean_dec(v_snd_1244_);
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_val_1246_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1247_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1248_ = 0;
v___x_1249_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1237_, v___x_1247_, v_env_1235_, v_val_1246_, v___x_1248_);
lean_dec(v_val_1246_);
lean_dec_ref(v_env_1235_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v___x_1249_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v___x_1249_);
lean_dec(v_structName_1236_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_sub(v___x_1251_, v___x_1254_);
v___x_1256_ = lean_nat_dec_le(v___x_1250_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec(v___x_1255_);
lean_dec_ref(v___x_1249_);
lean_dec(v_structName_1236_);
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1259_, 0, v_structName_1236_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
v___x_1260_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1249_, v___x_1259_, v___x_1250_, v___x_1255_);
lean_dec_ref_known(v___x_1259_, 4);
lean_dec_ref(v___x_1249_);
return v___x_1260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1265_, v_x_1266_, v_x_1267_);
lean_dec(v_x_1267_);
lean_dec_ref(v_x_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1269_, lean_object* v_k_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1269_, v_k_1270_, v_x_1271_, v_x_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1275_, lean_object* v_k_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1275_, v_k_1276_, v_x_1277_, v_x_1278_, v_x_1279_);
lean_dec_ref(v_k_1276_);
lean_dec_ref(v_as_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, size_t v_x_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1282_, v_x_1283_, v_x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
size_t v_x_543__boxed_1290_; lean_object* v_res_1291_; 
v_x_543__boxed_1290_ = lean_unbox_usize(v_x_1288_);
lean_dec(v_x_1288_);
v_res_1291_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1286_, v_x_1287_, v_x_543__boxed_1290_, v_x_1289_);
lean_dec(v_x_1289_);
lean_dec_ref(v_x_1287_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1292_, lean_object* v_keys_1293_, lean_object* v_vals_1294_, lean_object* v_heq_1295_, lean_object* v_i_1296_, lean_object* v_k_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1293_, v_vals_1294_, v_i_1296_, v_k_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1299_, lean_object* v_keys_1300_, lean_object* v_vals_1301_, lean_object* v_heq_1302_, lean_object* v_i_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1299_, v_keys_1300_, v_vals_1301_, v_heq_1302_, v_i_1303_, v_k_1304_);
lean_dec(v_k_1304_);
lean_dec_ref(v_vals_1301_);
lean_dec_ref(v_keys_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1306_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1308_ = lean_panic_fn_borrowed(v___x_1307_, v_msg_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1313_ = lean_unsigned_to_nat(4u);
v___x_1314_ = lean_unsigned_to_nat(139u);
v___x_1315_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1316_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1317_ = l_mkPanicMessageWithDecl(v___x_1316_, v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1318_, lean_object* v_structName_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_getStructureInfo_x3f(v_env_1318_, v_structName_1319_);
if (lean_obj_tag(v___x_1320_) == 1)
{
lean_object* v_val_1321_; 
v_val_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v___x_1320_, 1);
return v_val_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v___x_1320_);
v___x_1322_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1323_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1322_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1326_ = lean_panic_fn_borrowed(v___x_1325_, v_msg_1324_);
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1328_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1329_ = lean_unsigned_to_nat(9u);
v___x_1330_ = lean_unsigned_to_nat(154u);
v___x_1331_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1332_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1333_ = l_mkPanicMessageWithDecl(v___x_1332_, v___x_1331_, v___x_1330_, v___x_1329_, v___x_1328_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1335_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1336_ = lean_unsigned_to_nat(11u);
v___x_1337_ = lean_unsigned_to_nat(153u);
v___x_1338_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1339_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1340_ = l_mkPanicMessageWithDecl(v___x_1339_, v___x_1338_, v___x_1337_, v___x_1336_, v___x_1335_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1341_, lean_object* v_constName_1342_){
_start:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = 0;
lean_inc_ref(v_env_1341_);
v___x_1350_ = l_Lean_Environment_find_x3f(v_env_1341_, v_constName_1342_, v___x_1349_);
if (lean_obj_tag(v___x_1350_) == 1)
{
lean_object* v_val_1351_; 
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1350_, 1);
if (lean_obj_tag(v_val_1351_) == 5)
{
lean_object* v_val_1352_; lean_object* v_ctors_1353_; 
v_val_1352_ = lean_ctor_get(v_val_1351_, 0);
lean_inc_ref(v_val_1352_);
lean_dec_ref_known(v_val_1351_, 1);
v_ctors_1353_ = lean_ctor_get(v_val_1352_, 4);
lean_inc(v_ctors_1353_);
lean_dec_ref(v_val_1352_);
if (lean_obj_tag(v_ctors_1353_) == 1)
{
lean_object* v_tail_1354_; 
v_tail_1354_ = lean_ctor_get(v_ctors_1353_, 1);
if (lean_obj_tag(v_tail_1354_) == 0)
{
lean_object* v_head_1355_; lean_object* v___x_1356_; 
v_head_1355_ = lean_ctor_get(v_ctors_1353_, 0);
lean_inc(v_head_1355_);
lean_dec_ref_known(v_ctors_1353_, 2);
v___x_1356_ = l_Lean_Environment_find_x3f(v_env_1341_, v_head_1355_, v___x_1349_);
if (lean_obj_tag(v___x_1356_) == 1)
{
lean_object* v_val_1357_; 
v_val_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1356_, 1);
if (lean_obj_tag(v_val_1357_) == 6)
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v_val_1357_, 0);
lean_inc_ref(v_val_1358_);
lean_dec_ref_known(v_val_1357_, 1);
return v_val_1358_;
}
else
{
lean_dec(v_val_1357_);
goto v___jp_1346_;
}
}
else
{
lean_dec(v___x_1356_);
goto v___jp_1346_;
}
}
else
{
lean_dec_ref_known(v_ctors_1353_, 2);
lean_dec_ref(v_env_1341_);
goto v___jp_1343_;
}
}
else
{
lean_dec(v_ctors_1353_);
lean_dec_ref(v_env_1341_);
goto v___jp_1343_;
}
}
else
{
lean_dec(v_val_1351_);
lean_dec_ref(v_env_1341_);
goto v___jp_1343_;
}
}
else
{
lean_dec(v___x_1350_);
lean_dec_ref(v_env_1341_);
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1345_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1344_);
return v___x_1345_;
}
v___jp_1346_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1348_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1347_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1359_, lean_object* v_structName_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v_fieldNames_1362_; 
v___x_1361_ = l_Lean_getStructureInfo(v_env_1359_, v_structName_1360_);
v_fieldNames_1362_ = lean_ctor_get(v___x_1361_, 1);
lean_inc_ref(v_fieldNames_1362_);
lean_dec_ref(v___x_1361_);
return v_fieldNames_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1363_, lean_object* v_structName_1364_, lean_object* v_fieldName_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_getStructureInfo_x3f(v_env_1363_, v_structName_1364_);
if (lean_obj_tag(v___x_1366_) == 1)
{
lean_object* v_val_1367_; lean_object* v_fieldInfo_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_fieldInfo_1368_ = lean_ctor_get(v_val_1367_, 2);
lean_inc_ref(v_fieldInfo_1368_);
lean_dec(v_val_1367_);
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_array_get_size(v_fieldInfo_1368_);
v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_fieldInfo_1368_);
lean_dec(v_fieldName_1365_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_sub(v___x_1370_, v___x_1373_);
v___x_1375_ = lean_nat_dec_le(v___x_1369_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec(v___x_1374_);
lean_dec_ref(v_fieldInfo_1368_);
lean_dec(v_fieldName_1365_);
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_box(0);
v___x_1379_ = 0;
v___x_1380_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1380_, 0, v_fieldName_1365_);
lean_ctor_set(v___x_1380_, 1, v___x_1377_);
lean_ctor_set(v___x_1380_, 2, v___x_1378_);
lean_ctor_set(v___x_1380_, 3, v___x_1378_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*4, v___x_1379_);
v___x_1381_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1368_, v___x_1380_, v___x_1369_, v___x_1374_);
lean_dec_ref_known(v___x_1380_, 4);
lean_dec_ref(v_fieldInfo_1368_);
return v___x_1381_;
}
}
}
else
{
lean_object* v___x_1382_; 
lean_dec(v___x_1366_);
lean_dec(v_fieldName_1365_);
v___x_1382_ = lean_box(0);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1383_, lean_object* v_structName_1384_, lean_object* v_fieldName_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_getFieldInfo_x3f(v_env_1383_, v_structName_1384_, v_fieldName_1385_);
if (lean_obj_tag(v___x_1386_) == 1)
{
lean_object* v_val_1387_; lean_object* v_subobject_x3f_1388_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v_subobject_x3f_1388_ = lean_ctor_get(v_val_1387_, 2);
lean_inc(v_subobject_x3f_1388_);
lean_dec(v_val_1387_);
return v_subobject_x3f_1388_;
}
else
{
lean_object* v___x_1389_; 
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1390_, lean_object* v_structName_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v_parentInfo_1393_; 
v___x_1392_ = l_Lean_getStructureInfo(v_env_1390_, v_structName_1391_);
v_parentInfo_1393_ = lean_ctor_get(v___x_1392_, 3);
lean_inc_ref(v_parentInfo_1393_);
lean_dec_ref(v___x_1392_);
return v_parentInfo_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1394_, lean_object* v_structName_1395_, lean_object* v_as_1396_, size_t v_i_1397_, size_t v_stop_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v___y_1401_; uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_eq(v_i_1397_, v_stop_1398_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_array_uget_borrowed(v_as_1396_, v_i_1397_);
lean_inc(v___x_1406_);
lean_inc(v_structName_1395_);
lean_inc_ref(v_env_1394_);
v___x_1407_ = l_Lean_isSubobjectField_x3f(v_env_1394_, v_structName_1395_, v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
v___y_1401_ = v_b_1399_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1408_; lean_object* v___x_1409_; 
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = lean_array_push(v_b_1399_, v_val_1408_);
v___y_1401_ = v___x_1409_;
goto v___jp_1400_;
}
}
else
{
lean_dec(v_structName_1395_);
lean_dec_ref(v_env_1394_);
return v_b_1399_;
}
v___jp_1400_:
{
size_t v___x_1402_; size_t v___x_1403_; 
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = lean_usize_add(v_i_1397_, v___x_1402_);
v_i_1397_ = v___x_1403_;
v_b_1399_ = v___y_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1410_, lean_object* v_structName_1411_, lean_object* v_as_1412_, lean_object* v_i_1413_, lean_object* v_stop_1414_, lean_object* v_b_1415_){
_start:
{
size_t v_i_boxed_1416_; size_t v_stop_boxed_1417_; lean_object* v_res_1418_; 
v_i_boxed_1416_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_stop_boxed_1417_ = lean_unbox_usize(v_stop_1414_);
lean_dec(v_stop_1414_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1410_, v_structName_1411_, v_as_1412_, v_i_boxed_1416_, v_stop_boxed_1417_, v_b_1415_);
lean_dec_ref(v_as_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1419_, lean_object* v_structName_1420_, lean_object* v_as_1421_, lean_object* v_start_1422_, lean_object* v_stop_1423_){
_start:
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1425_ = lean_nat_dec_lt(v_start_1422_, v_stop_1423_);
if (v___x_1425_ == 0)
{
lean_dec(v_structName_1420_);
lean_dec_ref(v_env_1419_);
return v___x_1424_;
}
else
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_array_get_size(v_as_1421_);
v___x_1427_ = lean_nat_dec_le(v_stop_1423_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_lt(v_start_1422_, v___x_1426_);
if (v___x_1428_ == 0)
{
lean_dec(v_structName_1420_);
lean_dec_ref(v_env_1419_);
return v___x_1424_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = lean_usize_of_nat(v_start_1422_);
v___x_1430_ = lean_usize_of_nat(v___x_1426_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1419_, v_structName_1420_, v_as_1421_, v___x_1429_, v___x_1430_, v___x_1424_);
return v___x_1431_;
}
}
else
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_usize_of_nat(v_start_1422_);
v___x_1433_ = lean_usize_of_nat(v_stop_1423_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1419_, v_structName_1420_, v_as_1421_, v___x_1432_, v___x_1433_, v___x_1424_);
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1435_, lean_object* v_structName_1436_, lean_object* v_as_1437_, lean_object* v_start_1438_, lean_object* v_stop_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1435_, v_structName_1436_, v_as_1437_, v_start_1438_, v_stop_1439_);
lean_dec(v_stop_1439_);
lean_dec(v_start_1438_);
lean_dec_ref(v_as_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1441_, lean_object* v_structName_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_inc(v_structName_1442_);
lean_inc_ref(v_env_1441_);
v___x_1443_ = l_Lean_getStructureFields(v_env_1441_, v_structName_1442_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_array_get_size(v___x_1443_);
v___x_1446_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1441_, v_structName_1442_, v___x_1443_, v___x_1444_, v___x_1445_);
lean_dec_ref(v___x_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1447_, lean_object* v_as_1448_, size_t v_i_1449_, size_t v_stop_1450_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_eq(v_i_1449_, v_stop_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_array_uget_borrowed(v_as_1448_, v_i_1449_);
v___x_1453_ = lean_name_eq(v_a_1447_, v___x_1452_);
if (v___x_1453_ == 0)
{
size_t v___x_1454_; size_t v___x_1455_; 
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1449_, v___x_1454_);
v_i_1449_ = v___x_1455_;
goto _start;
}
else
{
return v___x_1453_;
}
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = 0;
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1458_, lean_object* v_as_1459_, lean_object* v_i_1460_, lean_object* v_stop_1461_){
_start:
{
size_t v_i_boxed_1462_; size_t v_stop_boxed_1463_; uint8_t v_res_1464_; lean_object* v_r_1465_; 
v_i_boxed_1462_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_stop_boxed_1463_ = lean_unbox_usize(v_stop_1461_);
lean_dec(v_stop_1461_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1458_, v_as_1459_, v_i_boxed_1462_, v_stop_boxed_1463_);
lean_dec_ref(v_as_1459_);
lean_dec(v_a_1458_);
v_r_1465_ = lean_box(v_res_1464_);
return v_r_1465_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_array_get_size(v_as_1466_);
v___x_1470_ = lean_nat_dec_lt(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
return v___x_1470_;
}
else
{
if (v___x_1470_ == 0)
{
return v___x_1470_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1469_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1467_, v_as_1466_, v___x_1471_, v___x_1472_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_as_1474_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1481_, lean_object* v_structName_1482_, lean_object* v_fieldName_1483_){
_start:
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
lean_inc(v_structName_1482_);
lean_inc_ref(v_env_1481_);
v___x_1484_ = l_Lean_getStructureFields(v_env_1481_, v_structName_1482_);
v___x_1485_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1484_, v_fieldName_1483_);
lean_dec_ref(v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v_fst_1492_; 
lean_inc_ref(v_env_1481_);
v___x_1486_ = l_Lean_getStructureSubobjects(v_env_1481_, v_structName_1482_);
v___x_1487_ = lean_box(0);
v___x_1488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1489_ = lean_array_size(v___x_1486_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1481_, v_fieldName_1483_, v___x_1486_, v_sz_1489_, v___x_1490_, v___x_1488_);
lean_dec_ref(v___x_1486_);
v_fst_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_fst_1492_);
lean_dec_ref(v___x_1491_);
if (lean_obj_tag(v_fst_1492_) == 0)
{
return v___x_1487_;
}
else
{
lean_object* v_val_1493_; 
v_val_1493_ = lean_ctor_get(v_fst_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v_fst_1492_, 1);
return v_val_1493_;
}
}
else
{
lean_object* v___x_1494_; 
lean_dec_ref(v_env_1481_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_structName_1482_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1495_, lean_object* v_fieldName_1496_, lean_object* v_as_1497_, size_t v_sz_1498_, size_t v_i_1499_, lean_object* v_b_1500_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_lt(v_i_1499_, v_sz_1498_);
if (v___x_1501_ == 0)
{
lean_dec_ref(v_env_1495_);
lean_inc_ref(v_b_1500_);
return v_b_1500_;
}
else
{
lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_box(0);
v_a_1503_ = lean_array_uget_borrowed(v_as_1497_, v_i_1499_);
lean_inc(v_a_1503_);
lean_inc_ref(v_env_1495_);
v___x_1504_ = l_Lean_findField_x3f(v_env_1495_, v_a_1503_, v_fieldName_1496_);
if (lean_obj_tag(v___x_1504_) == 1)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v_env_1495_);
v___x_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1502_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; 
lean_dec(v___x_1504_);
v___x_1507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_add(v_i_1499_, v___x_1508_);
v_i_1499_ = v___x_1509_;
v_b_1500_ = v___x_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1511_, lean_object* v_fieldName_1512_, lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1511_, v_fieldName_1512_, v_as_1513_, v_sz_boxed_1517_, v_i_boxed_1518_, v_b_1516_);
lean_dec_ref(v_b_1516_);
lean_dec_ref(v_as_1513_);
lean_dec(v_fieldName_1512_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1520_, lean_object* v_structName_1521_, lean_object* v_fieldName_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_findField_x3f(v_env_1520_, v_structName_1521_, v_fieldName_1522_);
lean_dec(v_fieldName_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1527_, lean_object* v_as_1528_, size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_b_1531_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_lt(v_i_1530_, v_sz_1529_);
if (v___x_1532_ == 0)
{
lean_inc_ref(v_b_1531_);
return v_b_1531_;
}
else
{
lean_object* v_a_1533_; lean_object* v_projFn_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_a_1533_ = lean_array_uget_borrowed(v_as_1528_, v_i_1530_);
v_projFn_1534_ = lean_ctor_get(v_a_1533_, 1);
v___x_1535_ = lean_box(0);
v___x_1536_ = l_Lean_Name_isSuffixOf(v_projName_1527_, v_projFn_1534_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; 
v___x_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1530_, v___x_1538_);
v_i_1530_ = v___x_1539_;
v_b_1531_ = v___x_1537_;
goto _start;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc(v_a_1533_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1533_);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1535_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1544_, lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_){
_start:
{
size_t v_sz_boxed_1549_; size_t v_i_boxed_1550_; lean_object* v_res_1551_; 
v_sz_boxed_1549_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1544_, v_as_1545_, v_sz_boxed_1549_, v_i_boxed_1550_, v_b_1548_);
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_as_1545_);
lean_dec(v_projName_1544_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1552_, lean_object* v_projName_1553_, lean_object* v_structName_1554_, lean_object* v_a_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_NameSet_contains(v_a_1555_, v_structName_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1581_; size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_1584_; lean_object* v_fst_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1602_; 
lean_inc(v_structName_1554_);
lean_inc_ref(v_env_1552_);
v___x_1557_ = l_Lean_getStructureParentInfo(v_env_1552_, v_structName_1554_);
v___x_1581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1582_ = lean_array_size(v___x_1557_);
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1553_, v___x_1557_, v_sz_1582_, v___x_1583_, v___x_1581_);
v_fst_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1584_, 1);
lean_dec(v_unused_1603_);
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1602_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_fst_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1602_;
goto v_resetjp_1586_;
}
v___jp_1558_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v_fst_1565_; lean_object* v_fst_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1579_; 
v___x_1559_ = l_Lean_NameSet_insert(v_a_1555_, v_structName_1554_);
v___x_1560_ = lean_box(0);
v___x_1561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1562_ = lean_array_size(v___x_1557_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1552_, v_projName_1553_, v___x_1557_, v_sz_1562_, v___x_1563_, v___x_1561_, v___x_1559_);
lean_dec_ref(v___x_1557_);
v_fst_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_fst_1565_);
v_fst_1566_ = lean_ctor_get(v_fst_1565_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_fst_1565_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_fst_1565_, 1);
lean_dec(v_unused_1580_);
v___x_1568_ = v_fst_1565_;
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_fst_1566_);
lean_dec(v_fst_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
if (lean_obj_tag(v_fst_1566_) == 0)
{
lean_object* v_snd_1570_; lean_object* v___x_1572_; 
v_snd_1570_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_snd_1570_);
lean_dec_ref(v___x_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_snd_1570_);
lean_ctor_set(v___x_1568_, 0, v___x_1560_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_snd_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v_snd_1574_; lean_object* v_val_1575_; lean_object* v___x_1577_; 
v_snd_1574_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_snd_1574_);
lean_dec_ref(v___x_1564_);
v_val_1575_ = lean_ctor_get(v_fst_1566_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v_fst_1566_, 1);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_snd_1574_);
lean_ctor_set(v___x_1568_, 0, v_val_1575_);
v___x_1577_ = v___x_1568_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_val_1575_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_snd_1574_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
v_resetjp_1586_:
{
if (lean_obj_tag(v_fst_1585_) == 0)
{
lean_del_object(v___x_1587_);
goto v___jp_1558_;
}
else
{
lean_object* v_val_1589_; 
v_val_1589_ = lean_ctor_get(v_fst_1585_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_fst_1585_, 1);
if (lean_obj_tag(v_val_1589_) == 1)
{
lean_object* v_val_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v___x_1557_);
lean_dec(v_structName_1554_);
lean_dec_ref(v_env_1552_);
v_val_1590_ = lean_ctor_get(v_val_1589_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_val_1589_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1592_ = v_val_1589_;
v_isShared_1593_ = v_isSharedCheck_1601_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_val_1590_);
lean_dec(v_val_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1601_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_structName_1594_; lean_object* v___x_1596_; 
v_structName_1594_ = lean_ctor_get(v_val_1590_, 0);
lean_inc(v_structName_1594_);
lean_dec(v_val_1590_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_structName_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_structName_1594_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 1, v_a_1555_);
lean_ctor_set(v___x_1587_, 0, v___x_1596_);
v___x_1598_ = v___x_1587_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_a_1555_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_dec(v_val_1589_);
lean_del_object(v___x_1587_);
goto v___jp_1558_;
}
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_structName_1554_);
lean_dec_ref(v_env_1552_);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v_a_1555_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1606_, lean_object* v_projName_1607_, lean_object* v_as_1608_, size_t v_sz_1609_, size_t v_i_1610_, lean_object* v_b_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_usize_dec_lt(v_i_1610_, v_sz_1609_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v_env_1606_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_b_1611_);
lean_ctor_set(v___x_1614_, 1, v___y_1612_);
return v___x_1614_;
}
else
{
lean_object* v_a_1615_; lean_object* v_structName_1616_; lean_object* v___x_1617_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_b_1611_);
v_a_1615_ = lean_array_uget_borrowed(v_as_1608_, v_i_1610_);
v_structName_1616_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_structName_1616_);
lean_inc_ref(v_env_1606_);
v___x_1617_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1606_, v_projName_1607_, v_structName_1616_, v___y_1612_);
v_fst_1618_ = lean_ctor_get(v___x_1617_, 0);
v_snd_1619_ = lean_ctor_get(v___x_1617_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1621_ = v___x_1617_;
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_inc(v_fst_1618_);
lean_dec(v___x_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_box(0);
if (lean_obj_tag(v_fst_1618_) == 1)
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
lean_dec_ref(v_env_1606_);
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_fst_1618_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v___x_1623_);
lean_ctor_set(v___x_1621_, 0, v___x_1624_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1623_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_snd_1619_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; 
lean_del_object(v___x_1621_);
lean_dec(v_fst_1618_);
v___x_1629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1610_, v___x_1630_);
v_i_1610_ = v___x_1631_;
v_b_1611_ = v___x_1629_;
v___y_1612_ = v_snd_1619_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1634_, lean_object* v_projName_1635_, lean_object* v_as_1636_, lean_object* v_sz_1637_, lean_object* v_i_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_){
_start:
{
size_t v_sz_boxed_1641_; size_t v_i_boxed_1642_; lean_object* v_res_1643_; 
v_sz_boxed_1641_ = lean_unbox_usize(v_sz_1637_);
lean_dec(v_sz_1637_);
v_i_boxed_1642_ = lean_unbox_usize(v_i_1638_);
lean_dec(v_i_1638_);
v_res_1643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1634_, v_projName_1635_, v_as_1636_, v_sz_boxed_1641_, v_i_boxed_1642_, v_b_1639_, v___y_1640_);
lean_dec_ref(v_as_1636_);
lean_dec(v_projName_1635_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1644_, lean_object* v_projName_1645_, lean_object* v_structName_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1644_, v_projName_1645_, v_structName_1646_, v_a_1647_);
lean_dec(v_projName_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1649_, lean_object* v_structName_1650_, lean_object* v_projName_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_fst_1654_; 
v___x_1652_ = l_Lean_NameSet_empty;
v___x_1653_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1649_, v_projName_1651_, v_structName_1650_, v___x_1652_);
v_fst_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_fst_1654_);
lean_dec_ref(v___x_1653_);
return v_fst_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1655_, lean_object* v_structName_1656_, lean_object* v_projName_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_findParentProjStruct_x3f(v_env_1655_, v_structName_1656_, v_projName_1657_);
lean_dec(v_projName_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1664_ = l_Lean_Name_append(v_structCtorName_1662_, v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1665_, lean_object* v_structName_1666_, uint8_t v_includeSubobjectFields_1667_, lean_object* v_as_1668_, size_t v_i_1669_, size_t v_stop_1670_, lean_object* v_b_1671_){
_start:
{
lean_object* v___y_1673_; uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_eq(v_i_1669_, v_stop_1670_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_array_uget_borrowed(v_as_1668_, v_i_1669_);
lean_inc(v___x_1678_);
lean_inc(v_structName_1666_);
lean_inc_ref(v_env_1665_);
v___x_1679_ = l_Lean_isSubobjectField_x3f(v_env_1665_, v_structName_1666_, v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
lean_inc(v___x_1678_);
v___x_1680_ = lean_array_push(v_b_1671_, v___x_1678_);
v___y_1673_ = v___x_1680_;
goto v___jp_1672_;
}
else
{
if (v_includeSubobjectFields_1667_ == 0)
{
lean_object* v_val_1681_; lean_object* v___x_1682_; 
v_val_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v___x_1679_, 1);
lean_inc_ref(v_env_1665_);
v___x_1682_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1665_, v_val_1681_, v_b_1671_, v_includeSubobjectFields_1667_);
v___y_1673_ = v___x_1682_;
goto v___jp_1672_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_val_1683_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v___x_1679_, 1);
lean_inc(v___x_1678_);
v___x_1684_ = lean_array_push(v_b_1671_, v___x_1678_);
lean_inc_ref(v_env_1665_);
v___x_1685_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1665_, v_val_1683_, v___x_1684_, v_includeSubobjectFields_1667_);
v___y_1673_ = v___x_1685_;
goto v___jp_1672_;
}
}
}
else
{
lean_dec(v_structName_1666_);
lean_dec_ref(v_env_1665_);
return v_b_1671_;
}
v___jp_1672_:
{
size_t v___x_1674_; size_t v___x_1675_; 
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1669_, v___x_1674_);
v_i_1669_ = v___x_1675_;
v_b_1671_ = v___y_1673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1686_, lean_object* v_structName_1687_, lean_object* v_fullNames_1688_, uint8_t v_includeSubobjectFields_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
lean_inc(v_structName_1687_);
lean_inc_ref(v_env_1686_);
v___x_1690_ = l_Lean_getStructureFields(v_env_1686_, v_structName_1687_);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_array_get_size(v___x_1690_);
v___x_1693_ = lean_nat_dec_lt(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_dec_ref(v___x_1690_);
lean_dec(v_structName_1687_);
lean_dec_ref(v_env_1686_);
return v_fullNames_1688_;
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_nat_dec_le(v___x_1692_, v___x_1692_);
if (v___x_1694_ == 0)
{
if (v___x_1693_ == 0)
{
lean_dec_ref(v___x_1690_);
lean_dec(v_structName_1687_);
lean_dec_ref(v_env_1686_);
return v_fullNames_1688_;
}
else
{
size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = lean_usize_of_nat(v___x_1692_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1686_, v_structName_1687_, v_includeSubobjectFields_1689_, v___x_1690_, v___x_1695_, v___x_1696_, v_fullNames_1688_);
lean_dec_ref(v___x_1690_);
return v___x_1697_;
}
}
else
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_of_nat(v___x_1692_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1686_, v_structName_1687_, v_includeSubobjectFields_1689_, v___x_1690_, v___x_1698_, v___x_1699_, v_fullNames_1688_);
lean_dec_ref(v___x_1690_);
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1701_, lean_object* v_structName_1702_, lean_object* v_fullNames_1703_, lean_object* v_includeSubobjectFields_1704_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1705_; lean_object* v_res_1706_; 
v_includeSubobjectFields_boxed_1705_ = lean_unbox(v_includeSubobjectFields_1704_);
v_res_1706_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1701_, v_structName_1702_, v_fullNames_1703_, v_includeSubobjectFields_boxed_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1707_, lean_object* v_structName_1708_, lean_object* v_includeSubobjectFields_1709_, lean_object* v_as_1710_, lean_object* v_i_1711_, lean_object* v_stop_1712_, lean_object* v_b_1713_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1714_; size_t v_i_boxed_1715_; size_t v_stop_boxed_1716_; lean_object* v_res_1717_; 
v_includeSubobjectFields_boxed_1714_ = lean_unbox(v_includeSubobjectFields_1709_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_stop_boxed_1716_ = lean_unbox_usize(v_stop_1712_);
lean_dec(v_stop_1712_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1707_, v_structName_1708_, v_includeSubobjectFields_boxed_1714_, v_as_1710_, v_i_boxed_1715_, v_stop_boxed_1716_, v_b_1713_);
lean_dec_ref(v_as_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1718_, lean_object* v_structName_1719_, uint8_t v_includeSubobjectFields_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1722_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1718_, v_structName_1719_, v___x_1721_, v_includeSubobjectFields_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1723_, lean_object* v_structName_1724_, lean_object* v_includeSubobjectFields_1725_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1726_; lean_object* v_res_1727_; 
v_includeSubobjectFields_boxed_1726_ = lean_unbox(v_includeSubobjectFields_1725_);
v_res_1727_ = l_Lean_getStructureFieldsFlattened(v_env_1723_, v_structName_1724_, v_includeSubobjectFields_boxed_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1728_, lean_object* v_constName_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_getStructureInfo_x3f(v_env_1728_, v_constName_1729_);
if (lean_obj_tag(v___x_1730_) == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = 0;
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; 
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = 1;
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1733_, lean_object* v_constName_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Lean_isStructure(v_env_1733_, v_constName_1734_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1737_, lean_object* v_structName_1738_, lean_object* v_fieldName_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_getFieldInfo_x3f(v_env_1737_, v_structName_1738_, v_fieldName_1739_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_val_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_projFn_1745_; lean_object* v___x_1747_; 
v_projFn_1745_ = lean_ctor_get(v_val_1741_, 1);
lean_inc(v_projFn_1745_);
lean_dec(v_val_1741_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_projFn_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_projFn_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1750_; 
lean_dec(v___x_1740_);
v___x_1750_ = lean_box(0);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1751_, lean_object* v_structName_1752_, lean_object* v_fieldName_1753_){
_start:
{
lean_object* v___x_1754_; 
lean_inc_ref(v_env_1751_);
v___x_1754_ = l_Lean_getProjFnForField_x3f(v_env_1751_, v_structName_1752_, v_fieldName_1753_);
if (lean_obj_tag(v___x_1754_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1756_; 
v_val_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_n(v_val_1755_, 2);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1751_, v_val_1755_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_dec(v_val_1755_);
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
else
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_val_1758_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1756_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v___x_1756_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_val_1755_);
lean_ctor_set(v___x_1762_, 1, v_val_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v___x_1754_);
lean_dec_ref(v_env_1751_);
v___x_1767_ = lean_box(0);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1771_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1773_ = l_Lean_Name_append(v_projFn_1771_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1777_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1779_ = l_Lean_Name_append(v_projFn_1777_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1780_, lean_object* v_env_1781_, lean_object* v_structName_1782_, lean_object* v_fieldName_1783_){
_start:
{
lean_object* v___x_1784_; 
lean_inc(v_fieldName_1783_);
lean_inc(v_structName_1782_);
lean_inc_ref(v_env_1781_);
v___x_1784_ = l_Lean_getProjFnForField_x3f(v_env_1781_, v_structName_1782_, v_fieldName_1783_);
if (lean_obj_tag(v___x_1784_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_fieldName_1783_);
lean_dec(v_structName_1782_);
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_val_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_defFn_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; 
v_defFn_1789_ = lean_apply_1(v_mkName_1780_, v_val_1785_);
v___x_1790_ = 1;
lean_inc(v_defFn_1789_);
v___x_1791_ = l_Lean_Environment_contains(v_env_1781_, v_defFn_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec(v_defFn_1789_);
lean_del_object(v___x_1787_);
v___x_1792_ = lean_box(0);
return v___x_1792_;
}
else
{
lean_object* v___x_1794_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_defFn_1789_);
v___x_1794_ = v___x_1787_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_defFn_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v___x_1797_; lean_object* v_defFn_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; 
lean_dec(v___x_1784_);
v___x_1797_ = l_Lean_Name_append(v_structName_1782_, v_fieldName_1783_);
v_defFn_1798_ = lean_apply_1(v_mkName_1780_, v___x_1797_);
v___x_1799_ = 1;
lean_inc(v_defFn_1798_);
v___x_1800_ = l_Lean_Environment_contains(v_env_1781_, v_defFn_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec(v_defFn_1798_);
v___x_1801_ = lean_box(0);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_defFn_1798_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1804_, lean_object* v_structName_1805_, lean_object* v_fieldName_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1808_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1807_, v_env_1804_, v_structName_1805_, v_fieldName_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1810_, lean_object* v_structName_1811_, lean_object* v_fieldName_1812_){
_start:
{
lean_object* v___x_1813_; 
lean_inc(v_fieldName_1812_);
lean_inc(v_structName_1811_);
lean_inc_ref(v_env_1810_);
v___x_1813_ = l_Lean_getDefaultFnForField_x3f(v_env_1810_, v_structName_1811_, v_fieldName_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1815_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1814_, v_env_1810_, v_structName_1811_, v_fieldName_1812_);
return v___x_1815_;
}
else
{
lean_dec(v_fieldName_1812_);
lean_dec(v_structName_1811_);
lean_dec_ref(v_env_1810_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1821_ = l_Lean_Name_append(v_projFn_1819_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1823_, lean_object* v_structName_1824_, lean_object* v_fieldName_1825_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1827_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1826_, v_env_1823_, v_structName_1824_, v_fieldName_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1828_, lean_object* v_env_1829_, lean_object* v_baseStructName_1830_, lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_snd_1835_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_array_get_size(v_as_1831_);
v___x_1840_ = lean_nat_dec_lt(v_i_1832_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec(v_i_1832_);
lean_dec_ref(v_env_1829_);
lean_dec(v_path_1828_);
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___y_1833_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v_subobject_x3f_1844_; 
v___x_1843_ = lean_array_fget_borrowed(v_as_1831_, v_i_1832_);
v_subobject_x3f_1844_ = lean_ctor_get(v___x_1843_, 2);
if (lean_obj_tag(v_subobject_x3f_1844_) == 1)
{
lean_object* v_projFn_1845_; lean_object* v_val_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_fst_1849_; 
v_projFn_1845_ = lean_ctor_get(v___x_1843_, 1);
v_val_1846_ = lean_ctor_get(v_subobject_x3f_1844_, 0);
lean_inc(v_path_1828_);
lean_inc(v_projFn_1845_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_projFn_1845_);
lean_ctor_set(v___x_1847_, 1, v_path_1828_);
lean_inc(v_val_1846_);
lean_inc_ref(v_env_1829_);
v___x_1848_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1829_, v_baseStructName_1830_, v_val_1846_, v___x_1847_, v___y_1833_);
v_fst_1849_ = lean_ctor_get(v___x_1848_, 0);
if (lean_obj_tag(v_fst_1849_) == 0)
{
lean_object* v_snd_1850_; 
v_snd_1850_ = lean_ctor_get(v___x_1848_, 1);
lean_inc(v_snd_1850_);
lean_dec_ref(v___x_1848_);
v_snd_1835_ = v_snd_1850_;
goto v___jp_1834_;
}
else
{
lean_dec(v_i_1832_);
lean_dec_ref(v_env_1829_);
lean_dec(v_path_1828_);
return v___x_1848_;
}
}
else
{
v_snd_1835_ = v___y_1833_;
goto v___jp_1834_;
}
}
v___jp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_nat_add(v_i_1832_, v___x_1836_);
lean_dec(v_i_1832_);
v_i_1832_ = v___x_1837_;
v___y_1833_ = v_snd_1835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1851_, lean_object* v_baseStructName_1852_, lean_object* v_structName_1853_, lean_object* v_path_1854_, lean_object* v_a_1855_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_name_eq(v_baseStructName_1852_, v_structName_1853_);
if (v___x_1869_ == 0)
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_NameSet_contains(v_a_1855_, v_structName_1853_);
if (v___x_1870_ == 0)
{
goto v___jp_1856_;
}
else
{
if (v___x_1869_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_path_1854_);
lean_dec(v_structName_1853_);
lean_dec_ref(v_env_1851_);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1855_);
return v___x_1872_;
}
else
{
goto v___jp_1856_;
}
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_structName_1853_);
lean_dec_ref(v_env_1851_);
v___x_1873_ = l_List_reverse___redArg(v_path_1854_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1855_);
return v___x_1875_;
}
v___jp_1856_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_inc(v_structName_1853_);
v___x_1857_ = l_Lean_NameSet_insert(v_a_1855_, v_structName_1853_);
lean_inc_ref(v_env_1851_);
v___x_1858_ = l_Lean_getStructureInfo_x3f(v_env_1851_, v_structName_1853_);
if (lean_obj_tag(v___x_1858_) == 1)
{
lean_object* v_val_1859_; lean_object* v_fieldInfo_1860_; lean_object* v_parentInfo_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_fst_1864_; 
v_val_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_val_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v_fieldInfo_1860_ = lean_ctor_get(v_val_1859_, 2);
lean_inc_ref(v_fieldInfo_1860_);
v_parentInfo_1861_ = lean_ctor_get(v_val_1859_, 3);
lean_inc_ref(v_parentInfo_1861_);
lean_dec(v_val_1859_);
v___x_1862_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1851_);
lean_inc(v_path_1854_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1854_, v_env_1851_, v_baseStructName_1852_, v_fieldInfo_1860_, v___x_1862_, v___x_1857_);
lean_dec_ref(v_fieldInfo_1860_);
v_fst_1864_ = lean_ctor_get(v___x_1863_, 0);
if (lean_obj_tag(v_fst_1864_) == 0)
{
lean_object* v_snd_1865_; lean_object* v___x_1866_; 
v_snd_1865_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_snd_1865_);
lean_dec_ref(v___x_1863_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1854_, v_env_1851_, v_baseStructName_1852_, v_parentInfo_1861_, v___x_1862_, v_snd_1865_);
lean_dec_ref(v_parentInfo_1861_);
return v___x_1866_;
}
else
{
lean_dec_ref(v_parentInfo_1861_);
lean_dec(v_path_1854_);
lean_dec_ref(v_env_1851_);
return v___x_1863_;
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec(v___x_1858_);
lean_dec(v_path_1854_);
lean_dec_ref(v_env_1851_);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1857_);
return v___x_1868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_1876_, lean_object* v_env_1877_, lean_object* v_baseStructName_1878_, lean_object* v_as_1879_, lean_object* v_i_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = lean_array_get_size(v_as_1879_);
v___x_1883_ = lean_nat_dec_lt(v_i_1880_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v_i_1880_);
lean_dec_ref(v_env_1877_);
lean_dec(v_path_1876_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___y_1881_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v_structName_1887_; lean_object* v_projFn_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_fst_1891_; 
v___x_1886_ = lean_array_fget_borrowed(v_as_1879_, v_i_1880_);
v_structName_1887_ = lean_ctor_get(v___x_1886_, 0);
v_projFn_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_path_1876_);
lean_inc(v_projFn_1888_);
v___x_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_projFn_1888_);
lean_ctor_set(v___x_1889_, 1, v_path_1876_);
lean_inc(v_structName_1887_);
lean_inc_ref(v_env_1877_);
v___x_1890_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1877_, v_baseStructName_1878_, v_structName_1887_, v___x_1889_, v___y_1881_);
v_fst_1891_ = lean_ctor_get(v___x_1890_, 0);
if (lean_obj_tag(v_fst_1891_) == 0)
{
lean_object* v_snd_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_snd_1892_ = lean_ctor_get(v___x_1890_, 1);
lean_inc(v_snd_1892_);
lean_dec_ref(v___x_1890_);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_i_1880_, v___x_1893_);
lean_dec(v_i_1880_);
v_i_1880_ = v___x_1894_;
v___y_1881_ = v_snd_1892_;
goto _start;
}
else
{
lean_dec(v_i_1880_);
lean_dec_ref(v_env_1877_);
lean_dec(v_path_1876_);
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_1896_, lean_object* v_env_1897_, lean_object* v_baseStructName_1898_, lean_object* v_as_1899_, lean_object* v_i_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1896_, v_env_1897_, v_baseStructName_1898_, v_as_1899_, v_i_1900_, v___y_1901_);
lean_dec_ref(v_as_1899_);
lean_dec(v_baseStructName_1898_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_1903_, lean_object* v_env_1904_, lean_object* v_baseStructName_1905_, lean_object* v_as_1906_, lean_object* v_i_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1903_, v_env_1904_, v_baseStructName_1905_, v_as_1906_, v_i_1907_, v___y_1908_);
lean_dec_ref(v_as_1906_);
lean_dec(v_baseStructName_1905_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_1910_, lean_object* v_baseStructName_1911_, lean_object* v_structName_1912_, lean_object* v_path_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1910_, v_baseStructName_1911_, v_structName_1912_, v_path_1913_, v_a_1914_);
lean_dec(v_baseStructName_1911_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1916_, lean_object* v_baseStructName_1917_, lean_object* v_structName_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_fst_1922_; 
v___x_1919_ = lean_box(0);
v___x_1920_ = l_Lean_NameSet_empty;
v___x_1921_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1916_, v_baseStructName_1917_, v_structName_1918_, v___x_1919_, v___x_1920_);
v_fst_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_fst_1922_);
lean_dec_ref(v___x_1921_);
return v_fst_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_1923_, lean_object* v_baseStructName_1924_, lean_object* v_structName_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_getPathToBaseStructure_x3f(v_env_1923_, v_baseStructName_1924_, v_structName_1925_);
lean_dec(v_baseStructName_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1927_, lean_object* v_constName_1928_){
_start:
{
uint8_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = 0;
v___x_1930_ = l_Lean_Environment_find_x3f(v_env_1927_, v_constName_1928_, v___x_1929_);
if (lean_obj_tag(v___x_1930_) == 1)
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1930_, 1);
if (lean_obj_tag(v_val_1931_) == 5)
{
lean_object* v_val_1932_; lean_object* v_numIndices_1933_; lean_object* v_ctors_1934_; uint8_t v_isRec_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_val_1932_ = lean_ctor_get(v_val_1931_, 0);
lean_inc_ref(v_val_1932_);
lean_dec_ref_known(v_val_1931_, 1);
v_numIndices_1933_ = lean_ctor_get(v_val_1932_, 2);
lean_inc(v_numIndices_1933_);
v_ctors_1934_ = lean_ctor_get(v_val_1932_, 4);
lean_inc(v_ctors_1934_);
v_isRec_1935_ = lean_ctor_get_uint8(v_val_1932_, sizeof(void*)*6);
lean_dec_ref(v_val_1932_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_nat_dec_eq(v_numIndices_1933_, v___x_1936_);
lean_dec(v_numIndices_1933_);
if (v___x_1937_ == 0)
{
lean_dec(v_ctors_1934_);
return v___x_1937_;
}
else
{
if (lean_obj_tag(v_ctors_1934_) == 1)
{
lean_object* v_tail_1938_; 
v_tail_1938_ = lean_ctor_get(v_ctors_1934_, 1);
lean_inc(v_tail_1938_);
lean_dec_ref_known(v_ctors_1934_, 2);
if (lean_obj_tag(v_tail_1938_) == 0)
{
if (v_isRec_1935_ == 0)
{
return v___x_1937_;
}
else
{
return v___x_1929_;
}
}
else
{
lean_dec(v_tail_1938_);
return v___x_1929_;
}
}
else
{
lean_dec(v_ctors_1934_);
return v___x_1929_;
}
}
}
else
{
lean_dec(v_val_1931_);
return v___x_1929_;
}
}
else
{
lean_dec(v___x_1930_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1939_, lean_object* v_constName_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Lean_isNonRecStructure(v_env_1939_, v_constName_1940_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_panic_fn_borrowed(v___x_1944_, v_msg_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1947_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1948_ = lean_unsigned_to_nat(11u);
v___x_1949_ = lean_unsigned_to_nat(374u);
v___x_1950_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1951_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1952_ = l_mkPanicMessageWithDecl(v___x_1951_, v___x_1950_, v___x_1949_, v___x_1948_, v___x_1947_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1953_, lean_object* v_constName_1954_){
_start:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = 0;
lean_inc_ref(v_env_1953_);
v___x_1959_ = l_Lean_Environment_find_x3f(v_env_1953_, v_constName_1954_, v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 1)
{
lean_object* v_val_1960_; 
v_val_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_val_1960_);
lean_dec_ref_known(v___x_1959_, 1);
if (lean_obj_tag(v_val_1960_) == 5)
{
lean_object* v_val_1961_; lean_object* v_numIndices_1962_; lean_object* v_ctors_1963_; uint8_t v_isRec_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_val_1961_ = lean_ctor_get(v_val_1960_, 0);
lean_inc_ref(v_val_1961_);
lean_dec_ref_known(v_val_1960_, 1);
v_numIndices_1962_ = lean_ctor_get(v_val_1961_, 2);
lean_inc(v_numIndices_1962_);
v_ctors_1963_ = lean_ctor_get(v_val_1961_, 4);
lean_inc(v_ctors_1963_);
v_isRec_1964_ = lean_ctor_get_uint8(v_val_1961_, sizeof(void*)*6);
lean_dec_ref(v_val_1961_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_nat_dec_eq(v_numIndices_1962_, v___x_1965_);
lean_dec(v_numIndices_1962_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v_ctors_1963_);
lean_dec_ref(v_env_1953_);
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
else
{
if (lean_obj_tag(v_ctors_1963_) == 1)
{
lean_object* v_tail_1968_; 
v_tail_1968_ = lean_ctor_get(v_ctors_1963_, 1);
if (lean_obj_tag(v_tail_1968_) == 0)
{
if (v_isRec_1964_ == 0)
{
lean_object* v_head_1969_; lean_object* v___x_1970_; 
v_head_1969_ = lean_ctor_get(v_ctors_1963_, 0);
lean_inc(v_head_1969_);
lean_dec_ref_known(v_ctors_1963_, 2);
v___x_1970_ = l_Lean_Environment_find_x3f(v_env_1953_, v_head_1969_, v_isRec_1964_);
if (lean_obj_tag(v___x_1970_) == 1)
{
lean_object* v_val_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
v_val_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_val_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
if (lean_obj_tag(v_val_1971_) == 6)
{
lean_object* v_val_1975_; lean_object* v___x_1977_; 
v_val_1975_ = lean_ctor_get(v_val_1971_, 0);
lean_inc_ref(v_val_1975_);
lean_dec_ref_known(v_val_1971_, 1);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_val_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_val_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
lean_del_object(v___x_1973_);
lean_dec(v_val_1971_);
goto v___jp_1955_;
}
}
}
else
{
lean_dec(v___x_1970_);
goto v___jp_1955_;
}
}
else
{
lean_object* v___x_1980_; 
lean_dec_ref_known(v_ctors_1963_, 2);
lean_dec_ref(v_env_1953_);
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
}
else
{
lean_object* v___x_1981_; 
lean_dec_ref_known(v_ctors_1963_, 2);
lean_dec_ref(v_env_1953_);
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_ctors_1963_);
lean_dec_ref(v_env_1953_);
v___x_1982_ = lean_box(0);
return v___x_1982_;
}
}
}
else
{
lean_object* v___x_1983_; 
lean_dec(v_val_1960_);
lean_dec_ref(v_env_1953_);
v___x_1983_ = lean_box(0);
return v___x_1983_;
}
}
else
{
lean_object* v___x_1984_; 
lean_dec(v___x_1959_);
lean_dec_ref(v_env_1953_);
v___x_1984_ = lean_box(0);
return v___x_1984_;
}
v___jp_1955_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1957_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1956_);
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1985_, lean_object* v_constName_1986_){
_start:
{
uint8_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = 0;
lean_inc_ref(v_env_1985_);
v___x_1988_ = l_Lean_Environment_find_x3f(v_env_1985_, v_constName_1986_, v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 1)
{
lean_object* v_val_1989_; 
v_val_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_val_1989_) == 5)
{
lean_object* v_val_1990_; lean_object* v_numIndices_1991_; lean_object* v_ctors_1992_; uint8_t v_isRec_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_val_1990_ = lean_ctor_get(v_val_1989_, 0);
lean_inc_ref(v_val_1990_);
lean_dec_ref_known(v_val_1989_, 1);
v_numIndices_1991_ = lean_ctor_get(v_val_1990_, 2);
lean_inc(v_numIndices_1991_);
v_ctors_1992_ = lean_ctor_get(v_val_1990_, 4);
lean_inc(v_ctors_1992_);
v_isRec_1993_ = lean_ctor_get_uint8(v_val_1990_, sizeof(void*)*6);
lean_dec_ref(v_val_1990_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_nat_dec_eq(v_numIndices_1991_, v___x_1994_);
lean_dec(v_numIndices_1991_);
if (v___x_1995_ == 0)
{
lean_dec(v_ctors_1992_);
lean_dec_ref(v_env_1985_);
return v___x_1994_;
}
else
{
if (lean_obj_tag(v_ctors_1992_) == 1)
{
lean_object* v_tail_1996_; 
v_tail_1996_ = lean_ctor_get(v_ctors_1992_, 1);
if (lean_obj_tag(v_tail_1996_) == 0)
{
if (v_isRec_1993_ == 0)
{
lean_object* v_head_1997_; lean_object* v___x_1998_; 
v_head_1997_ = lean_ctor_get(v_ctors_1992_, 0);
lean_inc(v_head_1997_);
lean_dec_ref_known(v_ctors_1992_, 2);
v___x_1998_ = l_Lean_Environment_find_x3f(v_env_1985_, v_head_1997_, v_isRec_1993_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; 
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_1999_);
lean_dec_ref_known(v___x_1998_, 1);
if (lean_obj_tag(v_val_1999_) == 6)
{
lean_object* v_val_2000_; lean_object* v_numFields_2001_; 
v_val_2000_ = lean_ctor_get(v_val_1999_, 0);
lean_inc_ref(v_val_2000_);
lean_dec_ref_known(v_val_1999_, 1);
v_numFields_2001_ = lean_ctor_get(v_val_2000_, 4);
lean_inc(v_numFields_2001_);
lean_dec_ref(v_val_2000_);
return v_numFields_2001_;
}
else
{
lean_dec(v_val_1999_);
return v___x_1994_;
}
}
else
{
lean_dec(v___x_1998_);
return v___x_1994_;
}
}
else
{
lean_dec_ref_known(v_ctors_1992_, 2);
lean_dec_ref(v_env_1985_);
return v___x_1994_;
}
}
else
{
lean_dec_ref_known(v_ctors_1992_, 2);
lean_dec_ref(v_env_1985_);
return v___x_1994_;
}
}
else
{
lean_dec(v_ctors_1992_);
lean_dec_ref(v_env_1985_);
return v___x_1994_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_val_1989_);
lean_dec_ref(v_env_1985_);
v___x_2002_ = lean_unsigned_to_nat(0u);
return v___x_2002_;
}
}
else
{
lean_object* v___x_2003_; 
lean_dec(v___x_1988_);
lean_dec_ref(v_env_1985_);
v___x_2003_ = lean_unsigned_to_nat(0u);
return v___x_2003_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
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
v___x_2014_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2015_, 0, v___x_2014_);
return v___f_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; 
v___f_2017_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_box(1);
v___x_2020_ = lean_box(0);
v___x_2021_ = 0;
v___x_2022_ = l_Lean_registerEnvExtension___redArg(v___f_2017_, v___x_2018_, v___x_2019_, v___x_2020_, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2025_, lean_object* v_structName_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v_asyncMode_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2027_ = l_Lean_structureResolutionExt;
v_asyncMode_2028_ = lean_ctor_get(v___x_2027_, 2);
v___x_2029_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2030_ = lean_box(0);
v___x_2031_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2029_, v___x_2027_, v_env_2025_, v_asyncMode_2028_, v___x_2030_);
v___x_2032_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2031_, v_structName_2026_);
lean_dec(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2033_, lean_object* v_structName_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2033_, v_structName_2034_);
lean_dec(v_structName_2034_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2036_, lean_object* v___x_2037_, lean_object* v_structName_2038_, lean_object* v_resolutionOrder_2039_, lean_object* v_s_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2036_, v___x_2037_, v_s_2040_, v_structName_2038_, v_resolutionOrder_2039_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2042_, lean_object* v_env_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v_asyncMode_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2044_ = l_Lean_structureResolutionExt;
v_asyncMode_2045_ = lean_ctor_get(v___x_2044_, 2);
v___x_2046_ = lean_box(0);
v___x_2047_ = 1;
v___x_2048_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2044_, v_env_2043_, v___f_2042_, v_asyncMode_2045_, v___x_2046_, v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2049_, lean_object* v_structName_2050_, lean_object* v_resolutionOrder_2051_){
_start:
{
lean_object* v_modifyEnv_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___f_2055_; lean_object* v___f_2056_; lean_object* v___x_2057_; 
v_modifyEnv_2052_ = lean_ctor_get(v_inst_2049_, 1);
lean_inc(v_modifyEnv_2052_);
lean_dec_ref(v_inst_2049_);
v___x_2053_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2054_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2055_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2055_, 0, v___x_2053_);
lean_closure_set(v___f_2055_, 1, v___x_2054_);
lean_closure_set(v___f_2055_, 2, v_structName_2050_);
lean_closure_set(v___f_2055_, 3, v_resolutionOrder_2051_);
v___f_2056_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2056_, 0, v___f_2055_);
v___x_2057_ = lean_apply_1(v_modifyEnv_2052_, v___f_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2058_, lean_object* v_inst_2059_, lean_object* v_structName_2060_, lean_object* v_resolutionOrder_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2059_, v_structName_2060_, v_resolutionOrder_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2080_, lean_object* v_resOrders_2081_, lean_object* v___x_2082_, lean_object* v_toPure_2083_, lean_object* v_____s_2084_){
_start:
{
lean_object* v_fst_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2100_; 
v_fst_2085_ = lean_ctor_get(v_____s_2084_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_____s_2084_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v_____s_2084_, 1);
lean_dec(v_unused_2101_);
v___x_2087_ = v_____s_2084_;
v_isShared_2088_ = v_isSharedCheck_2100_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_fst_2085_);
lean_dec(v_____s_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2100_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
if (lean_obj_tag(v_fst_2085_) == 0)
{
uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2089_ = 0;
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_array_get_borrowed(v___x_2080_, v_resOrders_2081_, v___x_2090_);
v___x_2092_ = lean_array_get_borrowed(v___x_2082_, v___x_2091_, v___x_2090_);
v___x_2093_ = lean_box(v___x_2089_);
lean_inc(v___x_2092_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2092_);
lean_ctor_set(v___x_2087_, 0, v___x_2093_);
v___x_2095_ = v___x_2087_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2092_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_apply_2(v_toPure_2083_, lean_box(0), v___x_2095_);
return v___x_2096_;
}
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2099_; 
lean_del_object(v___x_2087_);
v_val_2098_ = lean_ctor_get(v_fst_2085_, 0);
lean_inc(v_val_2098_);
lean_dec_ref_known(v_fst_2085_, 1);
v___x_2099_ = lean_apply_2(v_toPure_2083_, lean_box(0), v_val_2098_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2102_, lean_object* v_resOrders_2103_, lean_object* v___x_2104_, lean_object* v_toPure_2105_, lean_object* v_____s_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2102_, v_resOrders_2103_, v___x_2104_, v_toPure_2105_, v_____s_2106_);
lean_dec(v___x_2104_);
lean_dec_ref(v_resOrders_2103_);
lean_dec_ref(v___x_2102_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2108_, lean_object* v_____do__lift_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_apply_2(v_toPure_2108_, lean_box(0), v_____do__lift_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2111_, lean_object* v_toPure_2112_, lean_object* v___x_2113_, lean_object* v_____s_2114_){
_start:
{
lean_object* v_fst_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2133_; 
v_fst_2115_ = lean_ctor_get(v_____s_2114_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_____s_2114_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_____s_2114_, 1);
lean_dec(v_unused_2134_);
v___x_2117_ = v_____s_2114_;
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_fst_2115_);
lean_dec(v_____s_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
if (lean_obj_tag(v_fst_2115_) == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_del_object(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2111_);
v___x_2120_ = lean_apply_2(v_toPure_2112_, lean_box(0), v___x_2119_);
return v___x_2120_;
}
else
{
lean_object* v___x_2122_; 
lean_dec_ref(v___x_2111_);
lean_inc_ref(v_fst_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v___x_2113_);
v___x_2122_ = v___x_2117_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_fst_2115_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2113_);
v___x_2122_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v_fst_2115_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_fst_2115_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v_fst_2115_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v_fst_2115_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2122_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_apply_2(v_toPure_2112_, lean_box(0), v___x_2127_);
return v___x_2128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2135_, lean_object* v_next_2136_, lean_object* v_G_2137_, lean_object* v_____do__lift_2138_){
_start:
{
if (lean_obj_tag(v_____do__lift_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
lean_dec(v_G_2137_);
v_a_2139_ = lean_ctor_get(v_____do__lift_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v_____do__lift_2138_, 1);
v___x_2140_ = lean_apply_2(v_toPure_2135_, lean_box(0), v_a_2139_);
return v___x_2140_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec(v_toPure_2135_);
v_a_2141_ = lean_ctor_get(v_____do__lift_2138_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v_____do__lift_2138_, 1);
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = lean_nat_add(v_next_2136_, v___x_2142_);
v___x_2144_ = lean_apply_4(v_G_2137_, v___x_2143_, v_a_2141_, lean_box(0), lean_box(0));
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2145_, lean_object* v_next_2146_, lean_object* v_G_2147_, lean_object* v_____do__lift_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2145_, v_next_2146_, v_G_2147_, v_____do__lift_2148_);
lean_dec(v_next_2146_);
return v_res_2149_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2150_, uint8_t v___x_2151_, lean_object* v_v_2152_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_name_eq(v_v_2152_, v___x_2150_);
if (v___x_2153_ == 0)
{
return v___x_2153_;
}
else
{
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2154_, lean_object* v___x_2155_, lean_object* v_v_2156_){
_start:
{
uint8_t v___x_1557__boxed_2157_; uint8_t v_res_2158_; lean_object* v_r_2159_; 
v___x_1557__boxed_2157_ = lean_unbox(v___x_2155_);
v_res_2158_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2154_, v___x_1557__boxed_2157_, v_v_2156_);
lean_dec(v_v_2156_);
lean_dec(v___x_2154_);
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
uint8_t v___x_1602__boxed_2203_; uint8_t v_res_2204_; lean_object* v_r_2205_; 
v___x_1602__boxed_2203_ = lean_unbox(v___x_2200_);
v_res_2204_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1602__boxed_2203_, v___f_2201_, v_resOrder_2202_);
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
uint8_t v___y_1658__boxed_2215_; uint8_t v_res_2216_; lean_object* v_r_2217_; 
v___y_1658__boxed_2215_ = lean_unbox(v___y_2213_);
v_res_2216_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2212_, v___y_1658__boxed_2215_, v_v_2214_);
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
uint8_t v___x_1670__boxed_2227_; uint8_t v_res_2228_; lean_object* v_r_2229_; 
v___x_1670__boxed_2227_ = lean_unbox(v___x_2225_);
v_res_2228_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2224_, v___x_1670__boxed_2227_, v_v_2226_);
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
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_array_2251_; lean_object* v_start_2252_; lean_object* v_stop_2253_; lean_object* v___f_2254_; lean_object* v___y_2256_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___x_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; uint8_t v___y_2286_; uint8_t v___x_2298_; 
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
v___x_2281_ = lean_box(v___x_2245_);
lean_inc(v___x_2248_);
v___f_2282_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_2282_, 0, v___x_2248_);
lean_closure_set(v___f_2282_, 1, v___x_2281_);
v___x_2283_ = lean_box(v___x_2245_);
v___f_2284_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2284_, 0, v___x_2283_);
lean_closure_set(v___f_2284_, 1, v___f_2282_);
v___x_2298_ = lean_nat_dec_lt(v_start_2252_, v_stop_2253_);
if (v___x_2298_ == 0)
{
lean_dec(v_stop_2253_);
lean_dec(v_start_2252_);
lean_dec_ref(v_array_2251_);
v___y_2286_ = v___x_2245_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2299_; lean_object* v___f_2300_; lean_object* v___y_2302_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2299_ = lean_box(v___x_2245_);
lean_inc_ref(v___f_2284_);
v___f_2300_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2300_, 0, v___f_2284_);
lean_closure_set(v___f_2300_, 1, v___x_2299_);
v___x_2308_ = lean_array_get_size(v_array_2251_);
v___x_2309_ = lean_nat_dec_le(v_stop_2253_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_dec(v_stop_2253_);
v___y_2302_ = v___x_2308_;
goto v___jp_2301_;
}
else
{
v___y_2302_ = v_stop_2253_;
goto v___jp_2301_;
}
v___jp_2301_:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_nat_dec_lt(v_start_2252_, v___y_2302_);
if (v___x_2303_ == 0)
{
lean_dec(v___y_2302_);
lean_dec_ref(v___f_2300_);
lean_dec(v_start_2252_);
lean_dec_ref(v_array_2251_);
v___y_2286_ = v___x_2298_;
goto v___jp_2285_;
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2304_ = lean_usize_of_nat(v_start_2252_);
lean_dec(v_start_2252_);
v___x_2305_ = lean_usize_of_nat(v___y_2302_);
lean_dec(v___y_2302_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2250_, v___f_2300_, v_array_2251_, v___x_2304_, v___x_2305_);
v___x_2307_ = lean_unbox(v___x_2306_);
lean_dec(v___x_2306_);
if (v___x_2307_ == 0)
{
v___y_2286_ = v___x_2303_;
goto v___jp_2285_;
}
else
{
lean_dec_ref(v___f_2284_);
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
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2271_, v___y_2273_, v___y_2272_, v___x_2277_, v___x_2278_);
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
v___jp_2285_:
{
if (v___y_2286_ == 0)
{
lean_dec_ref(v___f_2284_);
lean_dec(v___x_2248_);
lean_dec(v_next_2241_);
lean_dec(v___x_2235_);
lean_dec_ref(v_resOrders_2233_);
lean_dec(v___x_2230_);
goto v___jp_2259_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_array_2290_; lean_object* v_start_2291_; lean_object* v_stop_2292_; uint8_t v___x_2293_; 
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_add(v_next_2241_, v___x_2287_);
lean_dec(v_next_2241_);
v___x_2289_ = l_Array_toSubarray___redArg(v_resOrders_2233_, v___x_2288_, v___x_2230_);
v_array_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc_ref(v_array_2290_);
v_start_2291_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_start_2291_);
v_stop_2292_ = lean_ctor_get(v___x_2289_, 2);
lean_inc(v_stop_2292_);
lean_dec_ref(v___x_2289_);
v___x_2293_ = lean_nat_dec_lt(v_start_2291_, v_stop_2292_);
if (v___x_2293_ == 0)
{
lean_dec(v_stop_2292_);
lean_dec(v_start_2291_);
lean_dec_ref(v_array_2290_);
lean_dec_ref(v___f_2284_);
lean_dec_ref(v___x_2238_);
goto v___jp_2262_;
}
else
{
lean_object* v___x_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2294_ = lean_box(v___y_2286_);
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2295_, 0, v___f_2284_);
lean_closure_set(v___f_2295_, 1, v___x_2294_);
v___x_2296_ = lean_array_get_size(v_array_2290_);
v___x_2297_ = lean_nat_dec_le(v_stop_2292_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_dec(v_stop_2292_);
v___y_2271_ = v___x_2250_;
v___y_2272_ = v_array_2290_;
v___y_2273_ = v___f_2295_;
v___y_2274_ = v_start_2291_;
v___y_2275_ = v___x_2296_;
goto v___jp_2270_;
}
else
{
v___y_2271_ = v___x_2250_;
v___y_2272_ = v_array_2290_;
v___y_2273_ = v___f_2295_;
v___y_2274_ = v_start_2291_;
v___y_2275_ = v_stop_2292_;
goto v___jp_2270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2310_, lean_object* v_toPure_2311_, lean_object* v___x_2312_, lean_object* v_resOrders_2313_, lean_object* v___x_2314_, lean_object* v___x_2315_, lean_object* v_toBind_2316_, lean_object* v___f_2317_, lean_object* v___x_2318_, lean_object* v_next_2319_, lean_object* v___x_2320_, lean_object* v_next_2321_, lean_object* v_acc_2322_, lean_object* v_h_2323_, lean_object* v_G_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2310_, v_toPure_2311_, v___x_2312_, v_resOrders_2313_, v___x_2314_, v___x_2315_, v_toBind_2316_, v___f_2317_, v___x_2318_, v_next_2319_, v___x_2320_, v_next_2321_, v_acc_2322_, v_h_2323_, v_G_2324_);
lean_dec(v_next_2319_);
lean_dec(v___x_2314_);
lean_dec_ref(v___x_2312_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2326_, lean_object* v_toPure_2327_, lean_object* v___x_2328_, lean_object* v_resOrders_2329_, lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v_toBind_2332_, lean_object* v___f_2333_, lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___f_2336_, lean_object* v___f_2337_, lean_object* v_next_2338_, lean_object* v_acc_2339_, lean_object* v_h_2340_, lean_object* v_G_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = lean_nat_dec_lt(v_next_2338_, v___x_2326_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; 
lean_dec(v_G_2341_);
lean_dec(v_next_2338_);
lean_dec(v___f_2337_);
lean_dec(v___f_2336_);
lean_dec_ref(v___x_2334_);
lean_dec(v___f_2333_);
lean_dec(v_toBind_2332_);
lean_dec(v___x_2331_);
lean_dec(v___x_2330_);
lean_dec_ref(v_resOrders_2329_);
lean_dec_ref(v___x_2328_);
v___x_2343_ = lean_apply_2(v_toPure_2327_, lean_box(0), v_acc_2339_);
return v___x_2343_;
}
else
{
lean_object* v___f_2344_; lean_object* v___x_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec_ref(v_acc_2339_);
lean_inc(v_next_2338_);
lean_inc(v_toPure_2327_);
v___f_2344_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2344_, 0, v_toPure_2327_);
lean_closure_set(v___f_2344_, 1, v_next_2338_);
lean_closure_set(v___f_2344_, 2, v_G_2341_);
v___x_2345_ = lean_nat_sub(v___x_2326_, v_next_2338_);
lean_inc_ref(v___x_2334_);
lean_inc_n(v_toBind_2332_, 3);
lean_inc(v___x_2331_);
v___f_2346_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2346_, 0, v___x_2345_);
lean_closure_set(v___f_2346_, 1, v_toPure_2327_);
lean_closure_set(v___f_2346_, 2, v___x_2328_);
lean_closure_set(v___f_2346_, 3, v_resOrders_2329_);
lean_closure_set(v___f_2346_, 4, v___x_2330_);
lean_closure_set(v___f_2346_, 5, v___x_2331_);
lean_closure_set(v___f_2346_, 6, v_toBind_2332_);
lean_closure_set(v___f_2346_, 7, v___f_2333_);
lean_closure_set(v___f_2346_, 8, v___x_2334_);
lean_closure_set(v___f_2346_, 9, v_next_2338_);
lean_closure_set(v___f_2346_, 10, v___x_2335_);
v___x_2347_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2346_, v___x_2331_, v___x_2334_, lean_box(0));
v___x_2348_ = lean_apply_4(v_toBind_2332_, lean_box(0), lean_box(0), v___x_2347_, v___f_2336_);
v___x_2349_ = lean_apply_4(v_toBind_2332_, lean_box(0), lean_box(0), v___x_2348_, v___f_2337_);
v___x_2350_ = lean_apply_4(v_toBind_2332_, lean_box(0), lean_box(0), v___x_2349_, v___f_2344_);
return v___x_2350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2351_, lean_object* v_toPure_2352_, lean_object* v___x_2353_, lean_object* v_resOrders_2354_, lean_object* v___x_2355_, lean_object* v___x_2356_, lean_object* v_toBind_2357_, lean_object* v___f_2358_, lean_object* v___x_2359_, lean_object* v___x_2360_, lean_object* v___f_2361_, lean_object* v___f_2362_, lean_object* v_next_2363_, lean_object* v_acc_2364_, lean_object* v_h_2365_, lean_object* v_G_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2351_, v_toPure_2352_, v___x_2353_, v_resOrders_2354_, v___x_2355_, v___x_2356_, v_toBind_2357_, v___f_2358_, v___x_2359_, v___x_2360_, v___f_2361_, v___f_2362_, v_next_2363_, v_acc_2364_, v_h_2365_, v_G_2366_);
lean_dec(v___x_2351_);
return v_res_2367_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Array_instInhabited___redArg();
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2372_, lean_object* v_resOrders_2373_){
_start:
{
lean_object* v_toApplicative_2374_; lean_object* v_toBind_2375_; lean_object* v_toPure_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_toApplicative_2374_ = lean_ctor_get(v_inst_2372_, 0);
lean_inc_ref(v_toApplicative_2374_);
v_toBind_2375_ = lean_ctor_get(v_inst_2372_, 1);
lean_inc_n(v_toBind_2375_, 2);
lean_dec_ref(v_inst_2372_);
v_toPure_2376_ = lean_ctor_get(v_toApplicative_2374_, 1);
lean_inc_n(v_toPure_2376_, 4);
lean_dec_ref(v_toApplicative_2374_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2379_ = lean_array_get_size(v_resOrders_2373_);
lean_inc_ref(v_resOrders_2373_);
v___f_2380_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2380_, 0, v___x_2378_);
lean_closure_set(v___f_2380_, 1, v_resOrders_2373_);
lean_closure_set(v___f_2380_, 2, v___x_2377_);
lean_closure_set(v___f_2380_, 3, v_toPure_2376_);
v___f_2381_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2381_, 0, v_toPure_2376_);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_box(0);
v___x_2384_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2385_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2385_, 0, v___x_2384_);
lean_closure_set(v___f_2385_, 1, v_toPure_2376_);
lean_closure_set(v___f_2385_, 2, v___x_2383_);
lean_inc_ref(v___f_2381_);
v___f_2386_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2386_, 0, v___x_2379_);
lean_closure_set(v___f_2386_, 1, v_toPure_2376_);
lean_closure_set(v___f_2386_, 2, v___x_2378_);
lean_closure_set(v___f_2386_, 3, v_resOrders_2373_);
lean_closure_set(v___f_2386_, 4, v___x_2377_);
lean_closure_set(v___f_2386_, 5, v___x_2382_);
lean_closure_set(v___f_2386_, 6, v_toBind_2375_);
lean_closure_set(v___f_2386_, 7, v___f_2381_);
lean_closure_set(v___f_2386_, 8, v___x_2384_);
lean_closure_set(v___f_2386_, 9, v___x_2383_);
lean_closure_set(v___f_2386_, 10, v___f_2385_);
lean_closure_set(v___f_2386_, 11, v___f_2381_);
v___x_2387_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2386_, v___x_2382_, v___x_2384_, lean_box(0));
v___x_2388_ = lean_apply_4(v_toBind_2375_, lean_box(0), lean_box(0), v___x_2387_, v___f_2380_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2389_, lean_object* v_inst_2390_, lean_object* v_resOrders_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2390_, v_resOrders_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2393_){
_start:
{
lean_object* v_structName_2394_; 
v_structName_2394_ = lean_ctor_get(v_x_2393_, 0);
lean_inc(v_structName_2394_);
return v_structName_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2395_);
lean_dec_ref(v_x_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2397_, lean_object* v_result_2398_, lean_object* v_____r_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_apply_2(v_toPure_2397_, lean_box(0), v_result_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2401_, lean_object* v_inst_2402_, lean_object* v_structName_2403_, lean_object* v_toBind_2404_, lean_object* v_result_2405_){
_start:
{
lean_object* v_resolutionOrder_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_resolutionOrder_2406_ = lean_ctor_get(v_result_2405_, 0);
lean_inc_ref(v_resolutionOrder_2406_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2407_, 0, v_toPure_2401_);
lean_closure_set(v___f_2407_, 1, v_result_2405_);
v___x_2408_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2402_, v_structName_2403_, v_resolutionOrder_2406_);
v___x_2409_ = lean_apply_4(v_toBind_2404_, lean_box(0), lean_box(0), v___x_2408_, v___f_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_toPure_2410_, lean_object* v_____s_2411_){
_start:
{
lean_object* v_snd_2412_; lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_snd_2412_ = lean_ctor_get(v_____s_2411_, 1);
lean_inc(v_snd_2412_);
lean_dec_ref(v_____s_2411_);
v_fst_2413_ = lean_ctor_get(v_snd_2412_, 0);
v_snd_2414_ = lean_ctor_get(v_snd_2412_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_snd_2412_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2416_ = v_snd_2412_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snd_2414_);
lean_inc(v_fst_2413_);
lean_dec(v_snd_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_fst_2413_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_snd_2414_);
v___x_2419_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_apply_2(v_toPure_2410_, lean_box(0), v___x_2419_);
return v___x_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2423_, lean_object* v_____do__lift_2424_){
_start:
{
if (lean_obj_tag(v_____do__lift_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2433_; 
v_a_2425_ = lean_ctor_get(v_____do__lift_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_____do__lift_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2427_ = v_____do__lift_2424_;
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v_____do__lift_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set_tag(v___x_2427_, 1);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2430_);
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_a_2434_ = lean_ctor_get(v_____do__lift_2424_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_____do__lift_2424_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v_____do__lift_2424_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v_____do__lift_2424_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 0);
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2439_);
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2443_, lean_object* v___f_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2446_ = lean_array_get_size(v_x_2445_);
v___x_2447_ = lean_mk_empty_array_with_capacity(v___x_2443_);
v___x_2448_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2449_ = lean_nat_dec_lt(v___x_2443_, v___x_2446_);
if (v___x_2449_ == 0)
{
lean_dec_ref(v_x_2445_);
lean_dec_ref(v___f_2444_);
return v___x_2447_;
}
else
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
if (v___x_2450_ == 0)
{
if (v___x_2449_ == 0)
{
lean_dec_ref(v_x_2445_);
lean_dec_ref(v___f_2444_);
return v___x_2447_;
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2446_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2448_, v___f_2444_, v_x_2445_, v___x_2451_, v___x_2452_, v___x_2447_);
return v___x_2453_;
}
}
else
{
size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = lean_usize_of_nat(v___x_2446_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2448_, v___f_2444_, v_x_2445_, v___x_2454_, v___x_2455_, v___x_2447_);
return v___x_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v___x_2457_, lean_object* v___f_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v___x_2457_, v___f_2458_, v_x_2459_);
lean_dec(v___x_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v_snd_2461_, lean_object* v_x1_2462_, lean_object* v_x2_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_name_eq(v_x2_2463_, v_snd_2461_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_array_push(v_x1_2462_, v_x2_2463_);
return v___x_2465_;
}
else
{
lean_dec(v_x2_2463_);
return v_x1_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v_snd_2466_, lean_object* v_x1_2467_, lean_object* v_x2_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v_snd_2466_, v_x1_2467_, v_x2_2468_);
lean_dec(v_snd_2466_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2470_, lean_object* v___f_2471_, lean_object* v_x1_2472_, lean_object* v_x2_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_array_2477_; lean_object* v_start_2478_; lean_object* v_stop_2479_; lean_object* v___y_2481_; uint8_t v___x_2488_; 
v___x_2474_ = lean_array_get_size(v_x2_2473_);
lean_inc_ref(v_x2_2473_);
v___x_2475_ = l_Array_toSubarray___redArg(v_x2_2473_, v___x_2470_, v___x_2474_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2477_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_ref(v_array_2477_);
v_start_2478_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_start_2478_);
v_stop_2479_ = lean_ctor_get(v___x_2475_, 2);
lean_inc(v_stop_2479_);
lean_dec_ref(v___x_2475_);
v___x_2488_ = lean_nat_dec_lt(v_start_2478_, v_stop_2479_);
if (v___x_2488_ == 0)
{
lean_dec(v_stop_2479_);
lean_dec(v_start_2478_);
lean_dec_ref(v_array_2477_);
lean_dec_ref(v_x2_2473_);
lean_dec_ref(v___f_2471_);
return v_x1_2472_;
}
else
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = lean_array_get_size(v_array_2477_);
v___x_2490_ = lean_nat_dec_le(v_stop_2479_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec(v_stop_2479_);
v___y_2481_ = v___x_2489_;
goto v___jp_2480_;
}
else
{
v___y_2481_ = v_stop_2479_;
goto v___jp_2480_;
}
}
v___jp_2480_:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_nat_dec_lt(v_start_2478_, v___y_2481_);
if (v___x_2482_ == 0)
{
lean_dec(v___y_2481_);
lean_dec(v_start_2478_);
lean_dec_ref(v_array_2477_);
lean_dec_ref(v_x2_2473_);
lean_dec_ref(v___f_2471_);
return v_x1_2472_;
}
else
{
size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2483_ = lean_usize_of_nat(v_start_2478_);
lean_dec(v_start_2478_);
v___x_2484_ = lean_usize_of_nat(v___y_2481_);
lean_dec(v___y_2481_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2476_, v___f_2471_, v_array_2477_, v___x_2483_, v___x_2484_);
v___x_2486_ = lean_unbox(v___x_2485_);
lean_dec(v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v_x2_2473_);
return v_x1_2472_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_array_push(v_x1_2472_, v_x2_2473_);
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_name_eq(v_x_2492_, v_snd_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2494_, lean_object* v_x_2495_){
_start:
{
uint8_t v_res_2496_; lean_object* v_r_2497_; 
v_res_2496_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2494_, v_x_2495_);
lean_dec(v_x_2495_);
lean_dec(v_snd_2494_);
v_r_2497_ = lean_box(v_res_2496_);
return v_r_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2499_, lean_object* v___x_2500_, lean_object* v_fst_2501_, lean_object* v_fst_2502_, lean_object* v___f_2503_, uint8_t v_relaxed_2504_, lean_object* v___x_2505_, lean_object* v_parentNames_2506_, lean_object* v___f_2507_, lean_object* v_snd_2508_, lean_object* v___f_2509_, lean_object* v___x_2510_, lean_object* v_____x_2511_){
_start:
{
lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___f_2522_; lean_object* v___f_2523_; lean_object* v_defects_2525_; lean_object* v___y_2540_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2564_; uint8_t v___x_2574_; 
v_fst_2520_ = lean_ctor_get(v_____x_2511_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v_____x_2511_, 1);
lean_inc_n(v_snd_2521_, 2);
lean_dec_ref(v_____x_2511_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2522_, 0, v_snd_2521_);
lean_inc(v___x_2500_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 3, 2);
lean_closure_set(v___f_2523_, 0, v___x_2500_);
lean_closure_set(v___f_2523_, 1, v___f_2522_);
v___x_2574_ = lean_unbox(v_fst_2520_);
lean_dec(v_fst_2520_);
if (v___x_2574_ == 0)
{
if (v_relaxed_2504_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2575_ = lean_array_get_size(v_fst_2502_);
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2500_);
v___x_2577_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2578_ = lean_nat_dec_lt(v___x_2500_, v___x_2575_);
if (v___x_2578_ == 0)
{
v___y_2564_ = v___x_2576_;
goto v___jp_2563_;
}
else
{
lean_object* v___f_2579_; lean_object* v___f_2580_; uint8_t v___x_2581_; 
lean_inc(v_snd_2521_);
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2579_, 0, v_snd_2521_);
lean_inc(v___x_2510_);
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2580_, 0, v___x_2510_);
lean_closure_set(v___f_2580_, 1, v___f_2579_);
v___x_2581_ = lean_nat_dec_le(v___x_2575_, v___x_2575_);
if (v___x_2581_ == 0)
{
if (v___x_2578_ == 0)
{
lean_dec_ref(v___f_2580_);
v___y_2564_ = v___x_2576_;
goto v___jp_2563_;
}
else
{
size_t v___x_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = lean_usize_of_nat(v___x_2575_);
lean_inc(v_fst_2502_);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2577_, v___f_2580_, v_fst_2502_, v___x_2582_, v___x_2583_, v___x_2576_);
v___y_2564_ = v___x_2584_;
goto v___jp_2563_;
}
}
else
{
size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = lean_usize_of_nat(v___x_2575_);
lean_inc(v_fst_2502_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2577_, v___f_2580_, v_fst_2502_, v___x_2585_, v___x_2586_, v___x_2576_);
v___y_2564_ = v___x_2587_;
goto v___jp_2563_;
}
}
}
else
{
lean_dec(v___x_2510_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___f_2507_);
lean_dec_ref(v_parentNames_2506_);
lean_dec_ref(v___x_2505_);
v_defects_2525_ = v_snd_2508_;
goto v___jp_2524_;
}
}
else
{
lean_dec(v___x_2510_);
lean_dec_ref(v___f_2509_);
lean_dec_ref(v___f_2507_);
lean_dec_ref(v_parentNames_2506_);
lean_dec_ref(v___x_2505_);
v_defects_2525_ = v_snd_2508_;
goto v___jp_2524_;
}
v___jp_2512_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___y_2514_);
lean_ctor_set(v___x_2516_, 1, v___y_2513_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___y_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
v___x_2519_ = lean_apply_2(v_toPure_2499_, lean_box(0), v___x_2518_);
return v___x_2519_;
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; size_t v_sz_2528_; size_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2526_ = lean_array_push(v_fst_2501_, v_snd_2521_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2528_ = lean_array_size(v_fst_2502_);
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2527_, v___f_2523_, v_sz_2528_, v___x_2529_, v_fst_2502_);
v___x_2531_ = lean_array_get_size(v___x_2530_);
v___x_2532_ = lean_mk_empty_array_with_capacity(v___x_2500_);
v___x_2533_ = lean_nat_dec_lt(v___x_2500_, v___x_2531_);
lean_dec(v___x_2500_);
if (v___x_2533_ == 0)
{
lean_dec(v___x_2530_);
lean_dec_ref(v___f_2503_);
v___y_2513_ = v_defects_2525_;
v___y_2514_ = v___x_2526_;
v___y_2515_ = v___x_2532_;
goto v___jp_2512_;
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_le(v___x_2531_, v___x_2531_);
if (v___x_2534_ == 0)
{
if (v___x_2533_ == 0)
{
lean_dec(v___x_2530_);
lean_dec_ref(v___f_2503_);
v___y_2513_ = v_defects_2525_;
v___y_2514_ = v___x_2526_;
v___y_2515_ = v___x_2532_;
goto v___jp_2512_;
}
else
{
size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_usize_of_nat(v___x_2531_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2527_, v___f_2503_, v___x_2530_, v___x_2529_, v___x_2535_, v___x_2532_);
v___y_2513_ = v_defects_2525_;
v___y_2514_ = v___x_2526_;
v___y_2515_ = v___x_2536_;
goto v___jp_2512_;
}
}
else
{
size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_usize_of_nat(v___x_2531_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2527_, v___f_2503_, v___x_2530_, v___x_2529_, v___x_2537_, v___x_2532_);
v___y_2513_ = v_defects_2525_;
v___y_2514_ = v___x_2526_;
v___y_2515_ = v___x_2538_;
goto v___jp_2512_;
}
}
}
v___jp_2539_:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; lean_object* v___x_2543_; size_t v_sz_2544_; size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_inc_ref(v___x_2505_);
v___x_2541_ = l_Array_eraseReps___redArg(v___x_2505_, v___y_2540_);
lean_inc_n(v_snd_2521_, 2);
v___x_2542_ = l_Array_contains___redArg(v___x_2505_, v_parentNames_2506_, v_snd_2521_);
v___x_2543_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2544_ = lean_array_size(v___x_2541_);
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2543_, v___f_2507_, v_sz_2544_, v___x_2545_, v___x_2541_);
v___x_2547_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2547_, 0, v_snd_2521_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*2, v___x_2542_);
v___x_2548_ = lean_array_push(v_snd_2508_, v___x_2547_);
v_defects_2525_ = v___x_2548_;
goto v___jp_2524_;
}
v___jp_2549_:
{
lean_object* v___x_2555_; 
lean_inc_ref(v___y_2553_);
v___x_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2553_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2554_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2554_);
lean_dec(v___y_2550_);
v___y_2540_ = v___x_2555_;
goto v___jp_2539_;
}
v___jp_2556_:
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_le(v___y_2561_, v___y_2558_);
if (v___x_2562_ == 0)
{
lean_dec(v___y_2558_);
lean_inc(v___y_2561_);
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2559_;
v___y_2552_ = v___y_2561_;
v___y_2553_ = v___y_2560_;
v___y_2554_ = v___y_2561_;
goto v___jp_2549_;
}
else
{
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2559_;
v___y_2552_ = v___y_2561_;
v___y_2553_ = v___y_2560_;
v___y_2554_ = v___y_2558_;
goto v___jp_2549_;
}
}
v___jp_2563_:
{
lean_object* v___x_2565_; size_t v_sz_2566_; size_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2565_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2566_ = lean_array_size(v___y_2564_);
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2565_, v___f_2509_, v_sz_2566_, v___x_2567_, v___y_2564_);
v___x_2569_ = lean_array_get_size(v___x_2568_);
v___x_2570_ = lean_nat_dec_eq(v___x_2569_, v___x_2500_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2572_ = lean_nat_sub(v___x_2569_, v___x_2510_);
lean_dec(v___x_2510_);
v___x_2573_ = lean_nat_dec_le(v___x_2500_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_inc(v___x_2572_);
v___y_2557_ = v___x_2569_;
v___y_2558_ = v___x_2572_;
v___y_2559_ = v___x_2568_;
v___y_2560_ = v___x_2571_;
v___y_2561_ = v___x_2572_;
goto v___jp_2556_;
}
else
{
lean_inc(v___x_2500_);
v___y_2557_ = v___x_2569_;
v___y_2558_ = v___x_2572_;
v___y_2559_ = v___x_2568_;
v___y_2560_ = v___x_2571_;
v___y_2561_ = v___x_2500_;
goto v___jp_2556_;
}
}
else
{
lean_dec(v___x_2510_);
v___y_2540_ = v___x_2568_;
goto v___jp_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2588_, lean_object* v___x_2589_, lean_object* v_fst_2590_, lean_object* v_fst_2591_, lean_object* v___f_2592_, lean_object* v_relaxed_2593_, lean_object* v___x_2594_, lean_object* v_parentNames_2595_, lean_object* v___f_2596_, lean_object* v_snd_2597_, lean_object* v___f_2598_, lean_object* v___x_2599_, lean_object* v_____x_2600_){
_start:
{
uint8_t v_relaxed_boxed_2601_; lean_object* v_res_2602_; 
v_relaxed_boxed_2601_ = lean_unbox(v_relaxed_2593_);
v_res_2602_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2588_, v___x_2589_, v_fst_2590_, v_fst_2591_, v___f_2592_, v_relaxed_boxed_2601_, v___x_2594_, v_parentNames_2595_, v___f_2596_, v_snd_2597_, v___f_2598_, v___x_2599_, v_____x_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2603_, lean_object* v_toPure_2604_, lean_object* v___f_2605_, uint8_t v_relaxed_2606_, lean_object* v___x_2607_, lean_object* v_parentNames_2608_, lean_object* v___f_2609_, lean_object* v___f_2610_, lean_object* v___x_2611_, lean_object* v_inst_2612_, lean_object* v_toBind_2613_, lean_object* v___f_2614_, lean_object* v_b_2615_){
_start:
{
lean_object* v_snd_2616_; lean_object* v_fst_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2643_; 
v_snd_2616_ = lean_ctor_get(v_b_2615_, 1);
v_fst_2617_ = lean_ctor_get(v_b_2615_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_b_2615_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2619_ = v_b_2615_;
v_isShared_2620_ = v_isSharedCheck_2643_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2616_);
lean_inc(v_fst_2617_);
lean_dec(v_b_2615_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2643_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2642_; 
v_fst_2621_ = lean_ctor_get(v_snd_2616_, 0);
v_snd_2622_ = lean_ctor_get(v_snd_2616_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_snd_2616_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2624_ = v_snd_2616_;
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_snd_2622_);
lean_inc(v_fst_2621_);
lean_dec(v_snd_2616_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_array_get_size(v_fst_2617_);
v___x_2627_ = lean_nat_dec_eq(v___x_2626_, v___x_2603_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_del_object(v___x_2624_);
lean_del_object(v___x_2619_);
v___x_2628_ = lean_box(v_relaxed_2606_);
lean_inc(v_fst_2617_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 13, 12);
lean_closure_set(v___f_2629_, 0, v_toPure_2604_);
lean_closure_set(v___f_2629_, 1, v___x_2603_);
lean_closure_set(v___f_2629_, 2, v_fst_2621_);
lean_closure_set(v___f_2629_, 3, v_fst_2617_);
lean_closure_set(v___f_2629_, 4, v___f_2605_);
lean_closure_set(v___f_2629_, 5, v___x_2628_);
lean_closure_set(v___f_2629_, 6, v___x_2607_);
lean_closure_set(v___f_2629_, 7, v_parentNames_2608_);
lean_closure_set(v___f_2629_, 8, v___f_2609_);
lean_closure_set(v___f_2629_, 9, v_snd_2622_);
lean_closure_set(v___f_2629_, 10, v___f_2610_);
lean_closure_set(v___f_2629_, 11, v___x_2611_);
v___x_2630_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2612_, v_fst_2617_);
lean_inc(v_toBind_2613_);
v___x_2631_ = lean_apply_4(v_toBind_2613_, lean_box(0), lean_box(0), v___x_2630_, v___f_2629_);
v___x_2632_ = lean_apply_4(v_toBind_2613_, lean_box(0), lean_box(0), v___x_2631_, v___f_2614_);
return v___x_2632_;
}
else
{
lean_object* v___x_2634_; 
lean_dec_ref(v_inst_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v___f_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v_parentNames_2608_);
lean_dec_ref(v___x_2607_);
lean_dec_ref(v___f_2605_);
lean_dec(v___x_2603_);
if (v_isShared_2625_ == 0)
{
v___x_2634_ = v___x_2624_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_fst_2621_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2622_);
v___x_2634_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v___x_2634_);
v___x_2636_ = v___x_2619_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_fst_2617_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = lean_apply_2(v_toPure_2604_, lean_box(0), v___x_2637_);
v___x_2639_ = lean_apply_4(v_toBind_2613_, lean_box(0), lean_box(0), v___x_2638_, v___f_2614_);
return v___x_2639_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2644_, lean_object* v_toPure_2645_, lean_object* v___f_2646_, lean_object* v_relaxed_2647_, lean_object* v___x_2648_, lean_object* v_parentNames_2649_, lean_object* v___f_2650_, lean_object* v___f_2651_, lean_object* v___x_2652_, lean_object* v_inst_2653_, lean_object* v_toBind_2654_, lean_object* v___f_2655_, lean_object* v_b_2656_){
_start:
{
uint8_t v_relaxed_boxed_2657_; lean_object* v_res_2658_; 
v_relaxed_boxed_2657_ = lean_unbox(v_relaxed_2647_);
v_res_2658_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2644_, v_toPure_2645_, v___f_2646_, v_relaxed_boxed_2657_, v___x_2648_, v_parentNames_2649_, v___f_2650_, v___f_2651_, v___x_2652_, v_inst_2653_, v_toBind_2654_, v___f_2655_, v_b_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2659_, lean_object* v___x_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_array_get_borrowed(v___x_2659_, v_x_2661_, v___x_2660_);
lean_inc(v___x_2662_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2663_, lean_object* v___x_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2663_, v___x_2664_, v_x_2665_);
lean_dec_ref(v_x_2665_);
lean_dec(v___x_2664_);
lean_dec(v___x_2663_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v___x_2669_, lean_object* v_toPure_2670_, lean_object* v___f_2671_, uint8_t v_relaxed_2672_, lean_object* v___x_2673_, lean_object* v_parentNames_2674_, lean_object* v___f_2675_, lean_object* v_inst_2676_, lean_object* v_toBind_2677_, lean_object* v___f_2678_, lean_object* v_structName_2679_, lean_object* v___f_2680_, lean_object* v___f_2681_, lean_object* v_parentResOrders_2682_){
_start:
{
lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___y_2686_; lean_object* v_j_2697_; lean_object* v_as_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2683_ = lean_unsigned_to_nat(0u);
v___f_2684_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2684_, 0, v___x_2669_);
lean_closure_set(v___f_2684_, 1, v___x_2683_);
v_j_2697_ = lean_array_get_size(v_parentResOrders_2682_);
lean_inc_ref(v_parentNames_2674_);
v_as_2698_ = lean_array_push(v_parentResOrders_2682_, v_parentNames_2674_);
v___x_2699_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2683_, v_as_2698_, v_j_2697_);
v___x_2700_ = lean_array_get_size(v___x_2699_);
v___x_2701_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v___x_2702_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2703_ = lean_nat_dec_lt(v___x_2683_, v___x_2700_);
if (v___x_2703_ == 0)
{
lean_dec_ref(v___x_2699_);
lean_dec_ref(v___f_2681_);
v___y_2686_ = v___x_2701_;
goto v___jp_2685_;
}
else
{
uint8_t v___x_2704_; 
v___x_2704_ = lean_nat_dec_le(v___x_2700_, v___x_2700_);
if (v___x_2704_ == 0)
{
if (v___x_2703_ == 0)
{
lean_dec_ref(v___x_2699_);
lean_dec_ref(v___f_2681_);
v___y_2686_ = v___x_2701_;
goto v___jp_2685_;
}
else
{
size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = lean_usize_of_nat(v___x_2700_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2702_, v___f_2681_, v___x_2699_, v___x_2705_, v___x_2706_, v___x_2701_);
v___y_2686_ = v___x_2707_;
goto v___jp_2685_;
}
}
else
{
size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = lean_usize_of_nat(v___x_2700_);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2702_, v___f_2681_, v___x_2699_, v___x_2708_, v___x_2709_, v___x_2701_);
v___y_2686_ = v___x_2710_;
goto v___jp_2685_;
}
}
v___jp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v_resOrder_2691_; lean_object* v_defects_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_box(v_relaxed_2672_);
lean_inc(v_toBind_2677_);
lean_inc_ref(v_inst_2676_);
v___f_2689_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_2689_, 0, v___x_2683_);
lean_closure_set(v___f_2689_, 1, v_toPure_2670_);
lean_closure_set(v___f_2689_, 2, v___f_2671_);
lean_closure_set(v___f_2689_, 3, v___x_2688_);
lean_closure_set(v___f_2689_, 4, v___x_2673_);
lean_closure_set(v___f_2689_, 5, v_parentNames_2674_);
lean_closure_set(v___f_2689_, 6, v___f_2675_);
lean_closure_set(v___f_2689_, 7, v___f_2684_);
lean_closure_set(v___f_2689_, 8, v___x_2687_);
lean_closure_set(v___f_2689_, 9, v_inst_2676_);
lean_closure_set(v___f_2689_, 10, v_toBind_2677_);
lean_closure_set(v___f_2689_, 11, v___f_2678_);
v___x_2690_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v_resOrder_2691_ = lean_array_push(v___x_2690_, v_structName_2679_);
v_defects_2692_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_resOrder_2691_);
lean_ctor_set(v___x_2693_, 1, v_defects_2692_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___y_2686_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2676_, v___f_2689_, v___x_2694_);
v___x_2696_ = lean_apply_4(v_toBind_2677_, lean_box(0), lean_box(0), v___x_2695_, v___f_2680_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v___x_2711_, lean_object* v_toPure_2712_, lean_object* v___f_2713_, lean_object* v_relaxed_2714_, lean_object* v___x_2715_, lean_object* v_parentNames_2716_, lean_object* v___f_2717_, lean_object* v_inst_2718_, lean_object* v_toBind_2719_, lean_object* v___f_2720_, lean_object* v_structName_2721_, lean_object* v___f_2722_, lean_object* v___f_2723_, lean_object* v_parentResOrders_2724_){
_start:
{
uint8_t v_relaxed_boxed_2725_; lean_object* v_res_2726_; 
v_relaxed_boxed_2725_ = lean_unbox(v_relaxed_2714_);
v_res_2726_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v___x_2711_, v_toPure_2712_, v___f_2713_, v_relaxed_boxed_2725_, v___x_2715_, v_parentNames_2716_, v___f_2717_, v_inst_2718_, v_toBind_2719_, v___f_2720_, v_structName_2721_, v___f_2722_, v___f_2723_, v_parentResOrders_2724_);
return v_res_2726_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2728_ = lean_array_get_size(v_x_2727_);
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = lean_nat_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
v___x_2731_ = 1;
return v___x_2731_;
}
else
{
uint8_t v___x_2732_; 
v___x_2732_ = 0;
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2733_){
_start:
{
uint8_t v_res_2734_; lean_object* v_r_2735_; 
v_res_2734_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2733_);
lean_dec_ref(v_x_2733_);
v_r_2735_ = lean_box(v_res_2734_);
return v_r_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2736_, lean_object* v_x1_2737_, lean_object* v_x2_2738_){
_start:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
lean_inc_ref(v_x2_2738_);
v___x_2739_ = lean_apply_1(v___f_2736_, v_x2_2738_);
v___x_2740_ = lean_unbox(v___x_2739_);
if (v___x_2740_ == 0)
{
lean_dec_ref(v_x2_2738_);
return v_x1_2737_;
}
else
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_array_push(v_x1_2737_, v_x2_2738_);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_toPure_2742_, lean_object* v_____do__lift_2743_){
_start:
{
lean_object* v_resolutionOrder_2744_; lean_object* v___x_2745_; 
v_resolutionOrder_2744_ = lean_ctor_get(v_____do__lift_2743_, 0);
lean_inc_ref(v_resolutionOrder_2744_);
lean_dec_ref(v_____do__lift_2743_);
v___x_2745_ = lean_apply_2(v_toPure_2742_, lean_box(0), v_resolutionOrder_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v___x_2746_, lean_object* v_parentNames_2747_, lean_object* v_x_2748_){
_start:
{
uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_inc(v_x_2748_);
v___x_2749_ = l_Array_contains___redArg(v___x_2746_, v_parentNames_2747_, v_x_2748_);
v___x_2750_ = lean_box(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_x_2748_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_structName_2758_, lean_object* v_parentNames_2759_, uint8_t v_relaxed_2760_){
_start:
{
lean_object* v_toApplicative_2761_; lean_object* v_toBind_2762_; lean_object* v_toPure_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___x_2772_; lean_object* v___f_2773_; size_t v_sz_2774_; size_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_toApplicative_2761_ = lean_ctor_get(v_inst_2756_, 0);
v_toBind_2762_ = lean_ctor_get(v_inst_2756_, 1);
lean_inc_n(v_toBind_2762_, 3);
v_toPure_2763_ = lean_ctor_get(v_toApplicative_2761_, 1);
v___f_2764_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
v___x_2765_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref_n(v_parentNames_2759_, 2);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 3, 2);
lean_closure_set(v___f_2766_, 0, v___x_2765_);
lean_closure_set(v___f_2766_, 1, v_parentNames_2759_);
v___x_2767_ = lean_box(0);
lean_inc_n(v_toPure_2763_, 4);
v___f_2768_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2768_, 0, v_toPure_2763_);
lean_inc_ref_n(v_inst_2756_, 2);
v___f_2769_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2769_, 0, v_inst_2756_);
lean_closure_set(v___f_2769_, 1, v_inst_2757_);
lean_closure_set(v___f_2769_, 2, v_toBind_2762_);
lean_closure_set(v___f_2769_, 3, v___f_2768_);
v___f_2770_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2770_, 0, v_toPure_2763_);
v___f_2771_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6), 2, 1);
lean_closure_set(v___f_2771_, 0, v_toPure_2763_);
v___x_2772_ = lean_box(v_relaxed_2760_);
v___f_2773_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 14, 13);
lean_closure_set(v___f_2773_, 0, v___x_2767_);
lean_closure_set(v___f_2773_, 1, v_toPure_2763_);
lean_closure_set(v___f_2773_, 2, v___f_2764_);
lean_closure_set(v___f_2773_, 3, v___x_2772_);
lean_closure_set(v___f_2773_, 4, v___x_2765_);
lean_closure_set(v___f_2773_, 5, v_parentNames_2759_);
lean_closure_set(v___f_2773_, 6, v___f_2766_);
lean_closure_set(v___f_2773_, 7, v_inst_2756_);
lean_closure_set(v___f_2773_, 8, v_toBind_2762_);
lean_closure_set(v___f_2773_, 9, v___f_2770_);
lean_closure_set(v___f_2773_, 10, v_structName_2758_);
lean_closure_set(v___f_2773_, 11, v___f_2771_);
lean_closure_set(v___f_2773_, 12, v___f_2764_);
v_sz_2774_ = lean_array_size(v_parentNames_2759_);
v___x_2775_ = ((size_t)0ULL);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2756_, v___f_2769_, v_sz_2774_, v___x_2775_, v_parentNames_2759_);
v___x_2777_ = lean_apply_4(v_toBind_2762_, lean_box(0), lean_box(0), v___x_2776_, v___f_2773_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2778_, lean_object* v_toPure_2779_, lean_object* v___f_2780_, lean_object* v_inst_2781_, lean_object* v_inst_2782_, uint8_t v_relaxed_2783_, lean_object* v_toBind_2784_, lean_object* v___f_2785_, lean_object* v_env_2786_){
_start:
{
lean_object* v___x_2787_; 
lean_inc_ref(v_env_2786_);
v___x_2787_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2786_, v_structName_2778_);
if (lean_obj_tag(v___x_2787_) == 1)
{
lean_object* v_val_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec_ref(v_env_2786_);
lean_dec(v___f_2785_);
lean_dec(v_toBind_2784_);
lean_dec_ref(v_inst_2782_);
lean_dec_ref(v_inst_2781_);
lean_dec_ref(v___f_2780_);
lean_dec(v_structName_2778_);
v_val_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_val_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_apply_2(v_toPure_2779_, lean_box(0), v___x_2790_);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; size_t v_sz_2794_; size_t v___x_2795_; lean_object* v_parentNames_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec(v___x_2787_);
lean_dec(v_toPure_2779_);
lean_inc(v_structName_2778_);
v___x_2792_ = l_Lean_getStructureParentInfo(v_env_2786_, v_structName_2778_);
v___x_2793_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2794_ = lean_array_size(v___x_2792_);
v___x_2795_ = ((size_t)0ULL);
v_parentNames_2796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2793_, v___f_2780_, v_sz_2794_, v___x_2795_, v___x_2792_);
v___x_2797_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2781_, v_inst_2782_, v_structName_2778_, v_parentNames_2796_, v_relaxed_2783_);
v___x_2798_ = lean_apply_4(v_toBind_2784_, lean_box(0), lean_box(0), v___x_2797_, v___f_2785_);
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2799_, lean_object* v_toPure_2800_, lean_object* v___f_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_relaxed_2804_, lean_object* v_toBind_2805_, lean_object* v___f_2806_, lean_object* v_env_2807_){
_start:
{
uint8_t v_relaxed_boxed_2808_; lean_object* v_res_2809_; 
v_relaxed_boxed_2808_ = lean_unbox(v_relaxed_2804_);
v_res_2809_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2799_, v_toPure_2800_, v___f_2801_, v_inst_2802_, v_inst_2803_, v_relaxed_boxed_2808_, v_toBind_2805_, v___f_2806_, v_env_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_structName_2812_, uint8_t v_relaxed_2813_){
_start:
{
lean_object* v_toApplicative_2814_; lean_object* v_toBind_2815_; lean_object* v_getEnv_2816_; lean_object* v_toPure_2817_; lean_object* v___f_2818_; lean_object* v___f_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
v_toApplicative_2814_ = lean_ctor_get(v_inst_2810_, 0);
v_toBind_2815_ = lean_ctor_get(v_inst_2810_, 1);
lean_inc_n(v_toBind_2815_, 3);
v_getEnv_2816_ = lean_ctor_get(v_inst_2811_, 0);
lean_inc(v_getEnv_2816_);
v_toPure_2817_ = lean_ctor_get(v_toApplicative_2814_, 1);
lean_inc_n(v_toPure_2817_, 2);
v___f_2818_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2812_);
lean_inc_ref(v_inst_2811_);
v___f_2819_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2819_, 0, v_toPure_2817_);
lean_closure_set(v___f_2819_, 1, v_inst_2811_);
lean_closure_set(v___f_2819_, 2, v_structName_2812_);
lean_closure_set(v___f_2819_, 3, v_toBind_2815_);
v___x_2820_ = lean_box(v_relaxed_2813_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2821_, 0, v_structName_2812_);
lean_closure_set(v___f_2821_, 1, v_toPure_2817_);
lean_closure_set(v___f_2821_, 2, v___f_2818_);
lean_closure_set(v___f_2821_, 3, v_inst_2810_);
lean_closure_set(v___f_2821_, 4, v_inst_2811_);
lean_closure_set(v___f_2821_, 5, v___x_2820_);
lean_closure_set(v___f_2821_, 6, v_toBind_2815_);
lean_closure_set(v___f_2821_, 7, v___f_2819_);
v___x_2822_ = lean_apply_4(v_toBind_2815_, lean_box(0), lean_box(0), v_getEnv_2816_, v___f_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_toBind_2825_, lean_object* v___f_2826_, lean_object* v_parentName_2827_){
_start:
{
uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = 1;
v___x_2829_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2823_, v_inst_2824_, v_parentName_2827_, v___x_2828_);
v___x_2830_ = lean_apply_4(v_toBind_2825_, lean_box(0), lean_box(0), v___x_2829_, v___f_2826_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_structName_2833_, lean_object* v_relaxed_2834_){
_start:
{
uint8_t v_relaxed_boxed_2835_; lean_object* v_res_2836_; 
v_relaxed_boxed_2835_ = lean_unbox(v_relaxed_2834_);
v_res_2836_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2831_, v_inst_2832_, v_structName_2833_, v_relaxed_boxed_2835_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_structName_2839_, lean_object* v_parentNames_2840_, lean_object* v_relaxed_2841_){
_start:
{
uint8_t v_relaxed_boxed_2842_; lean_object* v_res_2843_; 
v_relaxed_boxed_2842_ = lean_unbox(v_relaxed_2841_);
v_res_2843_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2837_, v_inst_2838_, v_structName_2839_, v_parentNames_2840_, v_relaxed_boxed_2842_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2844_, lean_object* v_inst_2845_, lean_object* v_inst_2846_, lean_object* v_structName_2847_, uint8_t v_relaxed_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2845_, v_inst_2846_, v_structName_2847_, v_relaxed_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_structName_2853_, lean_object* v_relaxed_2854_){
_start:
{
uint8_t v_relaxed_boxed_2855_; lean_object* v_res_2856_; 
v_relaxed_boxed_2855_ = lean_unbox(v_relaxed_2854_);
v_res_2856_ = l_Lean_computeStructureResolutionOrder(v_m_2850_, v_inst_2851_, v_inst_2852_, v_structName_2853_, v_relaxed_boxed_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_structName_2860_, lean_object* v_parentNames_2861_, uint8_t v_relaxed_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2858_, v_inst_2859_, v_structName_2860_, v_parentNames_2861_, v_relaxed_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_structName_2867_, lean_object* v_parentNames_2868_, lean_object* v_relaxed_2869_){
_start:
{
uint8_t v_relaxed_boxed_2870_; lean_object* v_res_2871_; 
v_relaxed_boxed_2870_ = lean_unbox(v_relaxed_2869_);
v_res_2871_ = l_Lean_mergeStructureResolutionOrders(v_m_2864_, v_inst_2865_, v_inst_2866_, v_structName_2867_, v_parentNames_2868_, v_relaxed_boxed_2870_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2872_){
_start:
{
lean_object* v_resolutionOrder_2873_; 
v_resolutionOrder_2873_ = lean_ctor_get(v_x_2872_, 0);
lean_inc_ref(v_resolutionOrder_2873_);
return v_resolutionOrder_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2874_);
lean_dec_ref(v_x_2874_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_structName_2879_){
_start:
{
lean_object* v_toApplicative_2880_; lean_object* v_toFunctor_2881_; lean_object* v_map_2882_; lean_object* v___f_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_toApplicative_2880_ = lean_ctor_get(v_inst_2877_, 0);
v_toFunctor_2881_ = lean_ctor_get(v_toApplicative_2880_, 0);
v_map_2882_ = lean_ctor_get(v_toFunctor_2881_, 0);
lean_inc(v_map_2882_);
v___f_2883_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2884_ = 1;
v___x_2885_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2877_, v_inst_2878_, v_structName_2879_, v___x_2884_);
v___x_2886_ = lean_apply_4(v_map_2882_, lean_box(0), lean_box(0), v___f_2883_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_structName_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2888_, v_inst_2889_, v_structName_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2892_, lean_object* v_structName_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Array_erase___redArg(v___x_2892_, v_x_2894_, v_structName_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_structName_2898_){
_start:
{
lean_object* v_toApplicative_2899_; lean_object* v_toFunctor_2900_; lean_object* v_map_2901_; lean_object* v___x_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_toApplicative_2899_ = lean_ctor_get(v_inst_2896_, 0);
v_toFunctor_2900_ = lean_ctor_get(v_toApplicative_2899_, 0);
v_map_2901_ = lean_ctor_get(v_toFunctor_2900_, 0);
lean_inc(v_map_2901_);
v___x_2902_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2898_);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2903_, 0, v___x_2902_);
lean_closure_set(v___f_2903_, 1, v_structName_2898_);
v___x_2904_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2896_, v_inst_2897_, v_structName_2898_);
v___x_2905_ = lean_apply_4(v_map_2901_, lean_box(0), lean_box(0), v___f_2903_, v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_structName_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_getAllParentStructures___redArg(v_inst_2907_, v_inst_2908_, v_structName_2909_);
return v___x_2910_;
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
