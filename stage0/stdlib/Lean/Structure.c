// Lean compiler output
// Module: Lean.Structure
// Imports: public import Lean.ProjFns public import Lean.Exception public import Init.While public import Init.Data.Range.Polymorphic.RangeIterator import Init.Data.Range.Polymorphic.Iterators
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
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
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
v___x_253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(size_t v_sz_262_, size_t v_i_263_, lean_object* v_bs_264_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_274_, lean_object* v_i_275_, lean_object* v_bs_276_){
_start:
{
size_t v_sz_boxed_277_; size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_sz_boxed_277_ = lean_unbox_usize(v_sz_274_);
lean_dec(v_sz_274_);
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_boxed_277_, v_i_boxed_278_, v_bs_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object* v_f_280_, lean_object* v_x1_281_, lean_object* v_x2_282_, lean_object* v_x3_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_apply_3(v_f_280_, v_x1_281_, v_x2_282_, v_x3_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_f_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_acc_289_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_f_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_298_, v_keys_299_, v_vals_300_, v_i_301_, v_acc_302_);
lean_dec_ref(v_vals_300_);
lean_dec_ref(v_keys_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_304_, lean_object* v_as_305_, size_t v_i_306_, size_t v_stop_307_, lean_object* v_b_308_){
_start:
{
lean_object* v___y_310_; uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_eq(v_i_306_, v_stop_307_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_array_uget_borrowed(v_as_305_, v_i_306_);
switch(lean_obj_tag(v___x_315_))
{
case 0:
{
lean_object* v_key_316_; lean_object* v_val_317_; lean_object* v___x_318_; 
v_key_316_ = lean_ctor_get(v___x_315_, 0);
v_val_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_f_304_);
lean_inc(v_val_317_);
lean_inc(v_key_316_);
v___x_318_ = lean_apply_3(v_f_304_, v_b_308_, v_key_316_, v_val_317_);
v___y_310_ = v___x_318_;
goto v___jp_309_;
}
case 1:
{
lean_object* v_node_319_; lean_object* v___x_320_; 
v_node_319_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_f_304_);
v___x_320_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_304_, v_node_319_, v_b_308_);
v___y_310_ = v___x_320_;
goto v___jp_309_;
}
default: 
{
v___y_310_ = v_b_308_;
goto v___jp_309_;
}
}
}
else
{
lean_dec(v_f_304_);
return v_b_308_;
}
v___jp_309_:
{
size_t v___x_311_; size_t v___x_312_; 
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_306_, v___x_311_);
v_i_306_ = v___x_312_;
v_b_308_ = v___y_310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_es_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_es_324_ = lean_ctor_get(v_x_322_, 0);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_array_get_size(v_es_324_);
v___x_327_ = lean_nat_dec_lt(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec(v_f_321_);
return v_x_323_;
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_326_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_321_, v_es_324_, v___x_328_, v___x_329_, v_x_323_);
return v___x_330_;
}
}
else
{
lean_object* v_ks_331_; lean_object* v_vs_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_ks_331_ = lean_ctor_get(v_x_322_, 0);
v_vs_332_ = lean_ctor_get(v_x_322_, 1);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_321_, v_ks_331_, v_vs_332_, v___x_333_, v_x_323_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_335_, v_x_336_, v_x_337_);
lean_dec_ref(v_x_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_339_, v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_347_, lean_object* v_f_348_, lean_object* v_init_349_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; 
v___f_350_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_350_, 0, v_f_348_);
v___x_351_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_350_, v_map_347_, v_init_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_352_, lean_object* v_f_353_, lean_object* v_init_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_352_, v_f_353_, v_init_354_);
lean_dec_ref(v_map_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_ps_356_, lean_object* v_k_357_, lean_object* v_v_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_k_357_);
lean_ctor_set(v___x_359_, 1, v_v_358_);
v___x_360_ = lean_array_push(v_ps_356_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_364_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___f_365_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_366_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___closed__1));
v___x_367_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_364_, v___f_365_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_m_368_);
lean_dec_ref(v_m_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_370_, lean_object* v_pivot_371_, lean_object* v_as_372_, lean_object* v_i_373_, lean_object* v_k_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_lt(v_k_374_, v_hi_370_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_k_374_);
v___x_376_ = lean_array_fswap(v_as_372_, v_i_373_, v_hi_370_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_i_373_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_fget_borrowed(v_as_372_, v_k_374_);
v___x_379_ = l_Lean_StructureInfo_lt(v___x_378_, v_pivot_371_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_k_374_, v___x_380_);
lean_dec(v_k_374_);
v_k_374_ = v___x_381_;
goto _start;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_array_fswap(v_as_372_, v_i_373_, v_k_374_);
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_i_373_, v___x_384_);
lean_dec(v_i_373_);
v___x_386_ = lean_nat_add(v_k_374_, v___x_384_);
lean_dec(v_k_374_);
v_as_372_ = v___x_383_;
v_i_373_ = v___x_385_;
v_k_374_ = v___x_386_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_388_, lean_object* v_pivot_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_k_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_388_, v_pivot_389_, v_as_390_, v_i_391_, v_k_392_);
lean_dec_ref(v_pivot_389_);
lean_dec(v_hi_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_394_, lean_object* v_as_395_, lean_object* v_lo_396_, lean_object* v_hi_397_){
_start:
{
lean_object* v___y_399_; uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_lt(v_lo_396_, v_hi_397_);
if (v___x_409_ == 0)
{
lean_dec(v_lo_396_);
return v_as_395_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_mid_412_; lean_object* v___y_414_; lean_object* v___y_420_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_410_ = lean_nat_add(v_lo_396_, v_hi_397_);
v___x_411_ = lean_unsigned_to_nat(1u);
v_mid_412_ = lean_nat_shiftr(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v___x_425_ = lean_array_fget_borrowed(v_as_395_, v_mid_412_);
v___x_426_ = lean_array_fget_borrowed(v_as_395_, v_lo_396_);
v___x_427_ = l_Lean_StructureInfo_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
v___y_420_ = v_as_395_;
goto v___jp_419_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_array_fswap(v_as_395_, v_lo_396_, v_mid_412_);
v___y_420_ = v___x_428_;
goto v___jp_419_;
}
v___jp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_array_fget_borrowed(v___y_414_, v_mid_412_);
v___x_416_ = lean_array_fget_borrowed(v___y_414_, v_hi_397_);
v___x_417_ = l_Lean_StructureInfo_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec(v_mid_412_);
v___y_399_ = v___y_414_;
goto v___jp_398_;
}
else
{
lean_object* v___x_418_; 
v___x_418_ = lean_array_fswap(v___y_414_, v_mid_412_, v_hi_397_);
lean_dec(v_mid_412_);
v___y_399_ = v___x_418_;
goto v___jp_398_;
}
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_array_fget_borrowed(v___y_420_, v_hi_397_);
v___x_422_ = lean_array_fget_borrowed(v___y_420_, v_lo_396_);
v___x_423_ = l_Lean_StructureInfo_lt(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
v___y_414_ = v___y_420_;
goto v___jp_413_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_array_fswap(v___y_420_, v_lo_396_, v_hi_397_);
v___y_414_ = v___x_424_;
goto v___jp_413_;
}
}
}
v___jp_398_:
{
lean_object* v_pivot_400_; lean_object* v___x_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; uint8_t v___x_404_; 
v_pivot_400_ = lean_array_fget(v___y_399_, v_hi_397_);
lean_inc_n(v_lo_396_, 2);
v___x_401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_397_, v_pivot_400_, v___y_399_, v_lo_396_, v_lo_396_);
lean_dec(v_pivot_400_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_fst_402_);
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v___x_401_);
v___x_404_ = lean_nat_dec_le(v_hi_397_, v_fst_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_394_, v_snd_403_, v_lo_396_, v_fst_402_);
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_fst_402_, v___x_406_);
lean_dec(v_fst_402_);
v_as_395_ = v___x_405_;
v_lo_396_ = v___x_407_;
goto _start;
}
else
{
lean_dec(v_fst_402_);
lean_dec(v_lo_396_);
return v_snd_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_429_, lean_object* v_as_430_, lean_object* v_lo_431_, lean_object* v_hi_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_429_, v_as_430_, v_lo_431_, v_hi_432_);
lean_dec(v_hi_432_);
lean_dec(v_n_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_434_, lean_object* v_x_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_snd_437_; lean_object* v___x_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___x_448_; 
v_snd_437_ = lean_ctor_get(v_s_436_, 1);
v___x_438_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_snd_437_);
v_sz_439_ = lean_array_size(v___x_438_);
v___x_440_ = ((size_t)0ULL);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_439_, v___x_440_, v___x_438_);
v___x_442_ = lean_array_get_size(v___x_441_);
v___x_448_ = lean_nat_dec_eq(v___x_442_, v___x_434_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___y_452_; uint8_t v___x_454_; 
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_sub(v___x_442_, v___x_449_);
v___x_454_ = lean_nat_dec_le(v___x_434_, v___x_450_);
if (v___x_454_ == 0)
{
lean_dec(v___x_434_);
lean_inc(v___x_450_);
v___y_452_ = v___x_450_;
goto v___jp_451_;
}
else
{
v___y_452_ = v___x_434_;
goto v___jp_451_;
}
v___jp_451_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_le(v___y_452_, v___x_450_);
if (v___x_453_ == 0)
{
lean_dec(v___x_450_);
lean_inc(v___y_452_);
v___y_444_ = v___y_452_;
v___y_445_ = v___y_452_;
goto v___jp_443_;
}
else
{
v___y_444_ = v___y_452_;
v___y_445_ = v___x_450_;
goto v___jp_443_;
}
}
}
else
{
lean_object* v___x_455_; 
lean_dec(v___x_434_);
lean_inc_ref_n(v___x_441_, 2);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_441_);
lean_ctor_set(v___x_455_, 1, v___x_441_);
lean_ctor_set(v___x_455_, 2, v___x_441_);
return v___x_455_;
}
v___jp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_442_, v___x_441_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_inc_ref_n(v___x_446_, 2);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_456_, lean_object* v_x_457_, lean_object* v_s_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_456_, v_x_457_, v_s_458_);
lean_dec_ref(v_s_458_);
lean_dec_ref(v_x_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_snd_462_; lean_object* v___x_463_; size_t v_sz_464_; size_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_snd_462_ = lean_ctor_get(v_x_461_, 1);
v___x_463_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_snd_462_);
v_sz_464_ = lean_array_size(v___x_463_);
v___x_465_ = ((size_t)0ULL);
v___x_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__1(v_sz_464_, v___x_465_, v___x_463_);
v___x_467_ = lean_array_get_size(v___x_466_);
v___x_468_ = lean_nat_dec_eq(v___x_467_, v___x_460_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___y_472_; uint8_t v___x_476_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_sub(v___x_467_, v___x_469_);
v___x_476_ = lean_nat_dec_le(v___x_460_, v___x_470_);
if (v___x_476_ == 0)
{
lean_dec(v___x_460_);
lean_inc(v___x_470_);
v___y_472_ = v___x_470_;
goto v___jp_471_;
}
else
{
v___y_472_ = v___x_460_;
goto v___jp_471_;
}
v___jp_471_:
{
uint8_t v___x_473_; 
v___x_473_ = lean_nat_dec_le(v___y_472_, v___x_470_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v___x_470_);
lean_inc(v___y_472_);
v___x_474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_467_, v___x_466_, v___y_472_, v___y_472_);
lean_dec(v___y_472_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v___x_467_, v___x_466_, v___y_472_, v___x_470_);
lean_dec(v___x_470_);
return v___x_475_;
}
}
}
else
{
lean_dec(v___x_460_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_477_, v_x_478_);
lean_dec_ref(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_ks_484_; lean_object* v_vs_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_509_; 
v_ks_484_ = lean_ctor_get(v_x_480_, 0);
v_vs_485_ = lean_ctor_get(v_x_480_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_509_ == 0)
{
v___x_487_ = v_x_480_;
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_vs_485_);
lean_inc(v_ks_484_);
lean_dec(v_x_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v_ks_484_);
v___x_490_ = lean_nat_dec_lt(v_x_481_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_x_481_);
v___x_491_ = lean_array_push(v_ks_484_, v_x_482_);
v___x_492_ = lean_array_push(v_vs_485_, v_x_483_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_492_);
lean_ctor_set(v___x_487_, 0, v___x_491_);
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v_k_x27_496_; uint8_t v___x_497_; 
v_k_x27_496_ = lean_array_fget_borrowed(v_ks_484_, v_x_481_);
v___x_497_ = lean_name_eq(v_x_482_, v_k_x27_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_499_; 
if (v_isShared_488_ == 0)
{
v___x_499_ = v___x_487_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_ks_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_vs_485_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_x_481_, v___x_500_);
lean_dec(v_x_481_);
v_x_480_ = v___x_499_;
v_x_481_ = v___x_501_;
goto _start;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_array_fset(v_ks_484_, v_x_481_, v_x_482_);
v___x_505_ = lean_array_fset(v_vs_485_, v_x_481_, v_x_483_);
lean_dec(v_x_481_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_505_);
lean_ctor_set(v___x_487_, 0, v___x_504_);
v___x_507_ = v___x_487_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_n_510_, lean_object* v_k_511_, lean_object* v_v_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_n_510_, v___x_513_, v_k_511_, v_v_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_x_516_, size_t v_x_517_, size_t v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_es_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_es_521_ = lean_ctor_get(v_x_516_, 0);
v___x_522_ = ((size_t)31ULL);
v___x_523_ = lean_usize_land(v_x_517_, v___x_522_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get_size(v_es_521_);
v___x_526_ = lean_nat_dec_lt(v_j_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v_j_524_);
lean_dec(v_x_520_);
lean_dec(v_x_519_);
return v_x_516_;
}
else
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_565_; 
lean_inc_ref(v_es_521_);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_x_516_, 0);
lean_dec(v_unused_566_);
v___x_528_ = v_x_516_;
v_isShared_529_ = v_isSharedCheck_565_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_565_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_v_530_; lean_object* v___x_531_; lean_object* v_xs_x27_532_; lean_object* v___y_534_; 
v_v_530_ = lean_array_fget(v_es_521_, v_j_524_);
v___x_531_ = lean_box(0);
v_xs_x27_532_ = lean_array_fset(v_es_521_, v_j_524_, v___x_531_);
switch(lean_obj_tag(v_v_530_))
{
case 0:
{
lean_object* v_key_539_; lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_550_; 
v_key_539_ = lean_ctor_get(v_v_530_, 0);
v_val_540_ = lean_ctor_get(v_v_530_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_550_ == 0)
{
v___x_542_ = v_v_530_;
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_inc(v_key_539_);
lean_dec(v_v_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v___x_544_; 
v___x_544_ = lean_name_eq(v_x_519_, v_key_539_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_del_object(v___x_542_);
v___x_545_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_539_, v_val_540_, v_x_519_, v_x_520_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___y_534_ = v___x_546_;
goto v___jp_533_;
}
else
{
lean_object* v___x_548_; 
lean_dec(v_val_540_);
lean_dec(v_key_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_x_520_);
lean_ctor_set(v___x_542_, 0, v_x_519_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_x_519_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_x_520_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_534_ = v___x_548_;
goto v___jp_533_;
}
}
}
}
case 1:
{
lean_object* v_node_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_563_; 
v_node_551_ = lean_ctor_get(v_v_530_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_563_ == 0)
{
v___x_553_ = v_v_530_;
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_node_551_);
lean_dec(v_v_530_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_555_ = ((size_t)5ULL);
v___x_556_ = lean_usize_shift_right(v_x_517_, v___x_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_x_518_, v___x_557_);
v___x_559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_node_551_, v___x_556_, v___x_558_, v_x_519_, v_x_520_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_559_);
v___x_561_ = v___x_553_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_534_ = v___x_561_;
goto v___jp_533_;
}
}
}
default: 
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_x_519_);
lean_ctor_set(v___x_564_, 1, v_x_520_);
v___y_534_ = v___x_564_;
goto v___jp_533_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_array_fset(v_xs_x27_532_, v_j_524_, v___y_534_);
lean_dec(v_j_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_535_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
else
{
lean_object* v_ks_567_; lean_object* v_vs_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
v_ks_567_ = lean_ctor_get(v_x_516_, 0);
v_vs_568_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_586_ == 0)
{
v___x_570_ = v_x_516_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_vs_568_);
lean_inc(v_ks_567_);
lean_dec(v_x_516_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_ks_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_vs_568_);
v___x_573_ = v_reuseFailAlloc_585_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v_newNode_574_; size_t v___x_575_; uint8_t v___x_576_; 
v_newNode_574_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_573_, v_x_519_, v_x_520_);
v___x_575_ = ((size_t)7ULL);
v___x_576_ = lean_usize_dec_le(v___x_575_, v_x_518_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_574_);
v___x_578_ = lean_unsigned_to_nat(4u);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
lean_dec(v___x_577_);
if (v___x_579_ == 0)
{
lean_object* v_ks_580_; lean_object* v_vs_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_ks_580_ = lean_ctor_get(v_newNode_574_, 0);
lean_inc_ref(v_ks_580_);
v_vs_581_ = lean_ctor_get(v_newNode_574_, 1);
lean_inc_ref(v_vs_581_);
lean_dec_ref(v_newNode_574_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___closed__0);
v___x_584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_x_518_, v_ks_580_, v_vs_581_, v___x_582_, v___x_583_);
lean_dec_ref(v_vs_581_);
lean_dec_ref(v_ks_580_);
return v___x_584_;
}
else
{
return v_newNode_574_;
}
}
else
{
return v_newNode_574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(size_t v_depth_587_, lean_object* v_keys_588_, lean_object* v_vals_589_, lean_object* v_i_590_, lean_object* v_entries_591_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_get_size(v_keys_588_);
v___x_593_ = lean_nat_dec_lt(v_i_590_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v_i_590_);
return v_entries_591_;
}
else
{
lean_object* v_k_594_; lean_object* v_v_595_; uint64_t v___y_597_; 
v_k_594_ = lean_array_fget_borrowed(v_keys_588_, v_i_590_);
v_v_595_ = lean_array_fget_borrowed(v_vals_589_, v_i_590_);
if (lean_obj_tag(v_k_594_) == 0)
{
uint64_t v___x_608_; 
v___x_608_ = 1723ULL;
v___y_597_ = v___x_608_;
goto v___jp_596_;
}
else
{
uint64_t v_hash_609_; 
v_hash_609_ = lean_ctor_get_uint64(v_k_594_, sizeof(void*)*2);
v___y_597_ = v_hash_609_;
goto v___jp_596_;
}
v___jp_596_:
{
size_t v_h_598_; size_t v___x_599_; lean_object* v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v_h_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_h_598_ = lean_uint64_to_usize(v___y_597_);
v___x_599_ = ((size_t)5ULL);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v_depth_587_, v___x_601_);
v___x_603_ = lean_usize_mul(v___x_599_, v___x_602_);
v_h_604_ = lean_usize_shift_right(v_h_598_, v___x_603_);
v___x_605_ = lean_nat_add(v_i_590_, v___x_600_);
lean_dec(v_i_590_);
lean_inc(v_v_595_);
lean_inc(v_k_594_);
v___x_606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_entries_591_, v_h_604_, v_depth_587_, v_k_594_, v_v_595_);
v_i_590_ = v___x_605_;
v_entries_591_ = v___x_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_depth_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_i_613_, lean_object* v_entries_614_){
_start:
{
size_t v_depth_boxed_615_; lean_object* v_res_616_; 
v_depth_boxed_615_ = lean_unbox_usize(v_depth_610_);
lean_dec(v_depth_610_);
v_res_616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_boxed_615_, v_keys_611_, v_vals_612_, v_i_613_, v_entries_614_);
lean_dec_ref(v_vals_612_);
lean_dec_ref(v_keys_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
size_t v_x_1801__boxed_622_; size_t v_x_1802__boxed_623_; lean_object* v_res_624_; 
v_x_1801__boxed_622_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_x_1802__boxed_623_ = lean_unbox_usize(v_x_619_);
lean_dec(v_x_619_);
v_res_624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_617_, v_x_1801__boxed_622_, v_x_1802__boxed_623_, v_x_620_, v_x_621_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
uint64_t v___y_629_; 
if (lean_obj_tag(v_x_626_) == 0)
{
uint64_t v___x_633_; 
v___x_633_ = 1723ULL;
v___y_629_ = v___x_633_;
goto v___jp_628_;
}
else
{
uint64_t v_hash_634_; 
v_hash_634_ = lean_ctor_get_uint64(v_x_626_, sizeof(void*)*2);
v___y_629_ = v_hash_634_;
goto v___jp_628_;
}
v___jp_628_:
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_uint64_to_usize(v___y_629_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_625_, v___x_630_, v___x_631_, v_x_626_, v_x_627_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_635_, lean_object* v_x_636_, lean_object* v_e_637_){
_start:
{
lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_647_; 
v_snd_638_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v_x_636_, 0);
lean_dec(v_unused_648_);
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_structName_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v_structName_642_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_structName_642_);
v___x_643_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(v_snd_638_, v_structName_642_, v_e_637_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_643_);
lean_ctor_set(v___x_640_, 0, v___x_635_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(lean_object* v___x_655_, lean_object* v_x_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_655_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v___x_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(v___x_660_, v_x_661_, v___y_662_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_x_661_);
return v_res_664_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__1, &l_Lean_instInhabitedStructureState_default___closed__1_once, _init_l_Lean_instInhabitedStructureState_default___closed__1);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_697_; lean_object* v___f_698_; 
v___x_697_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_698_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_698_, 0, v___x_697_);
return v___f_698_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_699_; lean_object* v___f_700_; 
v___x_699_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_700_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_700_, 0, v___x_699_);
return v___f_700_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_701_ = 1;
v___x_702_ = 0;
v___x_703_ = lean_box(0);
v___x_704_ = lean_box(2);
v___f_705_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_706_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_707_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___f_708_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___f_709_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_710_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___x_711_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___f_709_);
lean_ctor_set(v___x_711_, 2, v___f_708_);
lean_ctor_set(v___x_711_, 3, v___f_707_);
lean_ctor_set(v___x_711_, 4, v___f_706_);
lean_ctor_set(v___x_711_, 5, v___f_705_);
lean_ctor_set(v___x_711_, 6, v___x_704_);
lean_ctor_set(v___x_711_, 7, v___x_703_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*8, v___x_702_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*8 + 1, v___x_701_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___f_712_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_));
v___x_713_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___f_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_);
v___x_717_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2____boxed(lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2_();
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_720_, lean_object* v_m_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___redArg(v_m_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_723_, lean_object* v_m_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0(v_00_u03b2_723_, v_m_724_);
lean_dec_ref(v_m_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2(lean_object* v_n_726_, lean_object* v_as_727_, lean_object* v_lo_728_, lean_object* v_hi_729_, lean_object* v_w_730_, lean_object* v_hlo_731_, lean_object* v_hhi_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___redArg(v_n_726_, v_as_727_, v_lo_728_, v_hi_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_734_, lean_object* v_as_735_, lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_w_738_, lean_object* v_hlo_739_, lean_object* v_hhi_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2(v_n_734_, v_as_735_, v_lo_736_, v_hi_737_, v_w_738_, v_hlo_739_, v_hhi_740_);
lean_dec(v_hi_737_);
lean_dec(v_n_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3___redArg(v_x_743_, v_x_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_747_, lean_object* v_00_u03b2_748_, lean_object* v_map_749_, lean_object* v_f_750_, lean_object* v_init_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_749_, v_f_750_, v_init_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_753_, lean_object* v_00_u03b2_754_, lean_object* v_map_755_, lean_object* v_f_756_, lean_object* v_init_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_753_, v_00_u03b2_754_, v_map_755_, v_f_756_, v_init_757_);
lean_dec_ref(v_map_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_759_, lean_object* v_lo_760_, lean_object* v_hi_761_, lean_object* v_hhi_762_, lean_object* v_pivot_763_, lean_object* v_as_764_, lean_object* v_i_765_, lean_object* v_k_766_, lean_object* v_ilo_767_, lean_object* v_ik_768_, lean_object* v_w_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_761_, v_pivot_763_, v_as_764_, v_i_765_, v_k_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_771_, lean_object* v_lo_772_, lean_object* v_hi_773_, lean_object* v_hhi_774_, lean_object* v_pivot_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_k_778_, lean_object* v_ilo_779_, lean_object* v_ik_780_, lean_object* v_w_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__2_spec__3(v_n_771_, v_lo_772_, v_hi_773_, v_hhi_774_, v_pivot_775_, v_as_776_, v_i_777_, v_k_778_, v_ilo_779_, v_ik_780_, v_w_781_);
lean_dec_ref(v_pivot_775_);
lean_dec(v_hi_773_);
lean_dec(v_lo_772_);
lean_dec(v_n_771_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, size_t v_x_785_, size_t v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___redArg(v_x_784_, v_x_785_, v_x_786_, v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
size_t v_x_2195__boxed_796_; size_t v_x_2196__boxed_797_; lean_object* v_res_798_; 
v_x_2195__boxed_796_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_x_2196__boxed_797_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_res_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_790_, v_x_791_, v_x_2195__boxed_796_, v_x_2196__boxed_797_, v_x_794_, v_x_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_799_, lean_object* v_f_800_, lean_object* v_init_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_800_, v_map_799_, v_init_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_803_, lean_object* v_f_804_, lean_object* v_init_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_803_, v_f_804_, v_init_805_);
lean_dec_ref(v_map_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_807_, lean_object* v_00_u03b2_808_, lean_object* v_map_809_, lean_object* v_f_810_, lean_object* v_init_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_810_, v_map_809_, v_init_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_813_, lean_object* v_00_u03b2_814_, lean_object* v_map_815_, lean_object* v_f_816_, lean_object* v_init_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_813_, v_00_u03b2_814_, v_map_815_, v_f_816_, v_init_817_);
lean_dec_ref(v_map_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_819_, lean_object* v_n_820_, lean_object* v_k_821_, lean_object* v_v_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_n_820_, v_k_821_, v_v_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b2_824_, size_t v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_depth_825_, v_keys_826_, v_vals_827_, v_i_829_, v_entries_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_832_, lean_object* v_depth_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_entries_838_){
_start:
{
size_t v_depth_boxed_839_; lean_object* v_res_840_; 
v_depth_boxed_839_ = lean_unbox_usize(v_depth_833_);
lean_dec(v_depth_833_);
v_res_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b2_832_, v_depth_boxed_839_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_entries_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_841_, lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_f_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_844_, v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_848_, lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_f_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_848_, v_00_u03b1_849_, v_00_u03b2_850_, v_f_851_, v_x_852_, v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__9___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_00_u03c3_863_, lean_object* v_f_864_, lean_object* v_as_865_, size_t v_i_866_, size_t v_stop_867_, lean_object* v_b_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_864_, v_as_865_, v_i_866_, v_stop_867_, v_b_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_00_u03c3_872_, lean_object* v_f_873_, lean_object* v_as_874_, lean_object* v_i_875_, lean_object* v_stop_876_, lean_object* v_b_877_){
_start:
{
size_t v_i_boxed_878_; size_t v_stop_boxed_879_; lean_object* v_res_880_; 
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_stop_boxed_879_ = lean_unbox_usize(v_stop_876_);
lean_dec(v_stop_876_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_870_, v_00_u03b2_871_, v_00_u03c3_872_, v_f_873_, v_as_874_, v_i_boxed_878_, v_stop_boxed_879_, v_b_877_);
lean_dec_ref(v_as_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03c3_881_, lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_f_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_heq_887_, lean_object* v_i_888_, lean_object* v_acc_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___redArg(v_f_884_, v_keys_885_, v_vals_886_, v_i_888_, v_acc_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03c3_891_, lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_f_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_acc_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_1029248034____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_00_u03c3_891_, v_00_u03b1_892_, v_00_u03b2_893_, v_f_894_, v_keys_895_, v_vals_896_, v_heq_897_, v_i_898_, v_acc_899_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3(lean_object* v_env_908_, lean_object* v_msg_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_panic_fn_borrowed(v_env_908_, v_msg_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_registerStructure_spec__3___boxed(lean_object* v_env_911_, lean_object* v_msg_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_panic___at___00Lean_registerStructure_spec__3(v_env_911_, v_msg_912_);
lean_dec_ref(v_env_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure___lam__0(lean_object* v_addEntryFn_914_, lean_object* v___x_915_, lean_object* v_s_916_){
_start:
{
lean_object* v_importedEntries_917_; lean_object* v_state_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_importedEntries_917_ = lean_ctor_get(v_s_916_, 0);
v_state_918_ = lean_ctor_get(v_s_916_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_s_916_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v_s_916_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_state_918_);
lean_inc(v_importedEntries_917_);
lean_dec(v_s_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_state_922_; lean_object* v___x_924_; 
v_state_922_ = lean_apply_2(v_addEntryFn_914_, v_state_918_, v___x_915_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v_state_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_importedEntries_917_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_state_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(size_t v_sz_927_, size_t v_i_928_, lean_object* v_bs_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_930_ == 0)
{
return v_bs_929_;
}
else
{
lean_object* v_v_931_; lean_object* v_fieldName_932_; lean_object* v___x_933_; lean_object* v_bs_x27_934_; size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; 
v_v_931_ = lean_array_uget_borrowed(v_bs_929_, v_i_928_);
v_fieldName_932_ = lean_ctor_get(v_v_931_, 0);
lean_inc(v_fieldName_932_);
v___x_933_ = lean_unsigned_to_nat(0u);
v_bs_x27_934_ = lean_array_uset(v_bs_929_, v_i_928_, v___x_933_);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_928_, v___x_935_);
v___x_937_ = lean_array_uset(v_bs_x27_934_, v_i_928_, v_fieldName_932_);
v_i_928_ = v___x_936_;
v_bs_929_ = v___x_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_sz_939_, lean_object* v_i_940_, lean_object* v_bs_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_939_);
lean_dec(v_sz_939_);
v_i_boxed_943_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(v_sz_boxed_942_, v_i_boxed_943_, v_bs_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(lean_object* v_hi_945_, lean_object* v_pivot_946_, lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_k_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_lt(v_k_949_, v_hi_945_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_k_949_);
v___x_951_ = lean_array_fswap(v_as_947_, v_i_948_, v_hi_945_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_i_948_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_953_ = lean_array_fget_borrowed(v_as_947_, v_k_949_);
v___x_954_ = l_Lean_StructureFieldInfo_lt(v___x_953_, v_pivot_946_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_add(v_k_949_, v___x_955_);
lean_dec(v_k_949_);
v_k_949_ = v___x_956_;
goto _start;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = lean_array_fswap(v_as_947_, v_i_948_, v_k_949_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v_i_948_, v___x_959_);
lean_dec(v_i_948_);
v___x_961_ = lean_nat_add(v_k_949_, v___x_959_);
lean_dec(v_k_949_);
v_as_947_ = v___x_958_;
v_i_948_ = v___x_960_;
v_k_949_ = v___x_961_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg___boxed(lean_object* v_hi_963_, lean_object* v_pivot_964_, lean_object* v_as_965_, lean_object* v_i_966_, lean_object* v_k_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_963_, v_pivot_964_, v_as_965_, v_i_966_, v_k_967_);
lean_dec_ref(v_pivot_964_);
lean_dec(v_hi_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(lean_object* v_n_969_, lean_object* v_as_970_, lean_object* v_lo_971_, lean_object* v_hi_972_){
_start:
{
lean_object* v___y_974_; uint8_t v___x_984_; 
v___x_984_ = lean_nat_dec_lt(v_lo_971_, v_hi_972_);
if (v___x_984_ == 0)
{
lean_dec(v_lo_971_);
return v_as_970_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_mid_987_; lean_object* v___y_989_; lean_object* v___y_995_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_985_ = lean_nat_add(v_lo_971_, v_hi_972_);
v___x_986_ = lean_unsigned_to_nat(1u);
v_mid_987_ = lean_nat_shiftr(v___x_985_, v___x_986_);
lean_dec(v___x_985_);
v___x_1000_ = lean_array_fget_borrowed(v_as_970_, v_mid_987_);
v___x_1001_ = lean_array_fget_borrowed(v_as_970_, v_lo_971_);
v___x_1002_ = l_Lean_StructureFieldInfo_lt(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
v___y_995_ = v_as_970_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_array_fswap(v_as_970_, v_lo_971_, v_mid_987_);
v___y_995_ = v___x_1003_;
goto v___jp_994_;
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_array_fget_borrowed(v___y_989_, v_mid_987_);
v___x_991_ = lean_array_fget_borrowed(v___y_989_, v_hi_972_);
v___x_992_ = l_Lean_StructureFieldInfo_lt(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v_mid_987_);
v___y_974_ = v___y_989_;
goto v___jp_973_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = lean_array_fswap(v___y_989_, v_mid_987_, v_hi_972_);
lean_dec(v_mid_987_);
v___y_974_ = v___x_993_;
goto v___jp_973_;
}
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_996_ = lean_array_fget_borrowed(v___y_995_, v_hi_972_);
v___x_997_ = lean_array_fget_borrowed(v___y_995_, v_lo_971_);
v___x_998_ = l_Lean_StructureFieldInfo_lt(v___x_996_, v___x_997_);
if (v___x_998_ == 0)
{
v___y_989_ = v___y_995_;
goto v___jp_988_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_array_fswap(v___y_995_, v_lo_971_, v_hi_972_);
v___y_989_ = v___x_999_;
goto v___jp_988_;
}
}
}
v___jp_973_:
{
lean_object* v_pivot_975_; lean_object* v___x_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; uint8_t v___x_979_; 
v_pivot_975_ = lean_array_fget(v___y_974_, v_hi_972_);
lean_inc_n(v_lo_971_, 2);
v___x_976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_972_, v_pivot_975_, v___y_974_, v_lo_971_, v_lo_971_);
lean_dec(v_pivot_975_);
v_fst_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_977_);
v_snd_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_978_);
lean_dec_ref(v___x_976_);
v___x_979_ = lean_nat_dec_le(v_hi_972_, v_fst_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_969_, v_snd_978_, v_lo_971_, v_fst_977_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_fst_977_, v___x_981_);
lean_dec(v_fst_977_);
v_as_970_ = v___x_980_;
v_lo_971_ = v___x_982_;
goto _start;
}
else
{
lean_dec(v_fst_977_);
lean_dec(v_lo_971_);
return v_snd_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg___boxed(lean_object* v_n_1004_, lean_object* v_as_1005_, lean_object* v_lo_1006_, lean_object* v_hi_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_1004_, v_as_1005_, v_lo_1006_, v_hi_1007_);
lean_dec(v_hi_1007_);
lean_dec(v_n_1004_);
return v_res_1008_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_array_get_size(v_keys_1009_);
v___x_1013_ = lean_nat_dec_lt(v_i_1010_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_dec(v_i_1010_);
return v___x_1013_;
}
else
{
lean_object* v_k_x27_1014_; uint8_t v___x_1015_; 
v_k_x27_1014_ = lean_array_fget_borrowed(v_keys_1009_, v_i_1010_);
v___x_1015_ = lean_name_eq(v_k_1011_, v_k_x27_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_1010_, v___x_1016_);
lean_dec(v_i_1010_);
v_i_1010_ = v___x_1017_;
goto _start;
}
else
{
lean_dec(v_i_1010_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1019_, lean_object* v_i_1020_, lean_object* v_k_1021_){
_start:
{
uint8_t v_res_1022_; lean_object* v_r_1023_; 
v_res_1022_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_keys_1019_, v_i_1020_, v_k_1021_);
lean_dec(v_k_1021_);
lean_dec_ref(v_keys_1019_);
v_r_1023_ = lean_box(v_res_1022_);
return v_r_1023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(lean_object* v_x_1024_, size_t v_x_1025_, lean_object* v_x_1026_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v_es_1027_; lean_object* v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v_j_1031_; lean_object* v___x_1032_; 
v_es_1027_ = lean_ctor_get(v_x_1024_, 0);
v___x_1028_ = lean_box(2);
v___x_1029_ = ((size_t)31ULL);
v___x_1030_ = lean_usize_land(v_x_1025_, v___x_1029_);
v_j_1031_ = lean_usize_to_nat(v___x_1030_);
v___x_1032_ = lean_array_get_borrowed(v___x_1028_, v_es_1027_, v_j_1031_);
lean_dec(v_j_1031_);
switch(lean_obj_tag(v___x_1032_))
{
case 0:
{
lean_object* v_key_1033_; uint8_t v___x_1034_; 
v_key_1033_ = lean_ctor_get(v___x_1032_, 0);
v___x_1034_ = lean_name_eq(v_x_1026_, v_key_1033_);
return v___x_1034_;
}
case 1:
{
lean_object* v_node_1035_; size_t v___x_1036_; size_t v___x_1037_; 
v_node_1035_ = lean_ctor_get(v___x_1032_, 0);
v___x_1036_ = ((size_t)5ULL);
v___x_1037_ = lean_usize_shift_right(v_x_1025_, v___x_1036_);
v_x_1024_ = v_node_1035_;
v_x_1025_ = v___x_1037_;
goto _start;
}
default: 
{
uint8_t v___x_1039_; 
v___x_1039_ = 0;
return v___x_1039_;
}
}
}
else
{
lean_object* v_ks_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_ks_1040_ = lean_ctor_get(v_x_1024_, 0);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_ks_1040_, v___x_1041_, v_x_1026_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg___boxed(lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
size_t v_x_651__boxed_1046_; uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_x_651__boxed_1046_ = lean_unbox_usize(v_x_1044_);
lean_dec(v_x_1044_);
v_res_1047_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1043_, v_x_651__boxed_1046_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec_ref(v_x_1043_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
uint64_t v___y_1052_; 
if (lean_obj_tag(v_x_1050_) == 0)
{
uint64_t v___x_1055_; 
v___x_1055_ = 1723ULL;
v___y_1052_ = v___x_1055_;
goto v___jp_1051_;
}
else
{
uint64_t v_hash_1056_; 
v_hash_1056_ = lean_ctor_get_uint64(v_x_1050_, sizeof(void*)*2);
v___y_1052_ = v_hash_1056_;
goto v___jp_1051_;
}
v___jp_1051_:
{
size_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_uint64_to_usize(v___y_1052_);
v___x_1054_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1049_, v___x_1053_, v_x_1050_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg___boxed(lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_x_1057_, v_x_1058_);
lean_dec(v_x_1058_);
lean_dec_ref(v_x_1057_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
static lean_object* _init_l_Lean_registerStructure___closed__0(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = l_Lean_instInhabitedStructureState_default;
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_1070_, lean_object* v_e_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v_toEnvExtension_1073_; lean_object* v_addEntryFn_1074_; lean_object* v_asyncMode_1075_; uint8_t v_logWrites_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v_snd_1081_; lean_object* v_structName_1082_; lean_object* v_fields_1083_; uint8_t v___x_1084_; 
v___x_1072_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1073_ = lean_ctor_get(v___x_1072_, 0);
v_addEntryFn_1074_ = lean_ctor_get(v___x_1072_, 3);
v_asyncMode_1075_ = lean_ctor_get(v_toEnvExtension_1073_, 2);
v_logWrites_1076_ = lean_ctor_get_uint8(v_toEnvExtension_1073_, sizeof(void*)*6);
v___x_1077_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___x_1078_ = lean_box(0);
v___x_1079_ = 0;
lean_inc_ref(v_env_1070_);
v___x_1080_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1077_, v___x_1072_, v_env_1070_, v_asyncMode_1075_, v___x_1078_, v___x_1079_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec(v___x_1080_);
v_structName_1082_ = lean_ctor_get(v_e_1071_, 0);
lean_inc(v_structName_1082_);
v_fields_1083_ = lean_ctor_get(v_e_1071_, 1);
lean_inc_ref(v_fields_1083_);
lean_dec_ref(v_e_1071_);
v___x_1084_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_snd_1081_, v_structName_1082_);
lean_dec(v_snd_1081_);
if (v___x_1084_ == 0)
{
size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___y_1089_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_sz_1085_ = lean_array_size(v_fields_1083_);
v___x_1086_ = ((size_t)0ULL);
lean_inc_ref(v_fields_1083_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__1(v_sz_1085_, v___x_1086_, v_fields_1083_);
v___x_1097_ = lean_array_get_size(v_fields_1083_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_nat_dec_eq(v___x_1097_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; uint8_t v___x_1109_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_sub(v___x_1097_, v___x_1104_);
v___x_1109_ = lean_nat_dec_le(v___x_1102_, v___x_1105_);
if (v___x_1109_ == 0)
{
lean_inc(v___x_1105_);
v___y_1107_ = v___x_1105_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1102_;
goto v___jp_1106_;
}
v___jp_1106_:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_nat_dec_le(v___y_1107_, v___x_1105_);
if (v___x_1108_ == 0)
{
lean_dec(v___x_1105_);
lean_inc(v___y_1107_);
v___y_1099_ = v___y_1107_;
v___y_1100_ = v___y_1107_;
goto v___jp_1098_;
}
else
{
v___y_1099_ = v___y_1107_;
v___y_1100_ = v___x_1105_;
goto v___jp_1098_;
}
}
}
else
{
v___y_1089_ = v_fields_1083_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; uint8_t v___x_1093_; 
v___x_1090_ = ((lean_object*)(l_Lean_registerStructure___closed__1));
lean_inc(v_structName_1082_);
v___x_1091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1091_, 0, v_structName_1082_);
lean_ctor_set(v___x_1091_, 1, v___x_1087_);
lean_ctor_set(v___x_1091_, 2, v___y_1089_);
lean_ctor_set(v___x_1091_, 3, v___x_1090_);
lean_inc(v_addEntryFn_1074_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_registerStructure___lam__0), 3, 2);
lean_closure_set(v___f_1092_, 0, v_addEntryFn_1074_);
lean_closure_set(v___f_1092_, 1, v___x_1091_);
v___x_1093_ = 1;
if (v_logWrites_1076_ == 0)
{
lean_object* v___x_1094_; 
lean_dec(v_structName_1082_);
lean_inc_ref(v_toEnvExtension_1073_);
v___x_1094_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1073_, v_env_1070_, v___f_1092_, v_asyncMode_1075_, v___x_1078_, v___x_1093_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = l_Lean_Environment_logDeclChange(v_env_1070_, v_structName_1082_);
lean_inc_ref(v_toEnvExtension_1073_);
v___x_1096_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1073_, v___x_1095_, v___f_1092_, v_asyncMode_1075_, v___x_1078_, v___x_1093_);
return v___x_1096_;
}
}
v___jp_1098_:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v___x_1097_, v_fields_1083_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
v___y_1089_ = v___x_1101_;
goto v___jp_1088_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v_fields_1083_);
v___x_1110_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1111_ = ((lean_object*)(l_Lean_registerStructure___closed__3));
v___x_1112_ = lean_unsigned_to_nat(116u);
v___x_1113_ = lean_unsigned_to_nat(4u);
v___x_1114_ = ((lean_object*)(l_Lean_registerStructure___closed__4));
v___x_1115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_structName_1082_, v___x_1084_);
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_registerStructure___closed__5));
v___x_1118_ = lean_string_append(v___x_1116_, v___x_1117_);
v___x_1119_ = l_mkPanicMessageWithDecl(v___x_1110_, v___x_1111_, v___x_1112_, v___x_1113_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = lean_panic_fn_borrowed(v_env_1070_, v___x_1119_);
lean_dec_ref(v_env_1070_);
return v___x_1120_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___redArg(v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0(v_00_u03b2_1125_, v_x_1126_, v_x_1127_);
lean_dec(v_x_1127_);
lean_dec_ref(v_x_1126_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2(lean_object* v_n_1130_, lean_object* v_as_1131_, lean_object* v_lo_1132_, lean_object* v_hi_1133_, lean_object* v_w_1134_, lean_object* v_hlo_1135_, lean_object* v_hhi_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___redArg(v_n_1130_, v_as_1131_, v_lo_1132_, v_hi_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2___boxed(lean_object* v_n_1138_, lean_object* v_as_1139_, lean_object* v_lo_1140_, lean_object* v_hi_1141_, lean_object* v_w_1142_, lean_object* v_hlo_1143_, lean_object* v_hhi_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2(v_n_1138_, v_as_1139_, v_lo_1140_, v_hi_1141_, v_w_1142_, v_hlo_1143_, v_hhi_1144_);
lean_dec(v_hi_1141_);
lean_dec(v_n_1138_);
return v_res_1145_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(lean_object* v_00_u03b2_1146_, lean_object* v_x_1147_, size_t v_x_1148_, lean_object* v_x_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___redArg(v_x_1147_, v_x_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
size_t v_x_828__boxed_1155_; uint8_t v_res_1156_; lean_object* v_r_1157_; 
v_x_828__boxed_1155_ = lean_unbox_usize(v_x_1153_);
lean_dec(v_x_1153_);
v_res_1156_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0(v_00_u03b2_1151_, v_x_1152_, v_x_828__boxed_1155_, v_x_1154_);
lean_dec(v_x_1154_);
lean_dec_ref(v_x_1152_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3(lean_object* v_n_1158_, lean_object* v_lo_1159_, lean_object* v_hi_1160_, lean_object* v_hhi_1161_, lean_object* v_pivot_1162_, lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_k_1165_, lean_object* v_ilo_1166_, lean_object* v_ik_1167_, lean_object* v_w_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___redArg(v_hi_1160_, v_pivot_1162_, v_as_1163_, v_i_1164_, v_k_1165_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3___boxed(lean_object* v_n_1170_, lean_object* v_lo_1171_, lean_object* v_hi_1172_, lean_object* v_hhi_1173_, lean_object* v_pivot_1174_, lean_object* v_as_1175_, lean_object* v_i_1176_, lean_object* v_k_1177_, lean_object* v_ilo_1178_, lean_object* v_ik_1179_, lean_object* v_w_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__2_spec__3(v_n_1170_, v_lo_1171_, v_hi_1172_, v_hhi_1173_, v_pivot_1174_, v_as_1175_, v_i_1176_, v_k_1177_, v_ilo_1178_, v_ik_1179_, v_w_1180_);
lean_dec_ref(v_pivot_1174_);
lean_dec(v_hi_1172_);
lean_dec(v_lo_1171_);
lean_dec(v_n_1170_);
return v_res_1181_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1182_, lean_object* v_keys_1183_, lean_object* v_vals_1184_, lean_object* v_heq_1185_, lean_object* v_i_1186_, lean_object* v_k_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___redArg(v_keys_1183_, v_i_1186_, v_k_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1189_, lean_object* v_keys_1190_, lean_object* v_vals_1191_, lean_object* v_heq_1192_, lean_object* v_i_1193_, lean_object* v_k_1194_){
_start:
{
uint8_t v_res_1195_; lean_object* v_r_1196_; 
v_res_1195_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_registerStructure_spec__0_spec__0_spec__2(v_00_u03b2_1189_, v_keys_1190_, v_vals_1191_, v_heq_1192_, v_i_1193_, v_k_1194_);
lean_dec(v_k_1194_);
lean_dec_ref(v_vals_1191_);
lean_dec_ref(v_keys_1190_);
v_r_1196_ = lean_box(v_res_1195_);
return v_r_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v_val_1197_, lean_object* v_parentInfo_1198_, lean_object* v_addEntryFn_1199_, uint8_t v_logWrites_1200_, lean_object* v_toEnvExtension_1201_, lean_object* v_asyncMode_1202_, lean_object* v___x_1203_, lean_object* v_structName_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_structName_1206_; lean_object* v_fieldNames_1207_; lean_object* v_fieldInfo_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1220_; 
v_structName_1206_ = lean_ctor_get(v_val_1197_, 0);
v_fieldNames_1207_ = lean_ctor_get(v_val_1197_, 1);
v_fieldInfo_1208_ = lean_ctor_get(v_val_1197_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_val_1197_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_val_1197_, 3);
lean_dec(v_unused_1221_);
v___x_1210_ = v_val_1197_;
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_fieldInfo_1208_);
lean_inc(v_fieldNames_1207_);
lean_inc(v_structName_1206_);
lean_dec(v_val_1197_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 3, v_parentInfo_1198_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_structName_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_fieldNames_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_fieldInfo_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_parentInfo_1198_);
v___x_1213_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___f_1214_; uint8_t v___x_1215_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_registerStructure___lam__0), 3, 2);
lean_closure_set(v___f_1214_, 0, v_addEntryFn_1199_);
lean_closure_set(v___f_1214_, 1, v___x_1213_);
v___x_1215_ = 1;
if (v_logWrites_1200_ == 0)
{
lean_object* v___x_1216_; 
lean_dec(v_structName_1204_);
v___x_1216_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1201_, v_x_1205_, v___f_1214_, v_asyncMode_1202_, v___x_1203_, v___x_1215_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = l_Lean_Environment_logDeclChange(v_x_1205_, v_structName_1204_);
v___x_1218_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1201_, v___x_1217_, v___f_1214_, v_asyncMode_1202_, v___x_1203_, v___x_1215_);
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1___boxed(lean_object* v_val_1222_, lean_object* v_parentInfo_1223_, lean_object* v_addEntryFn_1224_, lean_object* v_logWrites_1225_, lean_object* v_toEnvExtension_1226_, lean_object* v_asyncMode_1227_, lean_object* v___x_1228_, lean_object* v_structName_1229_, lean_object* v_x_1230_){
_start:
{
uint8_t v_logWrites_boxed_1231_; lean_object* v_res_1232_; 
v_logWrites_boxed_1231_ = lean_unbox(v_logWrites_1225_);
v_res_1232_ = l_Lean_setStructureParents___redArg___lam__1(v_val_1222_, v_parentInfo_1223_, v_addEntryFn_1224_, v_logWrites_boxed_1231_, v_toEnvExtension_1226_, v_asyncMode_1227_, v___x_1228_, v_structName_1229_, v_x_1230_);
lean_dec(v_asyncMode_1227_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__0___closed__0));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__0___closed__2));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v___x_1239_, lean_object* v___x_1240_, lean_object* v___x_1241_, lean_object* v_structName_1242_, lean_object* v_parentInfo_1243_, lean_object* v_modifyEnv_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_____do__lift_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v_toEnvExtension_1249_; lean_object* v_addEntryFn_1250_; lean_object* v_asyncMode_1251_; uint8_t v_logWrites_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1273_; 
v___x_1248_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1249_ = lean_ctor_get(v___x_1248_, 0);
v_addEntryFn_1250_ = lean_ctor_get(v___x_1248_, 3);
v_asyncMode_1251_ = lean_ctor_get(v_toEnvExtension_1249_, 2);
v_logWrites_1252_ = lean_ctor_get_uint8(v_toEnvExtension_1249_, sizeof(void*)*6);
v___x_1253_ = lean_box(0);
v___x_1254_ = 0;
v___x_1255_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1239_, v___x_1248_, v_____do__lift_1247_, v_asyncMode_1251_, v___x_1253_, v___x_1254_);
v_snd_1256_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1274_);
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1273_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; 
lean_inc(v_structName_1242_);
v___x_1260_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1240_, v___x_1241_, v_snd_1256_, v_structName_1242_);
lean_dec(v_snd_1256_);
if (lean_obj_tag(v___x_1260_) == 1)
{
lean_object* v_val_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
lean_del_object(v___x_1258_);
lean_dec_ref(v_inst_1246_);
lean_dec_ref(v_inst_1245_);
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = lean_box(v_logWrites_1252_);
lean_inc(v_asyncMode_1251_);
lean_inc_ref(v_toEnvExtension_1249_);
lean_inc(v_addEntryFn_1250_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_1263_, 0, v_val_1261_);
lean_closure_set(v___f_1263_, 1, v_parentInfo_1243_);
lean_closure_set(v___f_1263_, 2, v_addEntryFn_1250_);
lean_closure_set(v___f_1263_, 3, v___x_1262_);
lean_closure_set(v___f_1263_, 4, v_toEnvExtension_1249_);
lean_closure_set(v___f_1263_, 5, v_asyncMode_1251_);
lean_closure_set(v___f_1263_, 6, v___x_1253_);
lean_closure_set(v___f_1263_, 7, v_structName_1242_);
v___x_1264_ = lean_apply_1(v_modifyEnv_1244_, v___f_1263_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec(v___x_1260_);
lean_dec(v_modifyEnv_1244_);
lean_dec_ref(v_parentInfo_1243_);
v___x_1265_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__0___closed__1, &l_Lean_setStructureParents___redArg___lam__0___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__0___closed__1);
v___x_1266_ = l_Lean_MessageData_ofName(v_structName_1242_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 7);
lean_ctor_set(v___x_1258_, 1, v___x_1266_);
lean_ctor_set(v___x_1258_, 0, v___x_1265_);
v___x_1268_ = v___x_1258_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__0___closed__3, &l_Lean_setStructureParents___redArg___lam__0___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__0___closed__3);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_throwError___redArg(v_inst_1245_, v_inst_1246_, v___x_1270_);
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_structName_1280_, lean_object* v_parentInfo_1281_){
_start:
{
lean_object* v_toBind_1282_; lean_object* v_getEnv_1283_; lean_object* v_modifyEnv_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; 
v_toBind_1282_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc(v_toBind_1282_);
v_getEnv_1283_ = lean_ctor_get(v_inst_1278_, 0);
lean_inc(v_getEnv_1283_);
v_modifyEnv_1284_ = lean_ctor_get(v_inst_1278_, 1);
lean_inc(v_modifyEnv_1284_);
lean_dec_ref(v_inst_1278_);
v___x_1285_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1286_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1287_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0), 9, 8);
lean_closure_set(v___f_1288_, 0, v___x_1287_);
lean_closure_set(v___f_1288_, 1, v___x_1285_);
lean_closure_set(v___f_1288_, 2, v___x_1286_);
lean_closure_set(v___f_1288_, 3, v_structName_1280_);
lean_closure_set(v___f_1288_, 4, v_parentInfo_1281_);
lean_closure_set(v___f_1288_, 5, v_modifyEnv_1284_);
lean_closure_set(v___f_1288_, 6, v_inst_1277_);
lean_closure_set(v___f_1288_, 7, v_inst_1279_);
v___x_1289_ = lean_apply_4(v_toBind_1282_, lean_box(0), lean_box(0), v_getEnv_1283_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_structName_1294_, lean_object* v_parentInfo_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_setStructureParents___redArg(v_inst_1291_, v_inst_1292_, v_inst_1293_, v_structName_1294_, v_parentInfo_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1297_, lean_object* v_k_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_m_1303_; lean_object* v_a_1304_; uint8_t v___x_1305_; 
v___x_1301_ = lean_nat_add(v_x_1299_, v_x_1300_);
v___x_1302_ = lean_unsigned_to_nat(1u);
v_m_1303_ = lean_nat_shiftr(v___x_1301_, v___x_1302_);
lean_dec(v___x_1301_);
v_a_1304_ = lean_array_fget_borrowed(v_as_1297_, v_m_1303_);
v___x_1305_ = l_Lean_StructureInfo_lt(v_a_1304_, v_k_1298_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; 
lean_dec(v_x_1300_);
v___x_1306_ = l_Lean_StructureInfo_lt(v_k_1298_, v_a_1304_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_m_1303_);
lean_dec(v_x_1299_);
lean_inc(v_a_1304_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1304_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_eq(v_m_1303_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_nat_sub(v_m_1303_, v___x_1302_);
lean_dec(v_m_1303_);
v___x_1311_ = lean_nat_dec_lt(v___x_1310_, v_x_1299_);
if (v___x_1311_ == 0)
{
v_x_1300_ = v___x_1310_;
goto _start;
}
else
{
lean_object* v___x_1313_; 
lean_dec(v___x_1310_);
lean_dec(v_x_1299_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
}
else
{
lean_object* v___x_1314_; 
lean_dec(v_m_1303_);
lean_dec(v_x_1299_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
}
}
else
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
lean_dec(v_x_1299_);
v___x_1315_ = lean_nat_add(v_m_1303_, v___x_1302_);
lean_dec(v_m_1303_);
v___x_1316_ = lean_nat_dec_le(v___x_1315_, v_x_1300_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v___x_1315_);
lean_dec(v_x_1300_);
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
v_x_1299_ = v___x_1315_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1319_, lean_object* v_k_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1319_, v_k_1320_, v_x_1321_, v_x_1322_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_as_1319_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1324_, lean_object* v_vals_1325_, lean_object* v_i_1326_, lean_object* v_k_1327_){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_array_get_size(v_keys_1324_);
v___x_1329_ = lean_nat_dec_lt(v_i_1326_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_i_1326_);
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v_k_x27_1331_; uint8_t v___x_1332_; 
v_k_x27_1331_ = lean_array_fget_borrowed(v_keys_1324_, v_i_1326_);
v___x_1332_ = lean_name_eq(v_k_1327_, v_k_x27_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_nat_add(v_i_1326_, v___x_1333_);
lean_dec(v_i_1326_);
v_i_1326_ = v___x_1334_;
goto _start;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_array_fget_borrowed(v_vals_1325_, v_i_1326_);
lean_dec(v_i_1326_);
lean_inc(v___x_1336_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_i_1340_, lean_object* v_k_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1338_, v_vals_1339_, v_i_1340_, v_k_1341_);
lean_dec(v_k_1341_);
lean_dec_ref(v_vals_1339_);
lean_dec_ref(v_keys_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1343_, size_t v_x_1344_, lean_object* v_x_1345_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_object* v_es_1346_; lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v_j_1350_; lean_object* v___x_1351_; 
v_es_1346_ = lean_ctor_get(v_x_1343_, 0);
v___x_1347_ = lean_box(2);
v___x_1348_ = ((size_t)31ULL);
v___x_1349_ = lean_usize_land(v_x_1344_, v___x_1348_);
v_j_1350_ = lean_usize_to_nat(v___x_1349_);
v___x_1351_ = lean_array_get_borrowed(v___x_1347_, v_es_1346_, v_j_1350_);
lean_dec(v_j_1350_);
switch(lean_obj_tag(v___x_1351_))
{
case 0:
{
lean_object* v_key_1352_; lean_object* v_val_1353_; uint8_t v___x_1354_; 
v_key_1352_ = lean_ctor_get(v___x_1351_, 0);
v_val_1353_ = lean_ctor_get(v___x_1351_, 1);
v___x_1354_ = lean_name_eq(v_x_1345_, v_key_1352_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_box(0);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; 
lean_inc(v_val_1353_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_val_1353_);
return v___x_1356_;
}
}
case 1:
{
lean_object* v_node_1357_; size_t v___x_1358_; size_t v___x_1359_; 
v_node_1357_ = lean_ctor_get(v___x_1351_, 0);
v___x_1358_ = ((size_t)5ULL);
v___x_1359_ = lean_usize_shift_right(v_x_1344_, v___x_1358_);
v_x_1343_ = v_node_1357_;
v_x_1344_ = v___x_1359_;
goto _start;
}
default: 
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_box(0);
return v___x_1361_;
}
}
}
else
{
lean_object* v_ks_1362_; lean_object* v_vs_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_ks_1362_ = lean_ctor_get(v_x_1343_, 0);
v_vs_1363_ = lean_ctor_get(v_x_1343_, 1);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1362_, v_vs_1363_, v___x_1364_, v_x_1345_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
size_t v_x_396__boxed_1369_; lean_object* v_res_1370_; 
v_x_396__boxed_1369_ = lean_unbox_usize(v_x_1367_);
lean_dec(v_x_1367_);
v_res_1370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1366_, v_x_396__boxed_1369_, v_x_1368_);
lean_dec(v_x_1368_);
lean_dec_ref(v_x_1366_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
uint64_t v___y_1374_; 
if (lean_obj_tag(v_x_1372_) == 0)
{
uint64_t v___x_1377_; 
v___x_1377_ = 1723ULL;
v___y_1374_ = v___x_1377_;
goto v___jp_1373_;
}
else
{
uint64_t v_hash_1378_; 
v_hash_1378_ = lean_ctor_get_uint64(v_x_1372_, sizeof(void*)*2);
v___y_1374_ = v_hash_1378_;
goto v___jp_1373_;
}
v___jp_1373_:
{
size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_uint64_to_usize(v___y_1374_);
v___x_1376_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1371_, v___x_1375_, v_x_1372_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1379_, v_x_1380_);
lean_dec(v_x_1380_);
lean_dec_ref(v_x_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1382_, lean_object* v_structName_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_obj_once(&l_Lean_registerStructure___closed__0, &l_Lean_registerStructure___closed__0_once, _init_l_Lean_registerStructure___closed__0);
v___x_1385_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1382_, v_structName_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v_toEnvExtension_1387_; lean_object* v_asyncMode_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; 
v___x_1386_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1387_ = lean_ctor_get(v___x_1386_, 0);
v_asyncMode_1388_ = lean_ctor_get(v_toEnvExtension_1387_, 2);
v___x_1389_ = lean_box(0);
v___x_1390_ = 0;
v___x_1391_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1384_, v___x_1386_, v_env_1382_, v_asyncMode_1388_, v___x_1389_, v___x_1390_);
v_snd_1392_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_snd_1392_);
lean_dec(v___x_1391_);
v___x_1393_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1392_, v_structName_1383_);
lean_dec(v_structName_1383_);
lean_dec(v_snd_1392_);
return v___x_1393_;
}
else
{
lean_object* v_val_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_val_1394_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1395_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1396_ = 0;
v___x_1397_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1384_, v___x_1395_, v_env_1382_, v_val_1394_, v___x_1396_);
lean_dec(v_val_1394_);
lean_dec_ref(v_env_1382_);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_array_get_size(v___x_1397_);
v___x_1400_ = lean_nat_dec_lt(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec_ref(v___x_1397_);
lean_dec(v_structName_1383_);
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = lean_nat_sub(v___x_1399_, v___x_1402_);
v___x_1404_ = lean_nat_dec_le(v___x_1398_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_dec(v___x_1403_);
lean_dec_ref(v___x_1397_);
lean_dec(v_structName_1383_);
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1407_, 0, v_structName_1383_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
lean_ctor_set(v___x_1407_, 2, v___x_1406_);
lean_ctor_set(v___x_1407_, 3, v___x_1406_);
v___x_1408_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1397_, v___x_1407_, v___x_1398_, v___x_1403_);
lean_dec_ref_known(v___x_1407_, 4);
lean_dec_ref(v___x_1397_);
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1410_, v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1413_, v_x_1414_, v_x_1415_);
lean_dec(v_x_1415_);
lean_dec_ref(v_x_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1417_, lean_object* v_k_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1417_, v_k_1418_, v_x_1419_, v_x_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1423_, lean_object* v_k_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1423_, v_k_1424_, v_x_1425_, v_x_1426_, v_x_1427_);
lean_dec_ref(v_k_1424_);
lean_dec_ref(v_as_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1429_, lean_object* v_x_1430_, size_t v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1430_, v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
size_t v_x_529__boxed_1438_; lean_object* v_res_1439_; 
v_x_529__boxed_1438_ = lean_unbox_usize(v_x_1436_);
lean_dec(v_x_1436_);
v_res_1439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1434_, v_x_1435_, v_x_529__boxed_1438_, v_x_1437_);
lean_dec(v_x_1437_);
lean_dec_ref(v_x_1435_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1440_, lean_object* v_keys_1441_, lean_object* v_vals_1442_, lean_object* v_heq_1443_, lean_object* v_i_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1441_, v_vals_1442_, v_i_1444_, v_k_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_heq_1450_, lean_object* v_i_1451_, lean_object* v_k_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1447_, v_keys_1448_, v_vals_1449_, v_heq_1450_, v_i_1451_, v_k_1452_);
lean_dec(v_k_1452_);
lean_dec_ref(v_vals_1449_);
lean_dec_ref(v_keys_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default));
v___x_1456_ = lean_panic_fn_borrowed(v___x_1455_, v_msg_1454_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__2(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_unsigned_to_nat(147u);
v___x_1462_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1463_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1464_ = l_mkPanicMessageWithDecl(v___x_1463_, v___x_1462_, v___x_1461_, v___x_1460_, v___x_1459_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1465_, lean_object* v_structName_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_getStructureInfo_x3f(v_env_1465_, v_structName_1466_);
if (lean_obj_tag(v___x_1467_) == 1)
{
lean_object* v_val_1468_; 
v_val_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v___x_1467_, 1);
return v_val_1468_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v___x_1467_);
v___x_1469_ = lean_obj_once(&l_Lean_getStructureInfo___closed__2, &l_Lean_getStructureInfo___closed__2_once, _init_l_Lean_getStructureInfo___closed__2);
v___x_1470_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1469_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1473_ = lean_panic_fn_borrowed(v___x_1472_, v_msg_1471_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1475_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1476_ = lean_unsigned_to_nat(9u);
v___x_1477_ = lean_unsigned_to_nat(162u);
v___x_1478_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1479_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1480_ = l_mkPanicMessageWithDecl(v___x_1479_, v___x_1478_, v___x_1477_, v___x_1476_, v___x_1475_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1483_ = lean_unsigned_to_nat(11u);
v___x_1484_ = lean_unsigned_to_nat(161u);
v___x_1485_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1486_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_1487_ = l_mkPanicMessageWithDecl(v___x_1486_, v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1488_, lean_object* v_constName_1489_){
_start:
{
uint8_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = 0;
lean_inc_ref(v_env_1488_);
v___x_1497_ = l_Lean_Environment_find_x3f(v_env_1488_, v_constName_1489_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 1)
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1497_, 1);
if (lean_obj_tag(v_val_1498_) == 5)
{
lean_object* v_val_1499_; lean_object* v_ctors_1500_; 
v_val_1499_ = lean_ctor_get(v_val_1498_, 0);
lean_inc_ref(v_val_1499_);
lean_dec_ref_known(v_val_1498_, 1);
v_ctors_1500_ = lean_ctor_get(v_val_1499_, 4);
lean_inc(v_ctors_1500_);
lean_dec_ref(v_val_1499_);
if (lean_obj_tag(v_ctors_1500_) == 1)
{
lean_object* v_tail_1501_; 
v_tail_1501_ = lean_ctor_get(v_ctors_1500_, 1);
if (lean_obj_tag(v_tail_1501_) == 0)
{
lean_object* v_head_1502_; lean_object* v___x_1503_; 
v_head_1502_ = lean_ctor_get(v_ctors_1500_, 0);
lean_inc(v_head_1502_);
lean_dec_ref_known(v_ctors_1500_, 2);
v___x_1503_ = l_Lean_Environment_find_x3f(v_env_1488_, v_head_1502_, v___x_1496_);
if (lean_obj_tag(v___x_1503_) == 1)
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1503_, 1);
if (lean_obj_tag(v_val_1504_) == 6)
{
lean_object* v_val_1505_; 
v_val_1505_ = lean_ctor_get(v_val_1504_, 0);
lean_inc_ref(v_val_1505_);
lean_dec_ref_known(v_val_1504_, 1);
return v_val_1505_;
}
else
{
lean_dec(v_val_1504_);
goto v___jp_1493_;
}
}
else
{
lean_dec(v___x_1503_);
goto v___jp_1493_;
}
}
else
{
lean_dec_ref_known(v_ctors_1500_, 2);
lean_dec_ref(v_env_1488_);
goto v___jp_1490_;
}
}
else
{
lean_dec(v_ctors_1500_);
lean_dec_ref(v_env_1488_);
goto v___jp_1490_;
}
}
else
{
lean_dec(v_val_1498_);
lean_dec_ref(v_env_1488_);
goto v___jp_1490_;
}
}
else
{
lean_dec(v___x_1497_);
lean_dec_ref(v_env_1488_);
goto v___jp_1490_;
}
v___jp_1490_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1492_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1491_);
return v___x_1492_;
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1495_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1494_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1506_, lean_object* v_structName_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v_fieldNames_1509_; 
v___x_1508_ = l_Lean_getStructureInfo(v_env_1506_, v_structName_1507_);
v_fieldNames_1509_ = lean_ctor_get(v___x_1508_, 1);
lean_inc_ref(v_fieldNames_1509_);
lean_dec_ref(v___x_1508_);
return v_fieldNames_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1510_, lean_object* v_structName_1511_, lean_object* v_fieldName_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_getStructureInfo_x3f(v_env_1510_, v_structName_1511_);
if (lean_obj_tag(v___x_1513_) == 1)
{
lean_object* v_val_1514_; lean_object* v_fieldInfo_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_val_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v_fieldInfo_1515_ = lean_ctor_get(v_val_1514_, 2);
lean_inc_ref(v_fieldInfo_1515_);
lean_dec(v_val_1514_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_fieldInfo_1515_);
v___x_1518_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref(v_fieldInfo_1515_);
lean_dec(v_fieldName_1512_);
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_sub(v___x_1517_, v___x_1520_);
v___x_1522_ = lean_nat_dec_le(v___x_1516_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec(v___x_1521_);
lean_dec_ref(v_fieldInfo_1515_);
lean_dec(v_fieldName_1512_);
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_box(0);
v___x_1526_ = 0;
v___x_1527_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1527_, 0, v_fieldName_1512_);
lean_ctor_set(v___x_1527_, 1, v___x_1524_);
lean_ctor_set(v___x_1527_, 2, v___x_1525_);
lean_ctor_set(v___x_1527_, 3, v___x_1525_);
lean_ctor_set_uint8(v___x_1527_, sizeof(void*)*4, v___x_1526_);
v___x_1528_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1515_, v___x_1527_, v___x_1516_, v___x_1521_);
lean_dec_ref_known(v___x_1527_, 4);
lean_dec_ref(v_fieldInfo_1515_);
return v___x_1528_;
}
}
}
else
{
lean_object* v___x_1529_; 
lean_dec(v___x_1513_);
lean_dec(v_fieldName_1512_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1530_, lean_object* v_structName_1531_, lean_object* v_fieldName_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_getFieldInfo_x3f(v_env_1530_, v_structName_1531_, v_fieldName_1532_);
if (lean_obj_tag(v___x_1533_) == 1)
{
lean_object* v_val_1534_; lean_object* v_subobject_x3f_1535_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v_subobject_x3f_1535_ = lean_ctor_get(v_val_1534_, 2);
lean_inc(v_subobject_x3f_1535_);
lean_dec(v_val_1534_);
return v_subobject_x3f_1535_;
}
else
{
lean_object* v___x_1536_; 
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1537_, lean_object* v_structName_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v_parentInfo_1540_; 
v___x_1539_ = l_Lean_getStructureInfo(v_env_1537_, v_structName_1538_);
v_parentInfo_1540_ = lean_ctor_get(v___x_1539_, 3);
lean_inc_ref(v_parentInfo_1540_);
lean_dec_ref(v___x_1539_);
return v_parentInfo_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1541_, lean_object* v_structName_1542_, lean_object* v_as_1543_, size_t v_i_1544_, size_t v_stop_1545_, lean_object* v_b_1546_){
_start:
{
lean_object* v___y_1548_; uint8_t v___x_1552_; 
v___x_1552_ = lean_usize_dec_eq(v_i_1544_, v_stop_1545_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_array_uget_borrowed(v_as_1543_, v_i_1544_);
lean_inc(v___x_1553_);
lean_inc(v_structName_1542_);
lean_inc_ref(v_env_1541_);
v___x_1554_ = l_Lean_isSubobjectField_x3f(v_env_1541_, v_structName_1542_, v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
v___y_1548_ = v_b_1546_;
goto v___jp_1547_;
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1556_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_array_push(v_b_1546_, v_val_1555_);
v___y_1548_ = v___x_1556_;
goto v___jp_1547_;
}
}
else
{
lean_dec(v_structName_1542_);
lean_dec_ref(v_env_1541_);
return v_b_1546_;
}
v___jp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1544_, v___x_1549_);
v_i_1544_ = v___x_1550_;
v_b_1546_ = v___y_1548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1557_, lean_object* v_structName_1558_, lean_object* v_as_1559_, lean_object* v_i_1560_, lean_object* v_stop_1561_, lean_object* v_b_1562_){
_start:
{
size_t v_i_boxed_1563_; size_t v_stop_boxed_1564_; lean_object* v_res_1565_; 
v_i_boxed_1563_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_stop_boxed_1564_ = lean_unbox_usize(v_stop_1561_);
lean_dec(v_stop_1561_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1557_, v_structName_1558_, v_as_1559_, v_i_boxed_1563_, v_stop_boxed_1564_, v_b_1562_);
lean_dec_ref(v_as_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1566_, lean_object* v_structName_1567_, lean_object* v_as_1568_, lean_object* v_start_1569_, lean_object* v_stop_1570_){
_start:
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1572_ = lean_nat_dec_lt(v_start_1569_, v_stop_1570_);
if (v___x_1572_ == 0)
{
lean_dec(v_structName_1567_);
lean_dec_ref(v_env_1566_);
return v___x_1571_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_get_size(v_as_1568_);
v___x_1574_ = lean_nat_dec_le(v_stop_1570_, v___x_1573_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_nat_dec_lt(v_start_1569_, v___x_1573_);
if (v___x_1575_ == 0)
{
lean_dec(v_structName_1567_);
lean_dec_ref(v_env_1566_);
return v___x_1571_;
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_usize_of_nat(v_start_1569_);
v___x_1577_ = lean_usize_of_nat(v___x_1573_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1566_, v_structName_1567_, v_as_1568_, v___x_1576_, v___x_1577_, v___x_1571_);
return v___x_1578_;
}
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_usize_of_nat(v_start_1569_);
v___x_1580_ = lean_usize_of_nat(v_stop_1570_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1566_, v_structName_1567_, v_as_1568_, v___x_1579_, v___x_1580_, v___x_1571_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1582_, lean_object* v_structName_1583_, lean_object* v_as_1584_, lean_object* v_start_1585_, lean_object* v_stop_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1582_, v_structName_1583_, v_as_1584_, v_start_1585_, v_stop_1586_);
lean_dec(v_stop_1586_);
lean_dec(v_start_1585_);
lean_dec_ref(v_as_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1588_, lean_object* v_structName_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_inc(v_structName_1589_);
lean_inc_ref(v_env_1588_);
v___x_1590_ = l_Lean_getStructureFields(v_env_1588_, v_structName_1589_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_array_get_size(v___x_1590_);
v___x_1593_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1588_, v_structName_1589_, v___x_1590_, v___x_1591_, v___x_1592_);
lean_dec_ref(v___x_1590_);
return v___x_1593_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1594_, lean_object* v_as_1595_, size_t v_i_1596_, size_t v_stop_1597_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_eq(v_i_1596_, v_stop_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = lean_array_uget_borrowed(v_as_1595_, v_i_1596_);
v___x_1600_ = lean_name_eq(v_a_1594_, v___x_1599_);
if (v___x_1600_ == 0)
{
size_t v___x_1601_; size_t v___x_1602_; 
v___x_1601_ = ((size_t)1ULL);
v___x_1602_ = lean_usize_add(v_i_1596_, v___x_1601_);
v_i_1596_ = v___x_1602_;
goto _start;
}
else
{
return v___x_1600_;
}
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = 0;
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1605_, lean_object* v_as_1606_, lean_object* v_i_1607_, lean_object* v_stop_1608_){
_start:
{
size_t v_i_boxed_1609_; size_t v_stop_boxed_1610_; uint8_t v_res_1611_; lean_object* v_r_1612_; 
v_i_boxed_1609_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_stop_boxed_1610_ = lean_unbox_usize(v_stop_1608_);
lean_dec(v_stop_1608_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1605_, v_as_1606_, v_i_boxed_1609_, v_stop_boxed_1610_);
lean_dec_ref(v_as_1606_);
lean_dec(v_a_1605_);
v_r_1612_ = lean_box(v_res_1611_);
return v_r_1612_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_array_get_size(v_as_1613_);
v___x_1617_ = lean_nat_dec_lt(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
return v___x_1617_;
}
else
{
size_t v___x_1618_; size_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = lean_usize_of_nat(v___x_1616_);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1614_, v_as_1613_, v___x_1618_, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_res_1623_; lean_object* v_r_1624_; 
v_res_1623_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1621_, v_a_1622_);
lean_dec(v_a_1622_);
lean_dec_ref(v_as_1621_);
v_r_1624_ = lean_box(v_res_1623_);
return v_r_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1628_, lean_object* v_structName_1629_, lean_object* v_fieldName_1630_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
lean_inc(v_structName_1629_);
lean_inc_ref(v_env_1628_);
v___x_1631_ = l_Lean_getStructureFields(v_env_1628_, v_structName_1629_);
v___x_1632_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1631_, v_fieldName_1630_);
lean_dec_ref(v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; size_t v_sz_1636_; size_t v___x_1637_; lean_object* v___x_1638_; lean_object* v_fst_1639_; 
lean_inc_ref(v_env_1628_);
v___x_1633_ = l_Lean_getStructureSubobjects(v_env_1628_, v_structName_1629_);
v___x_1634_ = lean_box(0);
v___x_1635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1636_ = lean_array_size(v___x_1633_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1628_, v_fieldName_1630_, v___x_1633_, v_sz_1636_, v___x_1637_, v___x_1635_);
lean_dec_ref(v___x_1633_);
v_fst_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_fst_1639_);
lean_dec_ref(v___x_1638_);
if (lean_obj_tag(v_fst_1639_) == 0)
{
return v___x_1634_;
}
else
{
lean_object* v_val_1640_; 
v_val_1640_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_fst_1639_, 1);
return v_val_1640_;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec_ref(v_env_1628_);
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_structName_1629_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1642_, lean_object* v_fieldName_1643_, lean_object* v_as_1644_, size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_b_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_lt(v_i_1646_, v_sz_1645_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v_env_1642_);
lean_inc_ref(v_b_1647_);
return v_b_1647_;
}
else
{
lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
v_a_1650_ = lean_array_uget_borrowed(v_as_1644_, v_i_1646_);
lean_inc(v_a_1650_);
lean_inc_ref(v_env_1642_);
v___x_1651_ = l_Lean_findField_x3f(v_env_1642_, v_a_1650_, v_fieldName_1643_);
if (lean_obj_tag(v___x_1651_) == 1)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_env_1642_);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1649_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; 
lean_dec(v___x_1651_);
v___x_1654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1655_ = ((size_t)1ULL);
v___x_1656_ = lean_usize_add(v_i_1646_, v___x_1655_);
v_i_1646_ = v___x_1656_;
v_b_1647_ = v___x_1654_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1658_, lean_object* v_fieldName_1659_, lean_object* v_as_1660_, lean_object* v_sz_1661_, lean_object* v_i_1662_, lean_object* v_b_1663_){
_start:
{
size_t v_sz_boxed_1664_; size_t v_i_boxed_1665_; lean_object* v_res_1666_; 
v_sz_boxed_1664_ = lean_unbox_usize(v_sz_1661_);
lean_dec(v_sz_1661_);
v_i_boxed_1665_ = lean_unbox_usize(v_i_1662_);
lean_dec(v_i_1662_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1658_, v_fieldName_1659_, v_as_1660_, v_sz_boxed_1664_, v_i_boxed_1665_, v_b_1663_);
lean_dec_ref(v_b_1663_);
lean_dec_ref(v_as_1660_);
lean_dec(v_fieldName_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1667_, lean_object* v_structName_1668_, lean_object* v_fieldName_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_findField_x3f(v_env_1667_, v_structName_1668_, v_fieldName_1669_);
lean_dec(v_fieldName_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1674_, lean_object* v_as_1675_, size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_b_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1679_ == 0)
{
lean_inc_ref(v_b_1678_);
return v_b_1678_;
}
else
{
lean_object* v_a_1680_; lean_object* v_projFn_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_a_1680_ = lean_array_uget_borrowed(v_as_1675_, v_i_1677_);
v_projFn_1681_ = lean_ctor_get(v_a_1680_, 1);
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Lean_Name_isSuffixOf(v_projName_1674_, v_projFn_1681_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; 
v___x_1684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1677_, v___x_1685_);
v_i_1677_ = v___x_1686_;
v_b_1678_ = v___x_1684_;
goto _start;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_inc(v_a_1680_);
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1680_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1682_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1691_, lean_object* v_as_1692_, lean_object* v_sz_1693_, lean_object* v_i_1694_, lean_object* v_b_1695_){
_start:
{
size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1693_);
lean_dec(v_sz_1693_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1691_, v_as_1692_, v_sz_boxed_1696_, v_i_boxed_1697_, v_b_1695_);
lean_dec_ref(v_b_1695_);
lean_dec_ref(v_as_1692_);
lean_dec(v_projName_1691_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1699_, lean_object* v_projName_1700_, lean_object* v_structName_1701_, lean_object* v_a_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = l_Lean_NameSet_contains(v_a_1702_, v_structName_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_fst_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1749_; 
lean_inc(v_structName_1701_);
lean_inc_ref(v_env_1699_);
v___x_1704_ = l_Lean_getStructureParentInfo(v_env_1699_, v_structName_1701_);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1729_ = lean_array_size(v___x_1704_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1700_, v___x_1704_, v_sz_1729_, v___x_1730_, v___x_1728_);
v_fst_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1731_, 1);
lean_dec(v_unused_1750_);
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1749_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_fst_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1749_;
goto v_resetjp_1733_;
}
v___jp_1705_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; size_t v_sz_1709_; size_t v___x_1710_; lean_object* v___x_1711_; lean_object* v_fst_1712_; lean_object* v_fst_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1726_; 
v___x_1706_ = l_Lean_NameSet_insert(v_a_1702_, v_structName_1701_);
v___x_1707_ = lean_box(0);
v___x_1708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1709_ = lean_array_size(v___x_1704_);
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1699_, v_projName_1700_, v___x_1704_, v_sz_1709_, v___x_1710_, v___x_1708_, v___x_1706_);
lean_dec_ref(v___x_1704_);
v_fst_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_fst_1712_);
v_fst_1713_ = lean_ctor_get(v_fst_1712_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_fst_1712_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_fst_1712_, 1);
lean_dec(v_unused_1727_);
v___x_1715_ = v_fst_1712_;
v_isShared_1716_ = v_isSharedCheck_1726_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_fst_1713_);
lean_dec(v_fst_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1726_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
if (lean_obj_tag(v_fst_1713_) == 0)
{
lean_object* v_snd_1717_; lean_object* v___x_1719_; 
v_snd_1717_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1711_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_snd_1717_);
lean_ctor_set(v___x_1715_, 0, v___x_1707_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_snd_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v_snd_1721_; lean_object* v_val_1722_; lean_object* v___x_1724_; 
v_snd_1721_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_snd_1721_);
lean_dec_ref(v___x_1711_);
v_val_1722_ = lean_ctor_get(v_fst_1713_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v_fst_1713_, 1);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_snd_1721_);
lean_ctor_set(v___x_1715_, 0, v_val_1722_);
v___x_1724_ = v___x_1715_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_val_1722_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_snd_1721_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
v_resetjp_1733_:
{
if (lean_obj_tag(v_fst_1732_) == 0)
{
lean_del_object(v___x_1734_);
goto v___jp_1705_;
}
else
{
lean_object* v_val_1736_; 
v_val_1736_ = lean_ctor_get(v_fst_1732_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v_fst_1732_, 1);
if (lean_obj_tag(v_val_1736_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v___x_1704_);
lean_dec(v_structName_1701_);
lean_dec_ref(v_env_1699_);
v_val_1737_ = lean_ctor_get(v_val_1736_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_val_1736_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1739_ = v_val_1736_;
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v_val_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_structName_1741_; lean_object* v___x_1743_; 
v_structName_1741_ = lean_ctor_get(v_val_1737_, 0);
lean_inc(v_structName_1741_);
lean_dec(v_val_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_structName_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_structName_1741_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_a_1702_);
lean_ctor_set(v___x_1734_, 0, v___x_1743_);
v___x_1745_ = v___x_1734_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_a_1702_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_dec(v_val_1736_);
lean_del_object(v___x_1734_);
goto v___jp_1705_;
}
}
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_structName_1701_);
lean_dec_ref(v_env_1699_);
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v_a_1702_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1753_, lean_object* v_projName_1754_, lean_object* v_as_1755_, size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_lt(v_i_1757_, v_sz_1756_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec_ref(v_env_1753_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1758_);
lean_ctor_set(v___x_1761_, 1, v___y_1759_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v_structName_1763_; lean_object* v___x_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_b_1758_);
v_a_1762_ = lean_array_uget_borrowed(v_as_1755_, v_i_1757_);
v_structName_1763_ = lean_ctor_get(v_a_1762_, 0);
lean_inc(v_structName_1763_);
lean_inc_ref(v_env_1753_);
v___x_1764_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1753_, v_projName_1754_, v_structName_1763_, v___y_1759_);
v_fst_1765_ = lean_ctor_get(v___x_1764_, 0);
v_snd_1766_ = lean_ctor_get(v___x_1764_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1768_ = v___x_1764_;
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_inc(v_fst_1765_);
lean_dec(v___x_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
if (lean_obj_tag(v_fst_1765_) == 1)
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec_ref(v_env_1753_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_fst_1765_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1770_);
lean_ctor_set(v___x_1768_, 0, v___x_1771_);
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1770_);
v___x_1773_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_snd_1766_);
return v___x_1774_;
}
}
else
{
lean_object* v___x_1776_; size_t v___x_1777_; size_t v___x_1778_; 
lean_del_object(v___x_1768_);
lean_dec(v_fst_1765_);
v___x_1776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1777_ = ((size_t)1ULL);
v___x_1778_ = lean_usize_add(v_i_1757_, v___x_1777_);
v_i_1757_ = v___x_1778_;
v_b_1758_ = v___x_1776_;
v___y_1759_ = v_snd_1766_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1781_, lean_object* v_projName_1782_, lean_object* v_as_1783_, lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1781_, v_projName_1782_, v_as_1783_, v_sz_boxed_1788_, v_i_boxed_1789_, v_b_1786_, v___y_1787_);
lean_dec_ref(v_as_1783_);
lean_dec(v_projName_1782_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1791_, lean_object* v_projName_1792_, lean_object* v_structName_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1791_, v_projName_1792_, v_structName_1793_, v_a_1794_);
lean_dec(v_projName_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1796_, lean_object* v_structName_1797_, lean_object* v_projName_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_fst_1801_; 
v___x_1799_ = l_Lean_NameSet_empty;
v___x_1800_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1796_, v_projName_1798_, v_structName_1797_, v___x_1799_);
v_fst_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_fst_1801_);
lean_dec_ref(v___x_1800_);
return v_fst_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1802_, lean_object* v_structName_1803_, lean_object* v_projName_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_findParentProjStruct_x3f(v_env_1802_, v_structName_1803_, v_projName_1804_);
lean_dec(v_projName_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1811_ = l_Lean_Name_append(v_structCtorName_1809_, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1812_, lean_object* v_structName_1813_, uint8_t v_includeSubobjectFields_1814_, lean_object* v_as_1815_, size_t v_i_1816_, size_t v_stop_1817_, lean_object* v_b_1818_){
_start:
{
lean_object* v___y_1820_; uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1816_, v_stop_1817_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_array_uget_borrowed(v_as_1815_, v_i_1816_);
lean_inc(v___x_1825_);
lean_inc(v_structName_1813_);
lean_inc_ref(v_env_1812_);
v___x_1826_ = l_Lean_isSubobjectField_x3f(v_env_1812_, v_structName_1813_, v___x_1825_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v___x_1827_; 
lean_inc(v___x_1825_);
v___x_1827_ = lean_array_push(v_b_1818_, v___x_1825_);
v___y_1820_ = v___x_1827_;
goto v___jp_1819_;
}
else
{
if (v_includeSubobjectFields_1814_ == 0)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; 
v_val_1828_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v___x_1826_, 1);
lean_inc_ref(v_env_1812_);
v___x_1829_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1812_, v_val_1828_, v_b_1818_, v_includeSubobjectFields_1814_);
v___y_1820_ = v___x_1829_;
goto v___jp_1819_;
}
else
{
lean_object* v_val_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_val_1830_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1826_, 1);
lean_inc(v___x_1825_);
v___x_1831_ = lean_array_push(v_b_1818_, v___x_1825_);
lean_inc_ref(v_env_1812_);
v___x_1832_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1812_, v_val_1830_, v___x_1831_, v_includeSubobjectFields_1814_);
v___y_1820_ = v___x_1832_;
goto v___jp_1819_;
}
}
}
else
{
lean_dec(v_structName_1813_);
lean_dec_ref(v_env_1812_);
return v_b_1818_;
}
v___jp_1819_:
{
size_t v___x_1821_; size_t v___x_1822_; 
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1816_, v___x_1821_);
v_i_1816_ = v___x_1822_;
v_b_1818_ = v___y_1820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1833_, lean_object* v_structName_1834_, lean_object* v_fullNames_1835_, uint8_t v_includeSubobjectFields_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_inc(v_structName_1834_);
lean_inc_ref(v_env_1833_);
v___x_1837_ = l_Lean_getStructureFields(v_env_1833_, v_structName_1834_);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_array_get_size(v___x_1837_);
v___x_1840_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_dec_ref(v___x_1837_);
lean_dec(v_structName_1834_);
lean_dec_ref(v_env_1833_);
return v_fullNames_1835_;
}
else
{
size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = lean_usize_of_nat(v___x_1839_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1833_, v_structName_1834_, v_includeSubobjectFields_1836_, v___x_1837_, v___x_1841_, v___x_1842_, v_fullNames_1835_);
lean_dec_ref(v___x_1837_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1844_, lean_object* v_structName_1845_, lean_object* v_fullNames_1846_, lean_object* v_includeSubobjectFields_1847_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1848_; lean_object* v_res_1849_; 
v_includeSubobjectFields_boxed_1848_ = lean_unbox(v_includeSubobjectFields_1847_);
v_res_1849_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1844_, v_structName_1845_, v_fullNames_1846_, v_includeSubobjectFields_boxed_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1850_, lean_object* v_structName_1851_, lean_object* v_includeSubobjectFields_1852_, lean_object* v_as_1853_, lean_object* v_i_1854_, lean_object* v_stop_1855_, lean_object* v_b_1856_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1857_; size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_includeSubobjectFields_boxed_1857_ = lean_unbox(v_includeSubobjectFields_1852_);
v_i_boxed_1858_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1855_);
lean_dec(v_stop_1855_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1850_, v_structName_1851_, v_includeSubobjectFields_boxed_1857_, v_as_1853_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1856_);
lean_dec_ref(v_as_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1861_, lean_object* v_structName_1862_, uint8_t v_includeSubobjectFields_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1865_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1861_, v_structName_1862_, v___x_1864_, v_includeSubobjectFields_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1866_, lean_object* v_structName_1867_, lean_object* v_includeSubobjectFields_1868_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1869_; lean_object* v_res_1870_; 
v_includeSubobjectFields_boxed_1869_ = lean_unbox(v_includeSubobjectFields_1868_);
v_res_1870_ = l_Lean_getStructureFieldsFlattened(v_env_1866_, v_structName_1867_, v_includeSubobjectFields_boxed_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1871_, lean_object* v_constName_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_getStructureInfo_x3f(v_env_1871_, v_constName_1872_);
if (lean_obj_tag(v___x_1873_) == 0)
{
uint8_t v___x_1874_; 
v___x_1874_ = 0;
return v___x_1874_;
}
else
{
uint8_t v___x_1875_; 
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = 1;
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1876_, lean_object* v_constName_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l_Lean_isStructure(v_env_1876_, v_constName_1877_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1880_, lean_object* v_structName_1881_, lean_object* v_fieldName_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_getFieldInfo_x3f(v_env_1880_, v_structName_1881_, v_fieldName_1882_);
if (lean_obj_tag(v___x_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1892_; 
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_projFn_1888_; lean_object* v___x_1890_; 
v_projFn_1888_ = lean_ctor_get(v_val_1884_, 1);
lean_inc(v_projFn_1888_);
lean_dec(v_val_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v_projFn_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_projFn_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1893_; 
lean_dec(v___x_1883_);
v___x_1893_ = lean_box(0);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1894_, lean_object* v_structName_1895_, lean_object* v_fieldName_1896_){
_start:
{
lean_object* v___x_1897_; 
lean_inc_ref(v_env_1894_);
v___x_1897_ = l_Lean_getProjFnForField_x3f(v_env_1894_, v_structName_1895_, v_fieldName_1896_);
if (lean_obj_tag(v___x_1897_) == 1)
{
lean_object* v_val_1898_; lean_object* v___x_1899_; 
v_val_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_n(v_val_1898_, 2);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1894_, v_val_1898_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_dec(v_val_1898_);
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
else
{
lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_val_1901_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1899_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_dec(v___x_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_val_1898_);
lean_ctor_set(v___x_1905_, 1, v_val_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v___x_1910_; 
lean_dec(v___x_1897_);
lean_dec_ref(v_env_1894_);
v___x_1910_ = lean_box(0);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1916_ = l_Lean_Name_append(v_projFn_1914_, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1922_ = l_Lean_Name_append(v_projFn_1920_, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1923_, lean_object* v_env_1924_, lean_object* v_structName_1925_, lean_object* v_fieldName_1926_){
_start:
{
lean_object* v___x_1927_; 
lean_inc(v_fieldName_1926_);
lean_inc(v_structName_1925_);
lean_inc_ref(v_env_1924_);
v___x_1927_ = l_Lean_getProjFnForField_x3f(v_env_1924_, v_structName_1925_, v_fieldName_1926_);
if (lean_obj_tag(v___x_1927_) == 1)
{
lean_object* v_val_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_fieldName_1926_);
lean_dec(v_structName_1925_);
v_val_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_val_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_defFn_1932_; uint8_t v___x_1933_; uint8_t v___x_1934_; 
v_defFn_1932_ = lean_apply_1(v_mkName_1923_, v_val_1928_);
v___x_1933_ = 1;
lean_inc(v_defFn_1932_);
v___x_1934_ = l_Lean_Environment_contains(v_env_1924_, v_defFn_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec(v_defFn_1932_);
lean_del_object(v___x_1930_);
v___x_1935_ = lean_box(0);
return v___x_1935_;
}
else
{
lean_object* v___x_1937_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_defFn_1932_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_defFn_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v___x_1940_; lean_object* v_defFn_1941_; uint8_t v___x_1942_; uint8_t v___x_1943_; 
lean_dec(v___x_1927_);
v___x_1940_ = l_Lean_Name_append(v_structName_1925_, v_fieldName_1926_);
v_defFn_1941_ = lean_apply_1(v_mkName_1923_, v___x_1940_);
v___x_1942_ = 1;
lean_inc(v_defFn_1941_);
v___x_1943_ = l_Lean_Environment_contains(v_env_1924_, v_defFn_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v_defFn_1941_);
v___x_1944_ = lean_box(0);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_defFn_1941_);
return v___x_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1947_, lean_object* v_structName_1948_, lean_object* v_fieldName_1949_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1951_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1950_, v_env_1947_, v_structName_1948_, v_fieldName_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1953_, lean_object* v_structName_1954_, lean_object* v_fieldName_1955_){
_start:
{
lean_object* v___x_1956_; 
lean_inc(v_fieldName_1955_);
lean_inc(v_structName_1954_);
lean_inc_ref(v_env_1953_);
v___x_1956_ = l_Lean_getDefaultFnForField_x3f(v_env_1953_, v_structName_1954_, v_fieldName_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1958_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1957_, v_env_1953_, v_structName_1954_, v_fieldName_1955_);
return v___x_1958_;
}
else
{
lean_dec(v_fieldName_1955_);
lean_dec(v_structName_1954_);
lean_dec_ref(v_env_1953_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1964_ = l_Lean_Name_append(v_projFn_1962_, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1966_, lean_object* v_structName_1967_, lean_object* v_fieldName_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1970_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1969_, v_env_1966_, v_structName_1967_, v_fieldName_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_path_1971_, lean_object* v_env_1972_, lean_object* v_baseStructName_1973_, lean_object* v_as_1974_, lean_object* v_i_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_snd_1978_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = lean_array_get_size(v_as_1974_);
v___x_1983_ = lean_nat_dec_lt(v_i_1975_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec(v_i_1975_);
lean_dec_ref(v_env_1972_);
lean_dec(v_path_1971_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v___y_1976_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v_subobject_x3f_1987_; 
v___x_1986_ = lean_array_fget_borrowed(v_as_1974_, v_i_1975_);
v_subobject_x3f_1987_ = lean_ctor_get(v___x_1986_, 2);
if (lean_obj_tag(v_subobject_x3f_1987_) == 1)
{
lean_object* v_projFn_1988_; lean_object* v_val_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_fst_1992_; 
v_projFn_1988_ = lean_ctor_get(v___x_1986_, 1);
v_val_1989_ = lean_ctor_get(v_subobject_x3f_1987_, 0);
lean_inc(v_path_1971_);
lean_inc(v_projFn_1988_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_projFn_1988_);
lean_ctor_set(v___x_1990_, 1, v_path_1971_);
lean_inc(v_val_1989_);
lean_inc_ref(v_env_1972_);
v___x_1991_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1972_, v_baseStructName_1973_, v_val_1989_, v___x_1990_, v___y_1976_);
v_fst_1992_ = lean_ctor_get(v___x_1991_, 0);
if (lean_obj_tag(v_fst_1992_) == 0)
{
lean_object* v_snd_1993_; 
v_snd_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_snd_1993_);
lean_dec_ref(v___x_1991_);
v_snd_1978_ = v_snd_1993_;
goto v___jp_1977_;
}
else
{
lean_dec(v_i_1975_);
lean_dec_ref(v_env_1972_);
lean_dec(v_path_1971_);
return v___x_1991_;
}
}
else
{
v_snd_1978_ = v___y_1976_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_i_1975_, v___x_1979_);
lean_dec(v_i_1975_);
v_i_1975_ = v___x_1980_;
v___y_1976_ = v_snd_1978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1994_, lean_object* v_baseStructName_1995_, lean_object* v_structName_1996_, lean_object* v_path_1997_, lean_object* v_a_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_name_eq(v_baseStructName_1995_, v_structName_1996_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Lean_NameSet_contains(v_a_1998_, v_structName_1996_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc(v_structName_1996_);
v___x_2001_ = l_Lean_NameSet_insert(v_a_1998_, v_structName_1996_);
lean_inc_ref(v_env_1994_);
v___x_2002_ = l_Lean_getStructureInfo_x3f(v_env_1994_, v_structName_1996_);
if (lean_obj_tag(v___x_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v_fieldInfo_2004_; lean_object* v_parentInfo_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_fst_2008_; 
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v_fieldInfo_2004_ = lean_ctor_get(v_val_2003_, 2);
lean_inc_ref(v_fieldInfo_2004_);
v_parentInfo_2005_ = lean_ctor_get(v_val_2003_, 3);
lean_inc_ref(v_parentInfo_2005_);
lean_dec(v_val_2003_);
v___x_2006_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_env_1994_);
lean_inc(v_path_1997_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_1997_, v_env_1994_, v_baseStructName_1995_, v_fieldInfo_2004_, v___x_2006_, v___x_2001_);
lean_dec_ref(v_fieldInfo_2004_);
v_fst_2008_ = lean_ctor_get(v___x_2007_, 0);
if (lean_obj_tag(v_fst_2008_) == 0)
{
lean_object* v_snd_2009_; lean_object* v___x_2010_; 
v_snd_2009_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_snd_2009_);
lean_dec_ref(v___x_2007_);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_1997_, v_env_1994_, v_baseStructName_1995_, v_parentInfo_2005_, v___x_2006_, v_snd_2009_);
lean_dec_ref(v_parentInfo_2005_);
return v___x_2010_;
}
else
{
lean_dec_ref(v_parentInfo_2005_);
lean_dec(v_path_1997_);
lean_dec_ref(v_env_1994_);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v___x_2002_);
lean_dec(v_path_1997_);
lean_dec_ref(v_env_1994_);
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v___x_2001_);
return v___x_2012_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_path_1997_);
lean_dec(v_structName_1996_);
lean_dec_ref(v_env_1994_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_a_1998_);
return v___x_2014_;
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v_structName_1996_);
lean_dec_ref(v_env_1994_);
v___x_2015_ = l_List_reverse___redArg(v_path_1997_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_a_1998_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(lean_object* v_path_2018_, lean_object* v_env_2019_, lean_object* v_baseStructName_2020_, lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = lean_array_get_size(v_as_2021_);
v___x_2025_ = lean_nat_dec_lt(v_i_2022_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v_i_2022_);
lean_dec_ref(v_env_2019_);
lean_dec(v_path_2018_);
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___y_2023_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v_structName_2029_; lean_object* v_projFn_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v_fst_2033_; 
v___x_2028_ = lean_array_fget_borrowed(v_as_2021_, v_i_2022_);
v_structName_2029_ = lean_ctor_get(v___x_2028_, 0);
v_projFn_2030_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_path_2018_);
lean_inc(v_projFn_2030_);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_projFn_2030_);
lean_ctor_set(v___x_2031_, 1, v_path_2018_);
lean_inc(v_structName_2029_);
lean_inc_ref(v_env_2019_);
v___x_2032_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2019_, v_baseStructName_2020_, v_structName_2029_, v___x_2031_, v___y_2023_);
v_fst_2033_ = lean_ctor_get(v___x_2032_, 0);
if (lean_obj_tag(v_fst_2033_) == 0)
{
lean_object* v_snd_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_snd_2034_ = lean_ctor_get(v___x_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___x_2032_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_add(v_i_2022_, v___x_2035_);
lean_dec(v_i_2022_);
v_i_2022_ = v___x_2036_;
v___y_2023_ = v_snd_2034_;
goto _start;
}
else
{
lean_dec(v_i_2022_);
lean_dec_ref(v_env_2019_);
lean_dec(v_path_2018_);
return v___x_2032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1___boxed(lean_object* v_path_2038_, lean_object* v_env_2039_, lean_object* v_baseStructName_2040_, lean_object* v_as_2041_, lean_object* v_i_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__1(v_path_2038_, v_env_2039_, v_baseStructName_2040_, v_as_2041_, v_i_2042_, v___y_2043_);
lean_dec_ref(v_as_2041_);
lean_dec(v_baseStructName_2040_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_path_2045_, lean_object* v_env_2046_, lean_object* v_baseStructName_2047_, lean_object* v_as_2048_, lean_object* v_i_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_path_2045_, v_env_2046_, v_baseStructName_2047_, v_as_2048_, v_i_2049_, v___y_2050_);
lean_dec_ref(v_as_2048_);
lean_dec(v_baseStructName_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___boxed(lean_object* v_env_2052_, lean_object* v_baseStructName_2053_, lean_object* v_structName_2054_, lean_object* v_path_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2052_, v_baseStructName_2053_, v_structName_2054_, v_path_2055_, v_a_2056_);
lean_dec(v_baseStructName_2053_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_2058_, lean_object* v_baseStructName_2059_, lean_object* v_structName_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_fst_2064_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Lean_NameSet_empty;
v___x_2063_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_2058_, v_baseStructName_2059_, v_structName_2060_, v___x_2061_, v___x_2062_);
v_fst_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_fst_2064_);
lean_dec_ref(v___x_2063_);
return v_fst_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* v_env_2065_, lean_object* v_baseStructName_2066_, lean_object* v_structName_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_getPathToBaseStructure_x3f(v_env_2065_, v_baseStructName_2066_, v_structName_2067_);
lean_dec(v_baseStructName_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_2069_, lean_object* v_constName_2070_){
_start:
{
uint8_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = 0;
v___x_2072_ = l_Lean_Environment_find_x3f(v_env_2069_, v_constName_2070_, v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 1)
{
lean_object* v_val_2073_; 
v_val_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2072_, 1);
if (lean_obj_tag(v_val_2073_) == 5)
{
lean_object* v_val_2074_; lean_object* v_numIndices_2075_; lean_object* v_ctors_2076_; uint8_t v_isRec_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_val_2074_ = lean_ctor_get(v_val_2073_, 0);
lean_inc_ref(v_val_2074_);
lean_dec_ref_known(v_val_2073_, 1);
v_numIndices_2075_ = lean_ctor_get(v_val_2074_, 2);
lean_inc(v_numIndices_2075_);
v_ctors_2076_ = lean_ctor_get(v_val_2074_, 4);
lean_inc(v_ctors_2076_);
v_isRec_2077_ = lean_ctor_get_uint8(v_val_2074_, sizeof(void*)*6);
lean_dec_ref(v_val_2074_);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_nat_dec_eq(v_numIndices_2075_, v___x_2078_);
lean_dec(v_numIndices_2075_);
if (v___x_2079_ == 0)
{
lean_dec(v_ctors_2076_);
return v___x_2079_;
}
else
{
if (lean_obj_tag(v_ctors_2076_) == 1)
{
lean_object* v_tail_2080_; 
v_tail_2080_ = lean_ctor_get(v_ctors_2076_, 1);
lean_inc(v_tail_2080_);
lean_dec_ref_known(v_ctors_2076_, 2);
if (lean_obj_tag(v_tail_2080_) == 0)
{
if (v_isRec_2077_ == 0)
{
return v___x_2079_;
}
else
{
return v___x_2071_;
}
}
else
{
lean_dec(v_tail_2080_);
return v___x_2071_;
}
}
else
{
lean_dec(v_ctors_2076_);
return v___x_2071_;
}
}
}
else
{
lean_dec(v_val_2073_);
return v___x_2071_;
}
}
else
{
lean_dec(v___x_2072_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_2081_, lean_object* v_constName_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Lean_isNonRecStructure(v_env_2081_, v_constName_2082_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_panic_fn_borrowed(v___x_2086_, v_msg_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2089_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_2090_ = lean_unsigned_to_nat(11u);
v___x_2091_ = lean_unsigned_to_nat(382u);
v___x_2092_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_2093_ = ((lean_object*)(l_Lean_registerStructure___closed__2));
v___x_2094_ = l_mkPanicMessageWithDecl(v___x_2093_, v___x_2092_, v___x_2091_, v___x_2090_, v___x_2089_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_2095_, lean_object* v_constName_2096_){
_start:
{
uint8_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = 0;
lean_inc_ref(v_env_2095_);
v___x_2101_ = l_Lean_Environment_find_x3f(v_env_2095_, v_constName_2096_, v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 1)
{
lean_object* v_val_2102_; 
v_val_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v___x_2101_, 1);
if (lean_obj_tag(v_val_2102_) == 5)
{
lean_object* v_val_2103_; lean_object* v_numIndices_2104_; lean_object* v_ctors_2105_; uint8_t v_isRec_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_val_2103_ = lean_ctor_get(v_val_2102_, 0);
lean_inc_ref(v_val_2103_);
lean_dec_ref_known(v_val_2102_, 1);
v_numIndices_2104_ = lean_ctor_get(v_val_2103_, 2);
lean_inc(v_numIndices_2104_);
v_ctors_2105_ = lean_ctor_get(v_val_2103_, 4);
lean_inc(v_ctors_2105_);
v_isRec_2106_ = lean_ctor_get_uint8(v_val_2103_, sizeof(void*)*6);
lean_dec_ref(v_val_2103_);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_nat_dec_eq(v_numIndices_2104_, v___x_2107_);
lean_dec(v_numIndices_2104_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v_ctors_2105_);
lean_dec_ref(v_env_2095_);
v___x_2109_ = lean_box(0);
return v___x_2109_;
}
else
{
if (lean_obj_tag(v_ctors_2105_) == 1)
{
lean_object* v_tail_2110_; 
v_tail_2110_ = lean_ctor_get(v_ctors_2105_, 1);
if (lean_obj_tag(v_tail_2110_) == 0)
{
if (v_isRec_2106_ == 0)
{
lean_object* v_head_2111_; lean_object* v___x_2112_; 
v_head_2111_ = lean_ctor_get(v_ctors_2105_, 0);
lean_inc(v_head_2111_);
lean_dec_ref_known(v_ctors_2105_, 2);
v___x_2112_ = l_Lean_Environment_find_x3f(v_env_2095_, v_head_2111_, v_isRec_2106_);
if (lean_obj_tag(v___x_2112_) == 1)
{
lean_object* v_val_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_val_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_val_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
if (lean_obj_tag(v_val_2113_) == 6)
{
lean_object* v_val_2117_; lean_object* v___x_2119_; 
v_val_2117_ = lean_ctor_get(v_val_2113_, 0);
lean_inc_ref(v_val_2117_);
lean_dec_ref_known(v_val_2113_, 1);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_val_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_val_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_del_object(v___x_2115_);
lean_dec(v_val_2113_);
goto v___jp_2097_;
}
}
}
else
{
lean_dec(v___x_2112_);
goto v___jp_2097_;
}
}
else
{
lean_object* v___x_2122_; 
lean_dec_ref_known(v_ctors_2105_, 2);
lean_dec_ref(v_env_2095_);
v___x_2122_ = lean_box(0);
return v___x_2122_;
}
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref_known(v_ctors_2105_, 2);
lean_dec_ref(v_env_2095_);
v___x_2123_ = lean_box(0);
return v___x_2123_;
}
}
else
{
lean_object* v___x_2124_; 
lean_dec(v_ctors_2105_);
lean_dec_ref(v_env_2095_);
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
}
else
{
lean_object* v___x_2125_; 
lean_dec(v_val_2102_);
lean_dec_ref(v_env_2095_);
v___x_2125_ = lean_box(0);
return v___x_2125_;
}
}
else
{
lean_object* v___x_2126_; 
lean_dec(v___x_2101_);
lean_dec_ref(v_env_2095_);
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_2099_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_2127_, lean_object* v_constName_2128_){
_start:
{
uint8_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = 0;
lean_inc_ref(v_env_2127_);
v___x_2130_ = l_Lean_Environment_find_x3f(v_env_2127_, v_constName_2128_, v___x_2129_);
if (lean_obj_tag(v___x_2130_) == 1)
{
lean_object* v_val_2131_; 
v_val_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v___x_2130_, 1);
if (lean_obj_tag(v_val_2131_) == 5)
{
lean_object* v_val_2132_; lean_object* v_numIndices_2133_; lean_object* v_ctors_2134_; uint8_t v_isRec_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_val_2132_ = lean_ctor_get(v_val_2131_, 0);
lean_inc_ref(v_val_2132_);
lean_dec_ref_known(v_val_2131_, 1);
v_numIndices_2133_ = lean_ctor_get(v_val_2132_, 2);
lean_inc(v_numIndices_2133_);
v_ctors_2134_ = lean_ctor_get(v_val_2132_, 4);
lean_inc(v_ctors_2134_);
v_isRec_2135_ = lean_ctor_get_uint8(v_val_2132_, sizeof(void*)*6);
lean_dec_ref(v_val_2132_);
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_nat_dec_eq(v_numIndices_2133_, v___x_2136_);
lean_dec(v_numIndices_2133_);
if (v___x_2137_ == 0)
{
lean_dec(v_ctors_2134_);
lean_dec_ref(v_env_2127_);
return v___x_2136_;
}
else
{
if (lean_obj_tag(v_ctors_2134_) == 1)
{
lean_object* v_tail_2138_; 
v_tail_2138_ = lean_ctor_get(v_ctors_2134_, 1);
if (lean_obj_tag(v_tail_2138_) == 0)
{
if (v_isRec_2135_ == 0)
{
lean_object* v_head_2139_; lean_object* v___x_2140_; 
v_head_2139_ = lean_ctor_get(v_ctors_2134_, 0);
lean_inc(v_head_2139_);
lean_dec_ref_known(v_ctors_2134_, 2);
v___x_2140_ = l_Lean_Environment_find_x3f(v_env_2127_, v_head_2139_, v_isRec_2135_);
if (lean_obj_tag(v___x_2140_) == 1)
{
lean_object* v_val_2141_; 
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___x_2140_, 1);
if (lean_obj_tag(v_val_2141_) == 6)
{
lean_object* v_val_2142_; lean_object* v_numFields_2143_; 
v_val_2142_ = lean_ctor_get(v_val_2141_, 0);
lean_inc_ref(v_val_2142_);
lean_dec_ref_known(v_val_2141_, 1);
v_numFields_2143_ = lean_ctor_get(v_val_2142_, 4);
lean_inc(v_numFields_2143_);
lean_dec_ref(v_val_2142_);
return v_numFields_2143_;
}
else
{
lean_dec(v_val_2141_);
return v___x_2136_;
}
}
else
{
lean_dec(v___x_2140_);
return v___x_2136_;
}
}
else
{
lean_dec_ref_known(v_ctors_2134_, 2);
lean_dec_ref(v_env_2127_);
return v___x_2136_;
}
}
else
{
lean_dec_ref_known(v_ctors_2134_, 2);
lean_dec_ref(v_env_2127_);
return v___x_2136_;
}
}
else
{
lean_dec(v_ctors_2134_);
lean_dec_ref(v_env_2127_);
return v___x_2136_;
}
}
}
else
{
lean_object* v___x_2144_; 
lean_dec(v_val_2131_);
lean_dec_ref(v_env_2127_);
v___x_2144_ = lean_unsigned_to_nat(0u);
return v___x_2144_;
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v___x_2130_);
lean_dec_ref(v_env_2127_);
v___x_2145_ = lean_unsigned_to_nat(0u);
return v___x_2145_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_obj_once(&l_Lean_instInhabitedStructureState_default___closed__0, &l_Lean_instInhabitedStructureState_default___closed__0_once, _init_l_Lean_instInhabitedStructureState_default___closed__0);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(lean_object* v___x_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object* v___x_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(v___x_2153_);
return v_res_2155_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___f_2157_; 
v___x_2156_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___f_2157_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2157_, 0, v___x_2156_);
return v___f_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; 
v___f_2163_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_box(1);
v___x_2166_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_));
v___x_2167_ = 0;
v___x_2168_ = 1;
v___x_2169_ = l_Lean_registerEnvExtension___redArg(v___f_2163_, v___x_2164_, v___x_2165_, v___x_2166_, v___x_2167_, v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2____boxed(lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2045624844____hygCtx___hyg_2_();
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_2172_, lean_object* v_structName_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v_asyncMode_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2174_ = l_Lean_structureResolutionExt;
v_asyncMode_2175_ = lean_ctor_get(v___x_2174_, 2);
v___x_2176_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_2177_ = lean_box(0);
v___x_2178_ = 0;
v___x_2179_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2176_, v___x_2174_, v_env_2172_, v_asyncMode_2175_, v___x_2177_, v___x_2178_);
v___x_2180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_2179_, v_structName_2173_);
lean_dec(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_2181_, lean_object* v_structName_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2181_, v_structName_2182_);
lean_dec(v_structName_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_2184_, lean_object* v___x_2185_, lean_object* v_structName_2186_, lean_object* v_resolutionOrder_2187_, lean_object* v_s_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2184_, v___x_2185_, v_s_2188_, v_structName_2186_, v_resolutionOrder_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_2190_, lean_object* v_env_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v_asyncMode_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; 
v___x_2192_ = l_Lean_structureResolutionExt;
v_asyncMode_2193_ = lean_ctor_get(v___x_2192_, 2);
v___x_2194_ = lean_box(0);
v___x_2195_ = 1;
v___x_2196_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_2192_, v_env_2191_, v___f_2190_, v_asyncMode_2193_, v___x_2194_, v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_2197_, lean_object* v_structName_2198_, lean_object* v_resolutionOrder_2199_){
_start:
{
lean_object* v_modifyEnv_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
v_modifyEnv_2200_ = lean_ctor_get(v_inst_2197_, 1);
lean_inc(v_modifyEnv_2200_);
lean_dec_ref(v_inst_2197_);
v___x_2201_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_2202_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2203_, 0, v___x_2201_);
lean_closure_set(v___f_2203_, 1, v___x_2202_);
lean_closure_set(v___f_2203_, 2, v_structName_2198_);
lean_closure_set(v___f_2203_, 3, v_resolutionOrder_2199_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2204_, 0, v___f_2203_);
v___x_2205_ = lean_apply_1(v_modifyEnv_2200_, v___f_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_2206_, lean_object* v_inst_2207_, lean_object* v_structName_2208_, lean_object* v_resolutionOrder_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2207_, v_structName_2208_, v_resolutionOrder_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_2228_, lean_object* v_resOrders_2229_, lean_object* v___x_2230_, lean_object* v_toPure_2231_, lean_object* v_____s_2232_){
_start:
{
lean_object* v_fst_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2248_; 
v_fst_2233_ = lean_ctor_get(v_____s_2232_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_____s_2232_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_____s_2232_, 1);
lean_dec(v_unused_2249_);
v___x_2235_ = v_____s_2232_;
v_isShared_2236_ = v_isSharedCheck_2248_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_fst_2233_);
lean_dec(v_____s_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2248_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
if (lean_obj_tag(v_fst_2233_) == 0)
{
uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2237_ = 0;
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_array_get_borrowed(v___x_2228_, v_resOrders_2229_, v___x_2238_);
v___x_2240_ = lean_array_get_borrowed(v___x_2230_, v___x_2239_, v___x_2238_);
v___x_2241_ = lean_box(v___x_2237_);
lean_inc(v___x_2240_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v___x_2240_);
lean_ctor_set(v___x_2235_, 0, v___x_2241_);
v___x_2243_ = v___x_2235_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2240_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_apply_2(v_toPure_2231_, lean_box(0), v___x_2243_);
return v___x_2244_;
}
}
else
{
lean_object* v_val_2246_; lean_object* v___x_2247_; 
lean_del_object(v___x_2235_);
v_val_2246_ = lean_ctor_get(v_fst_2233_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_fst_2233_, 1);
v___x_2247_ = lean_apply_2(v_toPure_2231_, lean_box(0), v_val_2246_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_2250_, lean_object* v_resOrders_2251_, lean_object* v___x_2252_, lean_object* v_toPure_2253_, lean_object* v_____s_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_2250_, v_resOrders_2251_, v___x_2252_, v_toPure_2253_, v_____s_2254_);
lean_dec(v___x_2252_);
lean_dec_ref(v_resOrders_2251_);
lean_dec_ref(v___x_2250_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_2256_, lean_object* v_____do__lift_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_apply_2(v_toPure_2256_, lean_box(0), v_____do__lift_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_2259_, lean_object* v_toPure_2260_, lean_object* v___x_2261_, lean_object* v_____s_2262_){
_start:
{
lean_object* v_fst_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2281_; 
v_fst_2263_ = lean_ctor_get(v_____s_2262_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_____s_2262_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_____s_2262_, 1);
lean_dec(v_unused_2282_);
v___x_2265_ = v_____s_2262_;
v_isShared_2266_ = v_isSharedCheck_2281_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_fst_2263_);
lean_dec(v_____s_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2281_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
if (lean_obj_tag(v_fst_2263_) == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_del_object(v___x_2265_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2259_);
v___x_2268_ = lean_apply_2(v_toPure_2260_, lean_box(0), v___x_2267_);
return v___x_2268_;
}
else
{
lean_object* v___x_2270_; 
lean_dec_ref(v___x_2259_);
lean_inc_ref(v_fst_2263_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___x_2261_);
v___x_2270_ = v___x_2265_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_fst_2263_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2261_);
v___x_2270_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
v_isSharedCheck_2278_ = !lean_is_exclusive(v_fst_2263_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v_fst_2263_, 0);
lean_dec(v_unused_2279_);
v___x_2272_ = v_fst_2263_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_dec(v_fst_2263_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2270_);
v___x_2275_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_apply_2(v_toPure_2260_, lean_box(0), v___x_2275_);
return v___x_2276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_2283_, lean_object* v_next_2284_, lean_object* v_G_2285_, lean_object* v_____do__lift_2286_){
_start:
{
if (lean_obj_tag(v_____do__lift_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
lean_dec(v_G_2285_);
v_a_2287_ = lean_ctor_get(v_____do__lift_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v_____do__lift_2286_, 1);
v___x_2288_ = lean_apply_2(v_toPure_2283_, lean_box(0), v_a_2287_);
return v___x_2288_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_toPure_2283_);
v_a_2289_ = lean_ctor_get(v_____do__lift_2286_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v_____do__lift_2286_, 1);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_nat_add(v_next_2284_, v___x_2290_);
v___x_2292_ = lean_apply_4(v_G_2285_, v___x_2291_, v_a_2289_, lean_box(0), lean_box(0));
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2293_, lean_object* v_next_2294_, lean_object* v_G_2295_, lean_object* v_____do__lift_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2293_, v_next_2294_, v_G_2295_, v_____do__lift_2296_);
lean_dec(v_next_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2298_, uint8_t v___x_2299_, lean_object* v_v_2300_){
_start:
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_name_eq(v_v_2300_, v___x_2298_);
if (v___x_2301_ == 0)
{
return v___x_2301_;
}
else
{
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2302_, lean_object* v___x_2303_, lean_object* v_v_2304_){
_start:
{
uint8_t v___x_1578__boxed_2305_; uint8_t v_res_2306_; lean_object* v_r_2307_; 
v___x_1578__boxed_2305_ = lean_unbox(v___x_2303_);
v_res_2306_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2302_, v___x_1578__boxed_2305_, v_v_2304_);
lean_dec(v_v_2304_);
lean_dec(v___x_2302_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2327_, lean_object* v___f_2328_, lean_object* v_resOrder_2329_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_array_2334_; lean_object* v_start_2335_; lean_object* v_stop_2336_; uint8_t v___x_2337_; lean_object* v___y_2339_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_array_get_size(v_resOrder_2329_);
v___x_2332_ = l_Array_toSubarray___redArg(v_resOrder_2329_, v___x_2330_, v___x_2331_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2334_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_array_2334_);
v_start_2335_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_start_2335_);
v_stop_2336_ = lean_ctor_get(v___x_2332_, 2);
lean_inc(v_stop_2336_);
lean_dec_ref(v___x_2332_);
v___x_2337_ = lean_nat_dec_lt(v_start_2335_, v_stop_2336_);
if (v___x_2337_ == 0)
{
lean_dec(v_stop_2336_);
lean_dec(v_start_2335_);
lean_dec_ref(v_array_2334_);
lean_dec_ref(v___f_2328_);
return v___x_2327_;
}
else
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_array_get_size(v_array_2334_);
v___x_2347_ = lean_nat_dec_le(v_stop_2336_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_dec(v_stop_2336_);
v___y_2339_ = v___x_2346_;
goto v___jp_2338_;
}
else
{
v___y_2339_ = v_stop_2336_;
goto v___jp_2338_;
}
}
v___jp_2338_:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_nat_dec_lt(v_start_2335_, v___y_2339_);
if (v___x_2340_ == 0)
{
lean_dec(v___y_2339_);
lean_dec(v_start_2335_);
lean_dec_ref(v_array_2334_);
lean_dec_ref(v___f_2328_);
return v___x_2337_;
}
else
{
size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2341_ = lean_usize_of_nat(v_start_2335_);
lean_dec(v_start_2335_);
v___x_2342_ = lean_usize_of_nat(v___y_2339_);
lean_dec(v___y_2339_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2333_, v___f_2328_, v_array_2334_, v___x_2341_, v___x_2342_);
v___x_2344_ = lean_unbox(v___x_2343_);
lean_dec(v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2340_;
}
else
{
uint8_t v___x_2345_; 
v___x_2345_ = 0;
return v___x_2345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2348_, lean_object* v___f_2349_, lean_object* v_resOrder_2350_){
_start:
{
uint8_t v___x_1623__boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v___x_1623__boxed_2351_ = lean_unbox(v___x_2348_);
v_res_2352_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1623__boxed_2351_, v___f_2349_, v_resOrder_2350_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2354_, uint8_t v___y_2355_, lean_object* v_v_2356_){
_start:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = lean_apply_1(v___f_2354_, v_v_2356_);
v___x_2358_ = lean_unbox(v___x_2357_);
if (v___x_2358_ == 0)
{
return v___y_2355_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2360_, lean_object* v___y_2361_, lean_object* v_v_2362_){
_start:
{
uint8_t v___y_1679__boxed_2363_; uint8_t v_res_2364_; lean_object* v_r_2365_; 
v___y_1679__boxed_2363_ = lean_unbox(v___y_2361_);
v_res_2364_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2360_, v___y_1679__boxed_2363_, v_v_2362_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2366_, uint8_t v___x_2367_, lean_object* v_v_2368_){
_start:
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = lean_apply_1(v___f_2366_, v_v_2368_);
v___x_2370_ = lean_unbox(v___x_2369_);
if (v___x_2370_ == 0)
{
return v___x_2367_;
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = 0;
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2372_, lean_object* v___x_2373_, lean_object* v_v_2374_){
_start:
{
uint8_t v___x_1691__boxed_2375_; uint8_t v_res_2376_; lean_object* v_r_2377_; 
v___x_1691__boxed_2375_ = lean_unbox(v___x_2373_);
v_res_2376_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2372_, v___x_1691__boxed_2375_, v_v_2374_);
v_r_2377_ = lean_box(v_res_2376_);
return v_r_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2378_, lean_object* v_toPure_2379_, lean_object* v___x_2380_, lean_object* v_resOrders_2381_, lean_object* v___x_2382_, lean_object* v___x_2383_, lean_object* v_toBind_2384_, lean_object* v___f_2385_, lean_object* v___x_2386_, lean_object* v_next_2387_, lean_object* v___x_2388_, lean_object* v_next_2389_, lean_object* v_acc_2390_, lean_object* v_h_2391_, lean_object* v_G_2392_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_nat_dec_lt(v_next_2389_, v___x_2378_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v_G_2392_);
lean_dec(v_next_2389_);
lean_dec_ref(v___x_2386_);
lean_dec(v___f_2385_);
lean_dec(v_toBind_2384_);
lean_dec(v___x_2383_);
lean_dec_ref(v_resOrders_2381_);
lean_dec(v___x_2378_);
v___x_2394_ = lean_apply_2(v_toPure_2379_, lean_box(0), v_acc_2390_);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_array_2399_; lean_object* v_start_2400_; lean_object* v_stop_2401_; lean_object* v___f_2402_; lean_object* v___y_2404_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; lean_object* v___f_2432_; uint8_t v___y_2434_; uint8_t v___x_2446_; 
lean_dec_ref(v_acc_2390_);
v___x_2395_ = lean_array_get_borrowed(v___x_2380_, v_resOrders_2381_, v_next_2389_);
v___x_2396_ = lean_array_get(v___x_2382_, v___x_2395_, v___x_2383_);
lean_inc_n(v_next_2389_, 2);
lean_inc(v___x_2383_);
lean_inc_ref(v_resOrders_2381_);
v___x_2397_ = l_Array_toSubarray___redArg(v_resOrders_2381_, v___x_2383_, v_next_2389_);
v___x_2398_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2399_ = lean_ctor_get(v___x_2397_, 0);
lean_inc_ref(v_array_2399_);
v_start_2400_ = lean_ctor_get(v___x_2397_, 1);
lean_inc(v_start_2400_);
v_stop_2401_ = lean_ctor_get(v___x_2397_, 2);
lean_inc(v_stop_2401_);
lean_dec_ref(v___x_2397_);
lean_inc(v_toPure_2379_);
v___f_2402_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2402_, 0, v_toPure_2379_);
lean_closure_set(v___f_2402_, 1, v_next_2389_);
lean_closure_set(v___f_2402_, 2, v_G_2392_);
v___x_2429_ = lean_box(v___x_2393_);
lean_inc(v___x_2396_);
v___f_2430_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 3, 2);
lean_closure_set(v___f_2430_, 0, v___x_2396_);
lean_closure_set(v___f_2430_, 1, v___x_2429_);
v___x_2431_ = lean_box(v___x_2393_);
v___f_2432_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2432_, 0, v___x_2431_);
lean_closure_set(v___f_2432_, 1, v___f_2430_);
v___x_2446_ = lean_nat_dec_lt(v_start_2400_, v_stop_2401_);
if (v___x_2446_ == 0)
{
lean_dec(v_stop_2401_);
lean_dec(v_start_2400_);
lean_dec_ref(v_array_2399_);
v___y_2434_ = v___x_2393_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2447_; lean_object* v___f_2448_; lean_object* v___y_2450_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2447_ = lean_box(v___x_2393_);
lean_inc_ref(v___f_2432_);
v___f_2448_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2448_, 0, v___f_2432_);
lean_closure_set(v___f_2448_, 1, v___x_2447_);
v___x_2456_ = lean_array_get_size(v_array_2399_);
v___x_2457_ = lean_nat_dec_le(v_stop_2401_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_dec(v_stop_2401_);
v___y_2450_ = v___x_2456_;
goto v___jp_2449_;
}
else
{
v___y_2450_ = v_stop_2401_;
goto v___jp_2449_;
}
v___jp_2449_:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_lt(v_start_2400_, v___y_2450_);
if (v___x_2451_ == 0)
{
lean_dec(v___y_2450_);
lean_dec_ref(v___f_2448_);
lean_dec(v_start_2400_);
lean_dec_ref(v_array_2399_);
v___y_2434_ = v___x_2446_;
goto v___jp_2433_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2452_ = lean_usize_of_nat(v_start_2400_);
lean_dec(v_start_2400_);
v___x_2453_ = lean_usize_of_nat(v___y_2450_);
lean_dec(v___y_2450_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2398_, v___f_2448_, v_array_2399_, v___x_2452_, v___x_2453_);
v___x_2455_ = lean_unbox(v___x_2454_);
lean_dec(v___x_2454_);
if (v___x_2455_ == 0)
{
v___y_2434_ = v___x_2451_;
goto v___jp_2433_;
}
else
{
lean_dec_ref(v___f_2432_);
lean_dec(v___x_2396_);
lean_dec(v_next_2389_);
lean_dec(v___x_2383_);
lean_dec_ref(v_resOrders_2381_);
lean_dec(v___x_2378_);
goto v___jp_2407_;
}
}
}
}
v___jp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_inc(v_toBind_2384_);
v___x_2405_ = lean_apply_4(v_toBind_2384_, lean_box(0), lean_box(0), v___y_2404_, v___f_2385_);
v___x_2406_ = lean_apply_4(v_toBind_2384_, lean_box(0), lean_box(0), v___x_2405_, v___f_2402_);
return v___x_2406_;
}
v___jp_2407_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2386_);
v___x_2409_ = lean_apply_2(v_toPure_2379_, lean_box(0), v___x_2408_);
v___y_2404_ = v___x_2409_;
goto v___jp_2403_;
}
v___jp_2410_:
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2411_ = lean_nat_dec_eq(v_next_2387_, v___x_2383_);
lean_dec(v___x_2383_);
v___x_2412_ = lean_box(v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2396_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2388_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
v___x_2417_ = lean_apply_2(v_toPure_2379_, lean_box(0), v___x_2416_);
v___y_2404_ = v___x_2417_;
goto v___jp_2403_;
}
v___jp_2418_:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_nat_dec_lt(v___y_2420_, v___y_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v___x_2386_);
goto v___jp_2410_;
}
else
{
size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2425_ = lean_usize_of_nat(v___y_2420_);
lean_dec(v___y_2420_);
v___x_2426_ = lean_usize_of_nat(v___y_2423_);
lean_dec(v___y_2423_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2422_, v___y_2421_, v___y_2419_, v___x_2425_, v___x_2426_);
v___x_2428_ = lean_unbox(v___x_2427_);
lean_dec(v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v___x_2386_);
goto v___jp_2410_;
}
else
{
lean_dec(v___x_2396_);
lean_dec(v___x_2383_);
goto v___jp_2407_;
}
}
}
v___jp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_array_2438_; lean_object* v_start_2439_; lean_object* v_stop_2440_; uint8_t v___x_2441_; 
v___x_2435_ = lean_unsigned_to_nat(1u);
v___x_2436_ = lean_nat_add(v_next_2389_, v___x_2435_);
lean_dec(v_next_2389_);
v___x_2437_ = l_Array_toSubarray___redArg(v_resOrders_2381_, v___x_2436_, v___x_2378_);
v_array_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_ref(v_array_2438_);
v_start_2439_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_start_2439_);
v_stop_2440_ = lean_ctor_get(v___x_2437_, 2);
lean_inc(v_stop_2440_);
lean_dec_ref(v___x_2437_);
v___x_2441_ = lean_nat_dec_lt(v_start_2439_, v_stop_2440_);
if (v___x_2441_ == 0)
{
lean_dec(v_stop_2440_);
lean_dec(v_start_2439_);
lean_dec_ref(v_array_2438_);
lean_dec_ref(v___f_2432_);
lean_dec_ref(v___x_2386_);
goto v___jp_2410_;
}
else
{
lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2442_ = lean_box(v___y_2434_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2443_, 0, v___f_2432_);
lean_closure_set(v___f_2443_, 1, v___x_2442_);
v___x_2444_ = lean_array_get_size(v_array_2438_);
v___x_2445_ = lean_nat_dec_le(v_stop_2440_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_dec(v_stop_2440_);
v___y_2419_ = v_array_2438_;
v___y_2420_ = v_start_2439_;
v___y_2421_ = v___f_2443_;
v___y_2422_ = v___x_2398_;
v___y_2423_ = v___x_2444_;
goto v___jp_2418_;
}
else
{
v___y_2419_ = v_array_2438_;
v___y_2420_ = v_start_2439_;
v___y_2421_ = v___f_2443_;
v___y_2422_ = v___x_2398_;
v___y_2423_ = v_stop_2440_;
goto v___jp_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2458_, lean_object* v_toPure_2459_, lean_object* v___x_2460_, lean_object* v_resOrders_2461_, lean_object* v___x_2462_, lean_object* v___x_2463_, lean_object* v_toBind_2464_, lean_object* v___f_2465_, lean_object* v___x_2466_, lean_object* v_next_2467_, lean_object* v___x_2468_, lean_object* v_next_2469_, lean_object* v_acc_2470_, lean_object* v_h_2471_, lean_object* v_G_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2458_, v_toPure_2459_, v___x_2460_, v_resOrders_2461_, v___x_2462_, v___x_2463_, v_toBind_2464_, v___f_2465_, v___x_2466_, v_next_2467_, v___x_2468_, v_next_2469_, v_acc_2470_, v_h_2471_, v_G_2472_);
lean_dec(v_next_2467_);
lean_dec(v___x_2462_);
lean_dec_ref(v___x_2460_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2474_, lean_object* v_toPure_2475_, lean_object* v___x_2476_, lean_object* v_resOrders_2477_, lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v_toBind_2480_, lean_object* v___f_2481_, lean_object* v___x_2482_, lean_object* v___x_2483_, lean_object* v___f_2484_, lean_object* v___f_2485_, lean_object* v_next_2486_, lean_object* v_acc_2487_, lean_object* v_h_2488_, lean_object* v_G_2489_){
_start:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_lt(v_next_2486_, v___x_2474_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_G_2489_);
lean_dec(v_next_2486_);
lean_dec(v___f_2485_);
lean_dec(v___f_2484_);
lean_dec_ref(v___x_2482_);
lean_dec(v___f_2481_);
lean_dec(v_toBind_2480_);
lean_dec(v___x_2479_);
lean_dec(v___x_2478_);
lean_dec_ref(v_resOrders_2477_);
lean_dec_ref(v___x_2476_);
v___x_2491_ = lean_apply_2(v_toPure_2475_, lean_box(0), v_acc_2487_);
return v___x_2491_;
}
else
{
lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec_ref(v_acc_2487_);
lean_inc(v_next_2486_);
lean_inc(v_toPure_2475_);
v___f_2492_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2492_, 0, v_toPure_2475_);
lean_closure_set(v___f_2492_, 1, v_next_2486_);
lean_closure_set(v___f_2492_, 2, v_G_2489_);
v___x_2493_ = lean_nat_sub(v___x_2474_, v_next_2486_);
lean_inc_ref(v___x_2482_);
lean_inc_n(v_toBind_2480_, 3);
lean_inc(v___x_2479_);
v___f_2494_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2494_, 0, v___x_2493_);
lean_closure_set(v___f_2494_, 1, v_toPure_2475_);
lean_closure_set(v___f_2494_, 2, v___x_2476_);
lean_closure_set(v___f_2494_, 3, v_resOrders_2477_);
lean_closure_set(v___f_2494_, 4, v___x_2478_);
lean_closure_set(v___f_2494_, 5, v___x_2479_);
lean_closure_set(v___f_2494_, 6, v_toBind_2480_);
lean_closure_set(v___f_2494_, 7, v___f_2481_);
lean_closure_set(v___f_2494_, 8, v___x_2482_);
lean_closure_set(v___f_2494_, 9, v_next_2486_);
lean_closure_set(v___f_2494_, 10, v___x_2483_);
v___x_2495_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2494_, v___x_2479_, v___x_2482_, lean_box(0));
v___x_2496_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2495_, v___f_2484_);
v___x_2497_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2496_, v___f_2485_);
v___x_2498_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2497_, v___f_2492_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2499_, lean_object* v_toPure_2500_, lean_object* v___x_2501_, lean_object* v_resOrders_2502_, lean_object* v___x_2503_, lean_object* v___x_2504_, lean_object* v_toBind_2505_, lean_object* v___f_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v___f_2509_, lean_object* v___f_2510_, lean_object* v_next_2511_, lean_object* v_acc_2512_, lean_object* v_h_2513_, lean_object* v_G_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2499_, v_toPure_2500_, v___x_2501_, v_resOrders_2502_, v___x_2503_, v___x_2504_, v_toBind_2505_, v___f_2506_, v___x_2507_, v___x_2508_, v___f_2509_, v___f_2510_, v_next_2511_, v_acc_2512_, v_h_2513_, v_G_2514_);
lean_dec(v___x_2499_);
return v_res_2515_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Array_instInhabited___redArg();
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2520_, lean_object* v_resOrders_2521_){
_start:
{
lean_object* v_toApplicative_2522_; lean_object* v_toBind_2523_; lean_object* v_toPure_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_toApplicative_2522_ = lean_ctor_get(v_inst_2520_, 0);
lean_inc_ref(v_toApplicative_2522_);
v_toBind_2523_ = lean_ctor_get(v_inst_2520_, 1);
lean_inc_n(v_toBind_2523_, 2);
lean_dec_ref(v_inst_2520_);
v_toPure_2524_ = lean_ctor_get(v_toApplicative_2522_, 1);
lean_inc_n(v_toPure_2524_, 4);
lean_dec_ref(v_toApplicative_2522_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2527_ = lean_array_get_size(v_resOrders_2521_);
lean_inc_ref(v_resOrders_2521_);
v___f_2528_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2528_, 0, v___x_2526_);
lean_closure_set(v___f_2528_, 1, v_resOrders_2521_);
lean_closure_set(v___f_2528_, 2, v___x_2525_);
lean_closure_set(v___f_2528_, 3, v_toPure_2524_);
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2529_, 0, v_toPure_2524_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = lean_box(0);
v___x_2532_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
v___f_2533_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2533_, 0, v___x_2532_);
lean_closure_set(v___f_2533_, 1, v_toPure_2524_);
lean_closure_set(v___f_2533_, 2, v___x_2531_);
lean_inc_ref(v___f_2529_);
v___f_2534_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2534_, 0, v___x_2527_);
lean_closure_set(v___f_2534_, 1, v_toPure_2524_);
lean_closure_set(v___f_2534_, 2, v___x_2526_);
lean_closure_set(v___f_2534_, 3, v_resOrders_2521_);
lean_closure_set(v___f_2534_, 4, v___x_2525_);
lean_closure_set(v___f_2534_, 5, v___x_2530_);
lean_closure_set(v___f_2534_, 6, v_toBind_2523_);
lean_closure_set(v___f_2534_, 7, v___f_2529_);
lean_closure_set(v___f_2534_, 8, v___x_2532_);
lean_closure_set(v___f_2534_, 9, v___x_2531_);
lean_closure_set(v___f_2534_, 10, v___f_2533_);
lean_closure_set(v___f_2534_, 11, v___f_2529_);
v___x_2535_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2534_, v___x_2530_, v___x_2532_, lean_box(0));
v___x_2536_ = lean_apply_4(v_toBind_2523_, lean_box(0), lean_box(0), v___x_2535_, v___f_2528_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2537_, lean_object* v_inst_2538_, lean_object* v_resOrders_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2538_, v_resOrders_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2541_){
_start:
{
lean_object* v_structName_2542_; 
v_structName_2542_ = lean_ctor_get(v_x_2541_, 0);
lean_inc(v_structName_2542_);
return v_structName_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2543_);
lean_dec_ref(v_x_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2545_, lean_object* v_result_2546_, lean_object* v_____r_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_apply_2(v_toPure_2545_, lean_box(0), v_result_2546_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2549_, lean_object* v_inst_2550_, lean_object* v_structName_2551_, lean_object* v_toBind_2552_, lean_object* v_result_2553_){
_start:
{
lean_object* v_resolutionOrder_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_resolutionOrder_2554_ = lean_ctor_get(v_result_2553_, 0);
lean_inc_ref(v_resolutionOrder_2554_);
v___f_2555_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2555_, 0, v_toPure_2549_);
lean_closure_set(v___f_2555_, 1, v_result_2553_);
v___x_2556_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2550_, v_structName_2551_, v_resolutionOrder_2554_);
v___x_2557_ = lean_apply_4(v_toBind_2552_, lean_box(0), lean_box(0), v___x_2556_, v___f_2555_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_toPure_2558_, lean_object* v_____s_2559_){
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
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v_toPure_2571_, lean_object* v_____do__lift_2572_){
_start:
{
if (lean_obj_tag(v_____do__lift_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2581_; 
v_a_2573_ = lean_ctor_get(v_____do__lift_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_____do__lift_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2575_ = v_____do__lift_2572_;
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v_____do__lift_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 1);
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_apply_2(v_toPure_2571_, lean_box(0), v___x_2578_);
return v___x_2579_;
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
v_a_2582_ = lean_ctor_get(v_____do__lift_2572_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_____do__lift_2572_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v_____do__lift_2572_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v_____do__lift_2572_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_apply_2(v_toPure_2571_, lean_box(0), v___x_2587_);
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v___x_2591_, lean_object* v___f_2592_, lean_object* v_x_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2594_ = lean_array_get_size(v_x_2593_);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2591_);
v___x_2596_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2597_ = lean_nat_dec_lt(v___x_2591_, v___x_2594_);
if (v___x_2597_ == 0)
{
lean_dec_ref(v_x_2593_);
lean_dec_ref(v___f_2592_);
return v___x_2595_;
}
else
{
size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = ((size_t)0ULL);
v___x_2599_ = lean_usize_of_nat(v___x_2594_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2596_, v___f_2592_, v_x_2593_, v___x_2598_, v___x_2599_, v___x_2595_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v___x_2601_, lean_object* v___f_2602_, lean_object* v_x_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v___x_2601_, v___f_2602_, v_x_2603_);
lean_dec(v___x_2601_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v_snd_2605_, lean_object* v_x1_2606_, lean_object* v_x2_2607_){
_start:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_name_eq(v_x2_2607_, v_snd_2605_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_array_push(v_x1_2606_, v_x2_2607_);
return v___x_2609_;
}
else
{
lean_dec(v_x2_2607_);
return v_x1_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed(lean_object* v_snd_2610_, lean_object* v_x1_2611_, lean_object* v_x2_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__8(v_snd_2610_, v_x1_2611_, v_x2_2612_);
lean_dec(v_snd_2610_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v___x_2614_, lean_object* v___f_2615_, lean_object* v_x1_2616_, lean_object* v_x2_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v_array_2621_; lean_object* v_start_2622_; lean_object* v_stop_2623_; lean_object* v___y_2625_; uint8_t v___x_2632_; 
v___x_2618_ = lean_array_get_size(v_x2_2617_);
lean_inc_ref(v_x2_2617_);
v___x_2619_ = l_Array_toSubarray___redArg(v_x2_2617_, v___x_2614_, v___x_2618_);
v___x_2620_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2621_ = lean_ctor_get(v___x_2619_, 0);
lean_inc_ref(v_array_2621_);
v_start_2622_ = lean_ctor_get(v___x_2619_, 1);
lean_inc(v_start_2622_);
v_stop_2623_ = lean_ctor_get(v___x_2619_, 2);
lean_inc(v_stop_2623_);
lean_dec_ref(v___x_2619_);
v___x_2632_ = lean_nat_dec_lt(v_start_2622_, v_stop_2623_);
if (v___x_2632_ == 0)
{
lean_dec(v_stop_2623_);
lean_dec(v_start_2622_);
lean_dec_ref(v_array_2621_);
lean_dec_ref(v_x2_2617_);
lean_dec_ref(v___f_2615_);
return v_x1_2616_;
}
else
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = lean_array_get_size(v_array_2621_);
v___x_2634_ = lean_nat_dec_le(v_stop_2623_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_dec(v_stop_2623_);
v___y_2625_ = v___x_2633_;
goto v___jp_2624_;
}
else
{
v___y_2625_ = v_stop_2623_;
goto v___jp_2624_;
}
}
v___jp_2624_:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_nat_dec_lt(v_start_2622_, v___y_2625_);
if (v___x_2626_ == 0)
{
lean_dec(v___y_2625_);
lean_dec(v_start_2622_);
lean_dec_ref(v_array_2621_);
lean_dec_ref(v_x2_2617_);
lean_dec_ref(v___f_2615_);
return v_x1_2616_;
}
else
{
size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2627_ = lean_usize_of_nat(v_start_2622_);
lean_dec(v_start_2622_);
v___x_2628_ = lean_usize_of_nat(v___y_2625_);
lean_dec(v___y_2625_);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2620_, v___f_2615_, v_array_2621_, v___x_2627_, v___x_2628_);
v___x_2630_ = lean_unbox(v___x_2629_);
lean_dec(v___x_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v_x2_2617_);
return v_x1_2616_;
}
else
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_array_push(v_x1_2616_, v_x2_2617_);
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v_snd_2635_, lean_object* v_x_2636_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_name_eq(v_x_2636_, v_snd_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed(lean_object* v_snd_2638_, lean_object* v_x_2639_){
_start:
{
uint8_t v_res_2640_; lean_object* v_r_2641_; 
v_res_2640_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__10(v_snd_2638_, v_x_2639_);
lean_dec(v_x_2639_);
lean_dec(v_snd_2638_);
v_r_2641_ = lean_box(v_res_2640_);
return v_r_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v_toPure_2643_, lean_object* v___x_2644_, lean_object* v_fst_2645_, lean_object* v_fst_2646_, lean_object* v___f_2647_, uint8_t v_relaxed_2648_, lean_object* v___x_2649_, lean_object* v_parentNames_2650_, lean_object* v___f_2651_, lean_object* v_snd_2652_, lean_object* v___f_2653_, lean_object* v___x_2654_, lean_object* v_____x_2655_){
_start:
{
lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v_defects_2669_; lean_object* v___y_2681_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2705_; uint8_t v___x_2715_; 
v_fst_2664_ = lean_ctor_get(v_____x_2655_, 0);
lean_inc(v_fst_2664_);
v_snd_2665_ = lean_ctor_get(v_____x_2655_, 1);
lean_inc_n(v_snd_2665_, 2);
lean_dec_ref(v_____x_2655_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2666_, 0, v_snd_2665_);
lean_inc(v___x_2644_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 3, 2);
lean_closure_set(v___f_2667_, 0, v___x_2644_);
lean_closure_set(v___f_2667_, 1, v___f_2666_);
v___x_2715_ = lean_unbox(v_fst_2664_);
lean_dec(v_fst_2664_);
if (v___x_2715_ == 0)
{
if (v_relaxed_2648_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2716_ = lean_array_get_size(v_fst_2646_);
v___x_2717_ = lean_mk_empty_array_with_capacity(v___x_2644_);
v___x_2718_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2719_ = lean_nat_dec_lt(v___x_2644_, v___x_2716_);
if (v___x_2719_ == 0)
{
v___y_2705_ = v___x_2717_;
goto v___jp_2704_;
}
else
{
lean_object* v___f_2720_; lean_object* v___f_2721_; size_t v___x_2722_; size_t v___x_2723_; lean_object* v___x_2724_; 
lean_inc(v_snd_2665_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10___boxed), 2, 1);
lean_closure_set(v___f_2720_, 0, v_snd_2665_);
lean_inc(v___x_2654_);
v___f_2721_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11), 4, 2);
lean_closure_set(v___f_2721_, 0, v___x_2654_);
lean_closure_set(v___f_2721_, 1, v___f_2720_);
v___x_2722_ = ((size_t)0ULL);
v___x_2723_ = lean_usize_of_nat(v___x_2716_);
lean_inc(v_fst_2646_);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2718_, v___f_2721_, v_fst_2646_, v___x_2722_, v___x_2723_, v___x_2717_);
v___y_2705_ = v___x_2724_;
goto v___jp_2704_;
}
}
else
{
lean_dec(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec_ref(v___f_2651_);
lean_dec_ref(v_parentNames_2650_);
lean_dec_ref(v___x_2649_);
v_defects_2669_ = v_snd_2652_;
goto v___jp_2668_;
}
}
else
{
lean_dec(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec_ref(v___f_2651_);
lean_dec_ref(v_parentNames_2650_);
lean_dec_ref(v___x_2649_);
v_defects_2669_ = v_snd_2652_;
goto v___jp_2668_;
}
v___jp_2656_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___y_2658_);
lean_ctor_set(v___x_2660_, 1, v___y_2657_);
v___x_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___y_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
v___x_2663_ = lean_apply_2(v_toPure_2643_, lean_box(0), v___x_2662_);
return v___x_2663_;
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; size_t v_sz_2672_; size_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2670_ = lean_array_push(v_fst_2645_, v_snd_2665_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2672_ = lean_array_size(v_fst_2646_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2671_, v___f_2667_, v_sz_2672_, v___x_2673_, v_fst_2646_);
v___x_2675_ = lean_array_get_size(v___x_2674_);
v___x_2676_ = lean_mk_empty_array_with_capacity(v___x_2644_);
v___x_2677_ = lean_nat_dec_lt(v___x_2644_, v___x_2675_);
lean_dec(v___x_2644_);
if (v___x_2677_ == 0)
{
lean_dec(v___x_2674_);
lean_dec_ref(v___f_2647_);
v___y_2657_ = v_defects_2669_;
v___y_2658_ = v___x_2670_;
v___y_2659_ = v___x_2676_;
goto v___jp_2656_;
}
else
{
size_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_usize_of_nat(v___x_2675_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2671_, v___f_2647_, v___x_2674_, v___x_2673_, v___x_2678_, v___x_2676_);
v___y_2657_ = v_defects_2669_;
v___y_2658_ = v___x_2670_;
v___y_2659_ = v___x_2679_;
goto v___jp_2656_;
}
}
v___jp_2680_:
{
lean_object* v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; size_t v_sz_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_inc_ref(v___x_2649_);
v___x_2682_ = l_Array_eraseReps___redArg(v___x_2649_, v___y_2681_);
lean_inc_n(v_snd_2665_, 2);
v___x_2683_ = l_Array_contains___redArg(v___x_2649_, v_parentNames_2650_, v_snd_2665_);
v___x_2684_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2685_ = lean_array_size(v___x_2682_);
v___x_2686_ = ((size_t)0ULL);
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2684_, v___f_2651_, v_sz_2685_, v___x_2686_, v___x_2682_);
v___x_2688_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2688_, 0, v_snd_2665_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*2, v___x_2683_);
v___x_2689_ = lean_array_push(v_snd_2652_, v___x_2688_);
v_defects_2669_ = v___x_2689_;
goto v___jp_2668_;
}
v___jp_2690_:
{
lean_object* v___x_2696_; 
lean_inc_ref(v___y_2693_);
v___x_2696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2693_, v___y_2692_, v___y_2694_, v___y_2691_, v___y_2695_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2695_);
lean_dec(v___y_2692_);
v___y_2681_ = v___x_2696_;
goto v___jp_2680_;
}
v___jp_2697_:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_nat_dec_le(v___y_2702_, v___y_2698_);
if (v___x_2703_ == 0)
{
lean_dec(v___y_2698_);
lean_inc(v___y_2702_);
v___y_2691_ = v___y_2702_;
v___y_2692_ = v___y_2699_;
v___y_2693_ = v___y_2700_;
v___y_2694_ = v___y_2701_;
v___y_2695_ = v___y_2702_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v___y_2702_;
v___y_2692_ = v___y_2699_;
v___y_2693_ = v___y_2700_;
v___y_2694_ = v___y_2701_;
v___y_2695_ = v___y_2698_;
goto v___jp_2690_;
}
}
v___jp_2704_:
{
lean_object* v___x_2706_; size_t v_sz_2707_; size_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2707_ = lean_array_size(v___y_2705_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2706_, v___f_2653_, v_sz_2707_, v___x_2708_, v___y_2705_);
v___x_2710_ = lean_array_get_size(v___x_2709_);
v___x_2711_ = lean_nat_dec_eq(v___x_2710_, v___x_2644_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2712_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___closed__0));
v___x_2713_ = lean_nat_sub(v___x_2710_, v___x_2654_);
lean_dec(v___x_2654_);
v___x_2714_ = lean_nat_dec_le(v___x_2644_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_inc(v___x_2713_);
v___y_2698_ = v___x_2713_;
v___y_2699_ = v___x_2710_;
v___y_2700_ = v___x_2712_;
v___y_2701_ = v___x_2709_;
v___y_2702_ = v___x_2713_;
goto v___jp_2697_;
}
else
{
lean_inc(v___x_2644_);
v___y_2698_ = v___x_2713_;
v___y_2699_ = v___x_2710_;
v___y_2700_ = v___x_2712_;
v___y_2701_ = v___x_2709_;
v___y_2702_ = v___x_2644_;
goto v___jp_2697_;
}
}
else
{
lean_dec(v___x_2654_);
v___y_2681_ = v___x_2709_;
goto v___jp_2680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v_toPure_2725_, lean_object* v___x_2726_, lean_object* v_fst_2727_, lean_object* v_fst_2728_, lean_object* v___f_2729_, lean_object* v_relaxed_2730_, lean_object* v___x_2731_, lean_object* v_parentNames_2732_, lean_object* v___f_2733_, lean_object* v_snd_2734_, lean_object* v___f_2735_, lean_object* v___x_2736_, lean_object* v_____x_2737_){
_start:
{
uint8_t v_relaxed_boxed_2738_; lean_object* v_res_2739_; 
v_relaxed_boxed_2738_ = lean_unbox(v_relaxed_2730_);
v_res_2739_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v_toPure_2725_, v___x_2726_, v_fst_2727_, v_fst_2728_, v___f_2729_, v_relaxed_boxed_2738_, v___x_2731_, v_parentNames_2732_, v___f_2733_, v_snd_2734_, v___f_2735_, v___x_2736_, v_____x_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v___x_2740_, lean_object* v_toPure_2741_, lean_object* v___f_2742_, uint8_t v_relaxed_2743_, lean_object* v___x_2744_, lean_object* v_parentNames_2745_, lean_object* v___f_2746_, lean_object* v___f_2747_, lean_object* v___x_2748_, lean_object* v_inst_2749_, lean_object* v_toBind_2750_, lean_object* v___f_2751_, lean_object* v_b_2752_){
_start:
{
lean_object* v_snd_2753_; lean_object* v_fst_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2780_; 
v_snd_2753_ = lean_ctor_get(v_b_2752_, 1);
v_fst_2754_ = lean_ctor_get(v_b_2752_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_b_2752_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2756_ = v_b_2752_;
v_isShared_2757_ = v_isSharedCheck_2780_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_snd_2753_);
lean_inc(v_fst_2754_);
lean_dec(v_b_2752_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2780_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2779_; 
v_fst_2758_ = lean_ctor_get(v_snd_2753_, 0);
v_snd_2759_ = lean_ctor_get(v_snd_2753_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_snd_2753_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2761_ = v_snd_2753_;
v_isShared_2762_ = v_isSharedCheck_2779_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snd_2759_);
lean_inc(v_fst_2758_);
lean_dec(v_snd_2753_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2779_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_array_get_size(v_fst_2754_);
v___x_2764_ = lean_nat_dec_eq(v___x_2763_, v___x_2740_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2761_);
lean_del_object(v___x_2756_);
v___x_2765_ = lean_box(v_relaxed_2743_);
lean_inc(v_fst_2754_);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 13, 12);
lean_closure_set(v___f_2766_, 0, v_toPure_2741_);
lean_closure_set(v___f_2766_, 1, v___x_2740_);
lean_closure_set(v___f_2766_, 2, v_fst_2758_);
lean_closure_set(v___f_2766_, 3, v_fst_2754_);
lean_closure_set(v___f_2766_, 4, v___f_2742_);
lean_closure_set(v___f_2766_, 5, v___x_2765_);
lean_closure_set(v___f_2766_, 6, v___x_2744_);
lean_closure_set(v___f_2766_, 7, v_parentNames_2745_);
lean_closure_set(v___f_2766_, 8, v___f_2746_);
lean_closure_set(v___f_2766_, 9, v_snd_2759_);
lean_closure_set(v___f_2766_, 10, v___f_2747_);
lean_closure_set(v___f_2766_, 11, v___x_2748_);
v___x_2767_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2749_, v_fst_2754_);
lean_inc(v_toBind_2750_);
v___x_2768_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2767_, v___f_2766_);
v___x_2769_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2768_, v___f_2751_);
return v___x_2769_;
}
else
{
lean_object* v___x_2771_; 
lean_dec_ref(v_inst_2749_);
lean_dec(v___x_2748_);
lean_dec_ref(v___f_2747_);
lean_dec_ref(v___f_2746_);
lean_dec_ref(v_parentNames_2745_);
lean_dec_ref(v___x_2744_);
lean_dec_ref(v___f_2742_);
lean_dec(v___x_2740_);
if (v_isShared_2762_ == 0)
{
v___x_2771_ = v___x_2761_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_fst_2758_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_snd_2759_);
v___x_2771_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v___x_2771_);
v___x_2773_ = v___x_2756_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_fst_2754_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
v___x_2775_ = lean_apply_2(v_toPure_2741_, lean_box(0), v___x_2774_);
v___x_2776_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2775_, v___f_2751_);
return v___x_2776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v___x_2781_, lean_object* v_toPure_2782_, lean_object* v___f_2783_, lean_object* v_relaxed_2784_, lean_object* v___x_2785_, lean_object* v_parentNames_2786_, lean_object* v___f_2787_, lean_object* v___f_2788_, lean_object* v___x_2789_, lean_object* v_inst_2790_, lean_object* v_toBind_2791_, lean_object* v___f_2792_, lean_object* v_b_2793_){
_start:
{
uint8_t v_relaxed_boxed_2794_; lean_object* v_res_2795_; 
v_relaxed_boxed_2794_ = lean_unbox(v_relaxed_2784_);
v_res_2795_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v___x_2781_, v_toPure_2782_, v___f_2783_, v_relaxed_boxed_2794_, v___x_2785_, v_parentNames_2786_, v___f_2787_, v___f_2788_, v___x_2789_, v_inst_2790_, v_toBind_2791_, v___f_2792_, v_b_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_array_get_borrowed(v___x_2796_, v_x_2798_, v___x_2797_);
lean_inc(v___x_2799_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2800_, v___x_2801_, v_x_2802_);
lean_dec_ref(v_x_2802_);
lean_dec(v___x_2801_);
lean_dec(v___x_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14(lean_object* v___x_2806_, lean_object* v_toPure_2807_, lean_object* v___f_2808_, uint8_t v_relaxed_2809_, lean_object* v___x_2810_, lean_object* v_parentNames_2811_, lean_object* v___f_2812_, lean_object* v_inst_2813_, lean_object* v_toBind_2814_, lean_object* v___f_2815_, lean_object* v_structName_2816_, lean_object* v___f_2817_, lean_object* v___f_2818_, lean_object* v_parentResOrders_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___y_2823_; lean_object* v_j_2834_; lean_object* v_as_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2820_ = lean_unsigned_to_nat(0u);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2821_, 0, v___x_2806_);
lean_closure_set(v___f_2821_, 1, v___x_2820_);
v_j_2834_ = lean_array_get_size(v_parentResOrders_2819_);
lean_inc_ref(v_parentNames_2811_);
v_as_2835_ = lean_array_push(v_parentResOrders_2819_, v_parentNames_2811_);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2820_, v_as_2835_, v_j_2834_);
v___x_2837_ = lean_array_get_size(v___x_2836_);
v___x_2838_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___closed__0));
v___x_2839_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2840_ = lean_nat_dec_lt(v___x_2820_, v___x_2837_);
if (v___x_2840_ == 0)
{
lean_dec_ref(v___x_2836_);
lean_dec_ref(v___f_2818_);
v___y_2823_ = v___x_2838_;
goto v___jp_2822_;
}
else
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = lean_usize_of_nat(v___x_2837_);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2839_, v___f_2818_, v___x_2836_, v___x_2841_, v___x_2842_, v___x_2838_);
v___y_2823_ = v___x_2843_;
goto v___jp_2822_;
}
v___jp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v_resOrder_2828_; lean_object* v_defects_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_box(v_relaxed_2809_);
lean_inc(v_toBind_2814_);
lean_inc_ref(v_inst_2813_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_2826_, 0, v___x_2820_);
lean_closure_set(v___f_2826_, 1, v_toPure_2807_);
lean_closure_set(v___f_2826_, 2, v___f_2808_);
lean_closure_set(v___f_2826_, 3, v___x_2825_);
lean_closure_set(v___f_2826_, 4, v___x_2810_);
lean_closure_set(v___f_2826_, 5, v_parentNames_2811_);
lean_closure_set(v___f_2826_, 6, v___f_2812_);
lean_closure_set(v___f_2826_, 7, v___f_2821_);
lean_closure_set(v___f_2826_, 8, v___x_2824_);
lean_closure_set(v___f_2826_, 9, v_inst_2813_);
lean_closure_set(v___f_2826_, 10, v_toBind_2814_);
lean_closure_set(v___f_2826_, 11, v___f_2815_);
v___x_2827_ = lean_mk_empty_array_with_capacity(v___x_2824_);
v_resOrder_2828_ = lean_array_push(v___x_2827_, v_structName_2816_);
v_defects_2829_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v_resOrder_2828_);
lean_ctor_set(v___x_2830_, 1, v_defects_2829_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___y_2823_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_2813_, v___f_2826_, v___x_2831_);
v___x_2833_ = lean_apply_4(v_toBind_2814_, lean_box(0), lean_box(0), v___x_2832_, v___f_2817_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed(lean_object* v___x_2844_, lean_object* v_toPure_2845_, lean_object* v___f_2846_, lean_object* v_relaxed_2847_, lean_object* v___x_2848_, lean_object* v_parentNames_2849_, lean_object* v___f_2850_, lean_object* v_inst_2851_, lean_object* v_toBind_2852_, lean_object* v___f_2853_, lean_object* v_structName_2854_, lean_object* v___f_2855_, lean_object* v___f_2856_, lean_object* v_parentResOrders_2857_){
_start:
{
uint8_t v_relaxed_boxed_2858_; lean_object* v_res_2859_; 
v_relaxed_boxed_2858_ = lean_unbox(v_relaxed_2847_);
v_res_2859_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__14(v___x_2844_, v_toPure_2845_, v___f_2846_, v_relaxed_boxed_2858_, v___x_2848_, v_parentNames_2849_, v___f_2850_, v_inst_2851_, v_toBind_2852_, v___f_2853_, v_structName_2854_, v___f_2855_, v___f_2856_, v_parentResOrders_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = lean_array_get_size(v_x_2860_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_nat_dec_eq(v___x_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
uint8_t v___x_2864_; 
v___x_2864_ = 1;
return v___x_2864_;
}
else
{
uint8_t v___x_2865_; 
v___x_2865_ = 0;
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2866_);
lean_dec_ref(v_x_2866_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2869_, lean_object* v_x1_2870_, lean_object* v_x2_2871_){
_start:
{
lean_object* v___x_2872_; uint8_t v___x_2873_; 
lean_inc_ref(v_x2_2871_);
v___x_2872_ = lean_apply_1(v___f_2869_, v_x2_2871_);
v___x_2873_ = lean_unbox(v___x_2872_);
if (v___x_2873_ == 0)
{
lean_dec_ref(v_x2_2871_);
return v_x1_2870_;
}
else
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_array_push(v_x1_2870_, v_x2_2871_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_toPure_2875_, lean_object* v_____do__lift_2876_){
_start:
{
lean_object* v_resolutionOrder_2877_; lean_object* v___x_2878_; 
v_resolutionOrder_2877_ = lean_ctor_get(v_____do__lift_2876_, 0);
lean_inc_ref(v_resolutionOrder_2877_);
lean_dec_ref(v_____do__lift_2876_);
v___x_2878_ = lean_apply_2(v_toPure_2875_, lean_box(0), v_resolutionOrder_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v___x_2879_, lean_object* v_parentNames_2880_, lean_object* v_x_2881_){
_start:
{
uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc(v_x_2881_);
v___x_2882_ = l_Array_contains___redArg(v___x_2879_, v_parentNames_2880_, v_x_2881_);
v___x_2883_ = lean_box(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v_x_2881_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_structName_2891_, lean_object* v_parentNames_2892_, uint8_t v_relaxed_2893_){
_start:
{
lean_object* v_toApplicative_2894_; lean_object* v_toBind_2895_; lean_object* v_toPure_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___f_2901_; lean_object* v___f_2902_; lean_object* v___f_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___f_2906_; size_t v_sz_2907_; size_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_toApplicative_2894_ = lean_ctor_get(v_inst_2889_, 0);
v_toBind_2895_ = lean_ctor_get(v_inst_2889_, 1);
lean_inc_n(v_toBind_2895_, 3);
v_toPure_2896_ = lean_ctor_get(v_toApplicative_2894_, 1);
v___f_2897_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
v___x_2898_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref_n(v_parentNames_2892_, 2);
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 3, 2);
lean_closure_set(v___f_2899_, 0, v___x_2898_);
lean_closure_set(v___f_2899_, 1, v_parentNames_2892_);
v___x_2900_ = lean_box(0);
lean_inc_n(v_toPure_2896_, 4);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2901_, 0, v_toPure_2896_);
lean_inc_ref_n(v_inst_2889_, 2);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2902_, 0, v_inst_2889_);
lean_closure_set(v___f_2902_, 1, v_inst_2890_);
lean_closure_set(v___f_2902_, 2, v_toBind_2895_);
lean_closure_set(v___f_2902_, 3, v___f_2901_);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__5), 2, 1);
lean_closure_set(v___f_2903_, 0, v_toPure_2896_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6), 2, 1);
lean_closure_set(v___f_2904_, 0, v_toPure_2896_);
v___x_2905_ = lean_box(v_relaxed_2893_);
v___f_2906_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__14___boxed), 14, 13);
lean_closure_set(v___f_2906_, 0, v___x_2900_);
lean_closure_set(v___f_2906_, 1, v_toPure_2896_);
lean_closure_set(v___f_2906_, 2, v___f_2897_);
lean_closure_set(v___f_2906_, 3, v___x_2905_);
lean_closure_set(v___f_2906_, 4, v___x_2898_);
lean_closure_set(v___f_2906_, 5, v_parentNames_2892_);
lean_closure_set(v___f_2906_, 6, v___f_2899_);
lean_closure_set(v___f_2906_, 7, v_inst_2889_);
lean_closure_set(v___f_2906_, 8, v_toBind_2895_);
lean_closure_set(v___f_2906_, 9, v___f_2903_);
lean_closure_set(v___f_2906_, 10, v_structName_2891_);
lean_closure_set(v___f_2906_, 11, v___f_2904_);
lean_closure_set(v___f_2906_, 12, v___f_2897_);
v_sz_2907_ = lean_array_size(v_parentNames_2892_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2889_, v___f_2902_, v_sz_2907_, v___x_2908_, v_parentNames_2892_);
v___x_2910_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2909_, v___f_2906_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2911_, lean_object* v_toPure_2912_, lean_object* v___f_2913_, lean_object* v_inst_2914_, lean_object* v_inst_2915_, uint8_t v_relaxed_2916_, lean_object* v_toBind_2917_, lean_object* v___f_2918_, lean_object* v_env_2919_){
_start:
{
lean_object* v___x_2920_; 
lean_inc_ref(v_env_2919_);
v___x_2920_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2919_, v_structName_2911_);
if (lean_obj_tag(v___x_2920_) == 1)
{
lean_object* v_val_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref(v_env_2919_);
lean_dec(v___f_2918_);
lean_dec(v_toBind_2917_);
lean_dec_ref(v_inst_2915_);
lean_dec_ref(v_inst_2914_);
lean_dec_ref(v___f_2913_);
lean_dec(v_structName_2911_);
v_val_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_val_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = ((lean_object*)(l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__1));
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v_val_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_apply_2(v_toPure_2912_, lean_box(0), v___x_2923_);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; size_t v_sz_2927_; size_t v___x_2928_; lean_object* v_parentNames_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v___x_2920_);
lean_dec(v_toPure_2912_);
lean_inc(v_structName_2911_);
v___x_2925_ = l_Lean_getStructureParentInfo(v_env_2919_, v_structName_2911_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2927_ = lean_array_size(v___x_2925_);
v___x_2928_ = ((size_t)0ULL);
v_parentNames_2929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2926_, v___f_2913_, v_sz_2927_, v___x_2928_, v___x_2925_);
v___x_2930_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2914_, v_inst_2915_, v_structName_2911_, v_parentNames_2929_, v_relaxed_2916_);
v___x_2931_ = lean_apply_4(v_toBind_2917_, lean_box(0), lean_box(0), v___x_2930_, v___f_2918_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2932_, lean_object* v_toPure_2933_, lean_object* v___f_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_relaxed_2937_, lean_object* v_toBind_2938_, lean_object* v___f_2939_, lean_object* v_env_2940_){
_start:
{
uint8_t v_relaxed_boxed_2941_; lean_object* v_res_2942_; 
v_relaxed_boxed_2941_ = lean_unbox(v_relaxed_2937_);
v_res_2942_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2932_, v_toPure_2933_, v___f_2934_, v_inst_2935_, v_inst_2936_, v_relaxed_boxed_2941_, v_toBind_2938_, v___f_2939_, v_env_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_structName_2945_, uint8_t v_relaxed_2946_){
_start:
{
lean_object* v_toApplicative_2947_; lean_object* v_toBind_2948_; lean_object* v_getEnv_2949_; lean_object* v_toPure_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v___f_2954_; lean_object* v___x_2955_; 
v_toApplicative_2947_ = lean_ctor_get(v_inst_2943_, 0);
v_toBind_2948_ = lean_ctor_get(v_inst_2943_, 1);
lean_inc_n(v_toBind_2948_, 3);
v_getEnv_2949_ = lean_ctor_get(v_inst_2944_, 0);
lean_inc(v_getEnv_2949_);
v_toPure_2950_ = lean_ctor_get(v_toApplicative_2947_, 1);
lean_inc_n(v_toPure_2950_, 2);
v___f_2951_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_structName_2945_);
lean_inc_ref(v_inst_2944_);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2952_, 0, v_toPure_2950_);
lean_closure_set(v___f_2952_, 1, v_inst_2944_);
lean_closure_set(v___f_2952_, 2, v_structName_2945_);
lean_closure_set(v___f_2952_, 3, v_toBind_2948_);
v___x_2953_ = lean_box(v_relaxed_2946_);
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2954_, 0, v_structName_2945_);
lean_closure_set(v___f_2954_, 1, v_toPure_2950_);
lean_closure_set(v___f_2954_, 2, v___f_2951_);
lean_closure_set(v___f_2954_, 3, v_inst_2943_);
lean_closure_set(v___f_2954_, 4, v_inst_2944_);
lean_closure_set(v___f_2954_, 5, v___x_2953_);
lean_closure_set(v___f_2954_, 6, v_toBind_2948_);
lean_closure_set(v___f_2954_, 7, v___f_2952_);
v___x_2955_ = lean_apply_4(v_toBind_2948_, lean_box(0), lean_box(0), v_getEnv_2949_, v___f_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_toBind_2958_, lean_object* v___f_2959_, lean_object* v_parentName_2960_){
_start:
{
uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = 1;
v___x_2962_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2956_, v_inst_2957_, v_parentName_2960_, v___x_2961_);
v___x_2963_ = lean_apply_4(v_toBind_2958_, lean_box(0), lean_box(0), v___x_2962_, v___f_2959_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_structName_2966_, lean_object* v_relaxed_2967_){
_start:
{
uint8_t v_relaxed_boxed_2968_; lean_object* v_res_2969_; 
v_relaxed_boxed_2968_ = lean_unbox(v_relaxed_2967_);
v_res_2969_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2964_, v_inst_2965_, v_structName_2966_, v_relaxed_boxed_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_structName_2972_, lean_object* v_parentNames_2973_, lean_object* v_relaxed_2974_){
_start:
{
uint8_t v_relaxed_boxed_2975_; lean_object* v_res_2976_; 
v_relaxed_boxed_2975_ = lean_unbox(v_relaxed_2974_);
v_res_2976_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2970_, v_inst_2971_, v_structName_2972_, v_parentNames_2973_, v_relaxed_boxed_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2977_, lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_structName_2980_, uint8_t v_relaxed_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2978_, v_inst_2979_, v_structName_2980_, v_relaxed_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_structName_2986_, lean_object* v_relaxed_2987_){
_start:
{
uint8_t v_relaxed_boxed_2988_; lean_object* v_res_2989_; 
v_relaxed_boxed_2988_ = lean_unbox(v_relaxed_2987_);
v_res_2989_ = l_Lean_computeStructureResolutionOrder(v_m_2983_, v_inst_2984_, v_inst_2985_, v_structName_2986_, v_relaxed_boxed_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_structName_2993_, lean_object* v_parentNames_2994_, uint8_t v_relaxed_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2991_, v_inst_2992_, v_structName_2993_, v_parentNames_2994_, v_relaxed_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_structName_3000_, lean_object* v_parentNames_3001_, lean_object* v_relaxed_3002_){
_start:
{
uint8_t v_relaxed_boxed_3003_; lean_object* v_res_3004_; 
v_relaxed_boxed_3003_ = lean_unbox(v_relaxed_3002_);
v_res_3004_ = l_Lean_mergeStructureResolutionOrders(v_m_2997_, v_inst_2998_, v_inst_2999_, v_structName_3000_, v_parentNames_3001_, v_relaxed_boxed_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_3005_){
_start:
{
lean_object* v_resolutionOrder_3006_; 
v_resolutionOrder_3006_ = lean_ctor_get(v_x_3005_, 0);
lean_inc_ref(v_resolutionOrder_3006_);
return v_resolutionOrder_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_3007_);
lean_dec_ref(v_x_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_structName_3012_){
_start:
{
lean_object* v_toApplicative_3013_; lean_object* v_toFunctor_3014_; lean_object* v_map_3015_; lean_object* v___f_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_toApplicative_3013_ = lean_ctor_get(v_inst_3010_, 0);
v_toFunctor_3014_ = lean_ctor_get(v_toApplicative_3013_, 0);
v_map_3015_ = lean_ctor_get(v_toFunctor_3014_, 0);
lean_inc(v_map_3015_);
v___f_3016_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_3017_ = 1;
v___x_3018_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_3010_, v_inst_3011_, v_structName_3012_, v___x_3017_);
v___x_3019_ = lean_apply_4(v_map_3015_, lean_box(0), lean_box(0), v___f_3016_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_structName_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_3021_, v_inst_3022_, v_structName_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_3025_, lean_object* v_structName_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Array_erase___redArg(v___x_3025_, v_x_3027_, v_structName_3026_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_structName_3031_){
_start:
{
lean_object* v_toApplicative_3032_; lean_object* v_toFunctor_3033_; lean_object* v_map_3034_; lean_object* v___x_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_toApplicative_3032_ = lean_ctor_get(v_inst_3029_, 0);
v_toFunctor_3033_ = lean_ctor_get(v_toApplicative_3032_, 0);
v_map_3034_ = lean_ctor_get(v_toFunctor_3033_, 0);
lean_inc(v_map_3034_);
v___x_3035_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_3031_);
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3036_, 0, v___x_3035_);
lean_closure_set(v___f_3036_, 1, v_structName_3031_);
v___x_3037_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_3029_, v_inst_3030_, v_structName_3031_);
v___x_3038_ = lean_apply_4(v_map_3034_, lean_box(0), lean_box(0), v___f_3036_, v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_structName_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_getAllParentStructures___redArg(v_inst_3040_, v_inst_3041_, v_structName_3042_);
return v___x_3043_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
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
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
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
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
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
