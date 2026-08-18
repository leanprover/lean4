// Lean compiler output
// Module: Lean.ReducibilityAttrs
// Imports: public import Lean.ScopedEnvExtension
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedReducibilityStatus_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedReducibilityStatus;
static const lean_string_object l_Lean_instReprReducibilityStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.ReducibilityStatus.reducible"};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__0 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprReducibilityStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__1 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__1_value;
static const lean_string_object l_Lean_instReprReducibilityStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.ReducibilityStatus.semireducible"};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__2 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprReducibilityStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__3 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__3_value;
static const lean_string_object l_Lean_instReprReducibilityStatus_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.ReducibilityStatus.irreducible"};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__4 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprReducibilityStatus_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__5 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__5_value;
static const lean_string_object l_Lean_instReprReducibilityStatus_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.ReducibilityStatus.implicitReducible"};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__6 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprReducibilityStatus_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__7 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__7_value;
static const lean_string_object l_Lean_instReprReducibilityStatus_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.ReducibilityStatus.instanceReducible"};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__8 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprReducibilityStatus_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__8_value)}};
static const lean_object* l_Lean_instReprReducibilityStatus_repr___closed__9 = (const lean_object*)&l_Lean_instReprReducibilityStatus_repr___closed__9_value;
static lean_once_cell_t l_Lean_instReprReducibilityStatus_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprReducibilityStatus_repr___closed__10;
static lean_once_cell_t l_Lean_instReprReducibilityStatus_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprReducibilityStatus_repr___closed__11;
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprReducibilityStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprReducibilityStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprReducibilityStatus___closed__0 = (const lean_object*)&l_Lean_instReprReducibilityStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprReducibilityStatus = (const lean_object*)&l_Lean_instReprReducibilityStatus___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityStatus_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqReducibilityStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqReducibilityStatus_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqReducibilityStatus___closed__0 = (const lean_object*)&l_Lean_instBEqReducibilityStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqReducibilityStatus = (const lean_object*)&l_Lean_instBEqReducibilityStatus___closed__0_value;
static const lean_string_object l_Lean_ReducibilityStatus_toAttrString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[reducible]"};
static const lean_object* l_Lean_ReducibilityStatus_toAttrString___closed__0 = (const lean_object*)&l_Lean_ReducibilityStatus_toAttrString___closed__0_value;
static const lean_string_object l_Lean_ReducibilityStatus_toAttrString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "[semireducible]"};
static const lean_object* l_Lean_ReducibilityStatus_toAttrString___closed__1 = (const lean_object*)&l_Lean_ReducibilityStatus_toAttrString___closed__1_value;
static const lean_string_object l_Lean_ReducibilityStatus_toAttrString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[irreducible]"};
static const lean_object* l_Lean_ReducibilityStatus_toAttrString___closed__2 = (const lean_object*)&l_Lean_ReducibilityStatus_toAttrString___closed__2_value;
static const lean_string_object l_Lean_ReducibilityStatus_toAttrString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "[implicit_reducible]"};
static const lean_object* l_Lean_ReducibilityStatus_toAttrString___closed__3 = (const lean_object*)&l_Lean_ReducibilityStatus_toAttrString___closed__3_value;
static const lean_string_object l_Lean_ReducibilityStatus_toAttrString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "[instance_reducible]"};
static const lean_object* l_Lean_ReducibilityStatus_toAttrString___closed__4 = (const lean_object*)&l_Lean_ReducibilityStatus_toAttrString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "reducibility attribute core extension"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "reducibilityCore"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 201, 42, 208, 53, 44, 245, 169)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityCoreExt;
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reducibilityExtra"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 61, 52, 173, 157, 234, 207, 193)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reducibilityExtraExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_getReducibilityStatusCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getReducibilityStatusCore___closed__0 = (const lean_object*)&l_Lean_getReducibilityStatusCore___closed__0_value;
static const lean_closure_object l_Lean_getReducibilityStatusCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getReducibilityStatusCore___closed__1 = (const lean_object*)&l_Lean_getReducibilityStatusCore___closed__1_value;
static lean_once_cell_t l_Lean_getReducibilityStatusCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getReducibilityStatusCore___closed__2;
LEAN_EXPORT uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatusCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "allowUnsafeReducibility"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 3, 217, 246, 47, 128, 204, 22)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 235, .m_capacity = 235, .m_length = 234, .m_data = "enables users to modify the reducibility settings for declarations even when such changes are deemed potentially hazardous. For example, `simp` and type class resolution maintain term indices where reducible declarations are expanded."};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 158, 85, 56, 211, 107, 118, 9)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_allowUnsafeReducibility;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to set `[semireducible]` for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` because it already is `[semireducible]`"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to set `[reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` is not currently `[semireducible]`, but `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "failed to set `[irreducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "` is not currently `[semireducible]`, `[implicit_reducible]` nor `[instance_reducible]`, but `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set `[implicit_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "` is not currently `[semireducible]` nor `[instance_reducible]`, but `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set `[instance_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "failed to set reducibility status, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "` has not been defined in this file, consider using the `local` modifier"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set `[local reducible]` for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = "`, recall that `[reducible]` affects the term indexing data structures used by `simp` and type class resolution"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to set `[local semireducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` is currently `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, `[irreducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "failed to set `[local irreducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "`, `[semireducible]`, `[implicit_reducible]` nor `[instance_reducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "failed to set `[local implicit_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, `[semireducible]` or `[instance_reducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "failed to set `[local instance_reducible]`, `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`, `[semireducible]` expected"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__42 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__42_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to set reducibility status for `"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__44 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__44_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "`, the `scoped` modifier is not recommended for this kind of attribute"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__46 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__46_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__48 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__48_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Use `set_option allowUnsafeReducibility true` to override reducibility status validation"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1 = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ReducibilityAttrs"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 243, 132, 119, 102, 176, 104, 231)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(136, 6, 121, 201, 161, 138, 59, 119)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 62, 6, 154, 126, 194, 108, 7)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 228, 198, 151, 110, 175, 120, 179)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 11, 210, 221, 39, 72, 148, 16)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 11, 42, 155, 183, 228, 253, 121)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 193, 210, 85, 51, 24, 109, 168)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(562565324) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(13, 53, 165, 236, 93, 163, 7, 1)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 6, 193, 170, 140, 56, 155, 78)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 73, 145, 21, 118, 11, 88, 35)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(155, 100, 92, 11, 143, 96, 227, 175)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "irreducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 207, 43, 193, 214, 202, 115, 95)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "irreducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "reducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "semireducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(82891871) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(118, 199, 147, 168, 131, 34, 217, 154)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 105, 54, 185, 136, 245, 11, 248)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 151, 171, 199, 88, 193, 139, 229)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(20, 89, 104, 119, 191, 122, 184, 229)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implicit_reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 100, 121, 167, 26, 160, 176, 156)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "implicit reducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2104212786) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(22, 126, 215, 185, 112, 104, 250, 112)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 41, 203, 163, 66, 33, 161, 91)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 186, 193, 195, 12, 58, 248, 252)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(52, 224, 28, 233, 79, 131, 248, 111)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instance_reducible"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 180, 213, 185, 56, 77, 23, 14)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "instance reducible declaration"};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))} };
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducibleCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducibleCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
uint8_t v_x_boxed_8_; lean_object* v_res_9_; 
v_x_boxed_8_ = lean_unbox(v_x_7_);
v_res_9_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_boxed_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg(lean_object* v_k_10_){
_start:
{
lean_inc(v_k_10_);
return v_k_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ReducibilityStatus_ctorElim___redArg(v_k_11_);
lean_dec(v_k_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, uint8_t v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_inc(v_k_17_);
return v_k_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
uint8_t v_t_boxed_23_; lean_object* v_res_24_; 
v_t_boxed_23_ = lean_unbox(v_t_20_);
v_res_24_ = l_Lean_ReducibilityStatus_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_boxed_23_, v_h_21_, v_k_22_);
lean_dec(v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg(lean_object* v_reducible_25_){
_start:
{
lean_inc(v_reducible_25_);
return v_reducible_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(lean_object* v_reducible_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_ReducibilityStatus_reducible_elim___redArg(v_reducible_26_);
lean_dec(v_reducible_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim(lean_object* v_motive_28_, uint8_t v_t_29_, lean_object* v_h_30_, lean_object* v_reducible_31_){
_start:
{
lean_inc(v_reducible_31_);
return v_reducible_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_reducible_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_reducible_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_ReducibilityStatus_reducible_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_reducible_35_);
lean_dec(v_reducible_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg(lean_object* v_semireducible_38_){
_start:
{
lean_inc(v_semireducible_38_);
return v_semireducible_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(lean_object* v_semireducible_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_ReducibilityStatus_semireducible_elim___redArg(v_semireducible_39_);
lean_dec(v_semireducible_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_semireducible_44_){
_start:
{
lean_inc(v_semireducible_44_);
return v_semireducible_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_semireducible_elim___boxed(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_semireducible_48_){
_start:
{
uint8_t v_t_boxed_49_; lean_object* v_res_50_; 
v_t_boxed_49_ = lean_unbox(v_t_46_);
v_res_50_ = l_Lean_ReducibilityStatus_semireducible_elim(v_motive_45_, v_t_boxed_49_, v_h_47_, v_semireducible_48_);
lean_dec(v_semireducible_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg(lean_object* v_irreducible_51_){
_start:
{
lean_inc(v_irreducible_51_);
return v_irreducible_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(lean_object* v_irreducible_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_ReducibilityStatus_irreducible_elim___redArg(v_irreducible_52_);
lean_dec(v_irreducible_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim(lean_object* v_motive_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_irreducible_57_){
_start:
{
lean_inc(v_irreducible_57_);
return v_irreducible_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_irreducible_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_irreducible_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l_Lean_ReducibilityStatus_irreducible_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_irreducible_61_);
lean_dec(v_irreducible_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(lean_object* v_implicitReducible_64_){
_start:
{
lean_inc(v_implicitReducible_64_);
return v_implicitReducible_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(lean_object* v_implicitReducible_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(v_implicitReducible_65_);
lean_dec(v_implicitReducible_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_implicitReducible_70_){
_start:
{
lean_inc(v_implicitReducible_70_);
return v_implicitReducible_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_implicitReducible_74_){
_start:
{
uint8_t v_t_boxed_75_; lean_object* v_res_76_; 
v_t_boxed_75_ = lean_unbox(v_t_72_);
v_res_76_ = l_Lean_ReducibilityStatus_implicitReducible_elim(v_motive_71_, v_t_boxed_75_, v_h_73_, v_implicitReducible_74_);
lean_dec(v_implicitReducible_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg(lean_object* v_instanceReducible_77_){
_start:
{
lean_inc(v_instanceReducible_77_);
return v_instanceReducible_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___redArg___boxed(lean_object* v_instanceReducible_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_ReducibilityStatus_instanceReducible_elim___redArg(v_instanceReducible_78_);
lean_dec(v_instanceReducible_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim(lean_object* v_motive_80_, uint8_t v_t_81_, lean_object* v_h_82_, lean_object* v_instanceReducible_83_){
_start:
{
lean_inc(v_instanceReducible_83_);
return v_instanceReducible_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_instanceReducible_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_instanceReducible_87_){
_start:
{
uint8_t v_t_boxed_88_; lean_object* v_res_89_; 
v_t_boxed_88_ = lean_unbox(v_t_85_);
v_res_89_ = l_Lean_ReducibilityStatus_instanceReducible_elim(v_motive_84_, v_t_boxed_88_, v_h_86_, v_instanceReducible_87_);
lean_dec(v_instanceReducible_87_);
return v_res_89_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus_default(void){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
static uint8_t _init_l_Lean_instInhabitedReducibilityStatus(void){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__10(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(2u);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_instReprReducibilityStatus_repr___closed__11(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr(uint8_t v_x_111_, lean_object* v_prec_112_){
_start:
{
lean_object* v___y_114_; lean_object* v___y_121_; lean_object* v___y_128_; lean_object* v___y_135_; lean_object* v___y_142_; 
switch(v_x_111_)
{
case 0:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1024u);
v___x_149_ = lean_nat_dec_le(v___x_148_, v_prec_112_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_114_ = v___x_150_;
goto v___jp_113_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_114_ = v___x_151_;
goto v___jp_113_;
}
}
case 1:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_112_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_121_ = v___x_154_;
goto v___jp_120_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_121_ = v___x_155_;
goto v___jp_120_;
}
}
case 2:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = lean_nat_dec_le(v___x_156_, v_prec_112_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_128_ = v___x_158_;
goto v___jp_127_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_128_ = v___x_159_;
goto v___jp_127_;
}
}
case 3:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1024u);
v___x_161_ = lean_nat_dec_le(v___x_160_, v_prec_112_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_135_ = v___x_162_;
goto v___jp_134_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_135_ = v___x_163_;
goto v___jp_134_;
}
}
default: 
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1024u);
v___x_165_ = lean_nat_dec_le(v___x_164_, v_prec_112_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__10, &l_Lean_instReprReducibilityStatus_repr___closed__10_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__10);
v___y_142_ = v___x_166_;
goto v___jp_141_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_instReprReducibilityStatus_repr___closed__11, &l_Lean_instReprReducibilityStatus_repr___closed__11_once, _init_l_Lean_instReprReducibilityStatus_repr___closed__11);
v___y_142_ = v___x_167_;
goto v___jp_141_;
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__1));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_112_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__3));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_112_);
return v___x_126_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__5));
lean_inc(v___y_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = l_Repr_addAppParen(v___x_132_, v_prec_112_);
return v___x_133_;
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__7));
lean_inc(v___y_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___y_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_112_);
return v___x_140_;
}
v___jp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Lean_instReprReducibilityStatus_repr___closed__9));
lean_inc(v___y_142_);
v___x_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_144_, 0, v___y_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_112_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprReducibilityStatus_repr___boxed(lean_object* v_x_168_, lean_object* v_prec_169_){
_start:
{
uint8_t v_x_289__boxed_170_; lean_object* v_res_171_; 
v_x_289__boxed_170_ = lean_unbox(v_x_168_);
v_res_171_ = l_Lean_instReprReducibilityStatus_repr(v_x_289__boxed_170_, v_prec_169_);
lean_dec(v_prec_169_);
return v_res_171_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t v_x_174_, uint8_t v_y_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_174_);
v___x_177_ = l_Lean_ReducibilityStatus_ctorIdx(v_y_175_);
v___x_178_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
lean_dec(v___x_177_);
lean_dec(v___x_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityStatus_beq___boxed(lean_object* v_x_179_, lean_object* v_y_180_){
_start:
{
uint8_t v_x_17__boxed_181_; uint8_t v_y_18__boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_x_17__boxed_181_ = lean_unbox(v_x_179_);
v_y_18__boxed_182_ = lean_unbox(v_y_180_);
v_res_183_ = l_Lean_instBEqReducibilityStatus_beq(v_x_17__boxed_181_, v_y_18__boxed_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString(uint8_t v_x_192_){
_start:
{
switch(v_x_192_)
{
case 0:
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__0));
return v___x_193_;
}
case 1:
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__1));
return v___x_194_;
}
case 2:
{
lean_object* v___x_195_; 
v___x_195_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__2));
return v___x_195_;
}
case 3:
{
lean_object* v___x_196_; 
v___x_196_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__3));
return v___x_196_;
}
default: 
{
lean_object* v___x_197_; 
v___x_197_ = ((lean_object*)(l_Lean_ReducibilityStatus_toAttrString___closed__4));
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityStatus_toAttrString___boxed(lean_object* v_x_198_){
_start:
{
uint8_t v_x_49__boxed_199_; lean_object* v_res_200_; 
v_x_49__boxed_199_ = lean_unbox(v_x_198_);
v_res_200_ = l_Lean_ReducibilityStatus_toAttrString(v_x_49__boxed_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_s_201_, lean_object* v_p_202_){
_start:
{
lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v___x_205_; 
v_fst_203_ = lean_ctor_get(v_p_202_, 0);
lean_inc(v_fst_203_);
v_snd_204_ = lean_ctor_get(v_p_202_, 1);
lean_inc(v_snd_204_);
lean_dec_ref(v_p_202_);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_203_, v_snd_204_, v_s_201_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_k_208_; lean_object* v_v_209_; lean_object* v_l_210_; lean_object* v_r_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_k_208_ = lean_ctor_get(v_x_207_, 1);
v_v_209_ = lean_ctor_get(v_x_207_, 2);
v_l_210_ = lean_ctor_get(v_x_207_, 3);
v_r_211_ = lean_ctor_get(v_x_207_, 4);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_206_, v_l_210_);
lean_inc(v_v_209_);
lean_inc(v_k_208_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_k_208_);
lean_ctor_set(v___x_213_, 1, v_v_209_);
v___x_214_ = lean_array_push(v___x_212_, v___x_213_);
v_init_206_ = v___x_214_;
v_x_207_ = v_r_211_;
goto _start;
}
else
{
return v_init_206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_216_, v_x_217_);
lean_dec(v_x_217_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v_fst_221_; lean_object* v_fst_222_; uint8_t v___x_223_; 
v_fst_221_ = lean_ctor_get(v_a_219_, 0);
v_fst_222_ = lean_ctor_get(v_b_220_, 0);
v___x_223_ = l_Lean_Name_quickLt(v_fst_221_, v_fst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_224_, v_b_225_);
lean_dec_ref(v_b_225_);
lean_dec_ref(v_a_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_228_, lean_object* v_pivot_229_, lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_k_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_nat_dec_lt(v_k_232_, v_hi_228_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_k_232_);
v___x_234_ = lean_array_fswap(v_as_230_, v_i_231_, v_hi_228_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_i_231_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_fst_238_; uint8_t v___x_239_; 
v___x_236_ = lean_array_fget_borrowed(v_as_230_, v_k_232_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
v_fst_238_ = lean_ctor_get(v_pivot_229_, 0);
v___x_239_ = l_Lean_Name_quickLt(v_fst_237_, v_fst_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_k_232_, v___x_240_);
lean_dec(v_k_232_);
v_k_232_ = v___x_241_;
goto _start;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_array_fswap(v_as_230_, v_i_231_, v_k_232_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_i_231_, v___x_244_);
lean_dec(v_i_231_);
v___x_246_ = lean_nat_add(v_k_232_, v___x_244_);
lean_dec(v_k_232_);
v_as_230_ = v___x_243_;
v_i_231_ = v___x_245_;
v_k_232_ = v___x_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_248_, lean_object* v_pivot_249_, lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_248_, v_pivot_249_, v_as_250_, v_i_251_, v_k_252_);
lean_dec_ref(v_pivot_249_);
lean_dec(v_hi_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_254_, lean_object* v_as_255_, lean_object* v_lo_256_, lean_object* v_hi_257_){
_start:
{
lean_object* v___y_259_; uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_lt(v_lo_256_, v_hi_257_);
if (v___x_269_ == 0)
{
lean_dec(v_lo_256_);
return v_as_255_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_mid_272_; lean_object* v___y_274_; lean_object* v___y_280_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_270_ = lean_nat_add(v_lo_256_, v_hi_257_);
v___x_271_ = lean_unsigned_to_nat(1u);
v_mid_272_ = lean_nat_shiftr(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___x_285_ = lean_array_fget_borrowed(v_as_255_, v_mid_272_);
v___x_286_ = lean_array_fget_borrowed(v_as_255_, v_lo_256_);
v___x_287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_280_ = v_as_255_;
goto v___jp_279_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_array_fswap(v_as_255_, v_lo_256_, v_mid_272_);
v___y_280_ = v___x_288_;
goto v___jp_279_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = lean_array_fget_borrowed(v___y_274_, v_mid_272_);
v___x_276_ = lean_array_fget_borrowed(v___y_274_, v_hi_257_);
v___x_277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_dec(v_mid_272_);
v___y_259_ = v___y_274_;
goto v___jp_258_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_array_fswap(v___y_274_, v_mid_272_, v_hi_257_);
lean_dec(v_mid_272_);
v___y_259_ = v___x_278_;
goto v___jp_258_;
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_array_fget_borrowed(v___y_280_, v_hi_257_);
v___x_282_ = lean_array_fget_borrowed(v___y_280_, v_lo_256_);
v___x_283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
v___y_274_ = v___y_280_;
goto v___jp_273_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_fswap(v___y_280_, v_lo_256_, v_hi_257_);
v___y_274_ = v___x_284_;
goto v___jp_273_;
}
}
}
v___jp_258_:
{
lean_object* v_pivot_260_; lean_object* v___x_261_; lean_object* v_fst_262_; lean_object* v_snd_263_; uint8_t v___x_264_; 
v_pivot_260_ = lean_array_fget(v___y_259_, v_hi_257_);
lean_inc_n(v_lo_256_, 2);
v___x_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_257_, v_pivot_260_, v___y_259_, v_lo_256_, v_lo_256_);
lean_dec(v_pivot_260_);
v_fst_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc(v_snd_263_);
lean_dec_ref(v___x_261_);
v___x_264_ = lean_nat_dec_le(v_hi_257_, v_fst_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_254_, v_snd_263_, v_lo_256_, v_fst_262_);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_fst_262_, v___x_266_);
lean_dec(v_fst_262_);
v_as_255_ = v___x_265_;
v_lo_256_ = v___x_267_;
goto _start;
}
else
{
lean_dec(v_fst_262_);
lean_dec(v_lo_256_);
return v_snd_263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_289_, lean_object* v_as_290_, lean_object* v_lo_291_, lean_object* v_hi_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_289_, v_as_290_, v_lo_291_, v_hi_292_);
lean_dec(v_hi_292_);
lean_dec(v_n_289_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_x_296_, lean_object* v_s_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_r_300_; lean_object* v___x_301_; lean_object* v___y_303_; lean_object* v___y_304_; uint8_t v___x_307_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v_r_300_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_299_, v_s_297_);
v___x_301_ = lean_array_get_size(v_r_300_);
v___x_307_ = lean_nat_dec_eq(v___x_301_, v___x_298_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___y_311_; uint8_t v___x_313_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_sub(v___x_301_, v___x_308_);
v___x_313_ = lean_nat_dec_le(v___x_298_, v___x_309_);
if (v___x_313_ == 0)
{
lean_inc(v___x_309_);
v___y_311_ = v___x_309_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___x_298_;
goto v___jp_310_;
}
v___jp_310_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_le(v___y_311_, v___x_309_);
if (v___x_312_ == 0)
{
lean_dec(v___x_309_);
lean_inc(v___y_311_);
v___y_303_ = v___y_311_;
v___y_304_ = v___y_311_;
goto v___jp_302_;
}
else
{
v___y_303_ = v___y_311_;
v___y_304_ = v___x_309_;
goto v___jp_302_;
}
}
}
else
{
lean_object* v___x_314_; 
lean_inc_ref_n(v_r_300_, 2);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v_r_300_);
lean_ctor_set(v___x_314_, 1, v_r_300_);
lean_ctor_set(v___x_314_, 2, v_r_300_);
return v___x_314_;
}
v___jp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_301_, v_r_300_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_inc_ref_n(v___x_305_, 2);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_ctor_set(v___x_306_, 2, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_x_315_, lean_object* v_s_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_x_315_, v_s_316_);
lean_dec(v_s_316_);
lean_dec_ref(v_x_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_s_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___y_333_; 
v___x_331_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
if (lean_obj_tag(v_s_330_) == 0)
{
lean_object* v_size_337_; 
v_size_337_ = lean_ctor_get(v_s_330_, 0);
lean_inc(v_size_337_);
lean_dec_ref_known(v_s_330_, 5);
v___y_333_ = v_size_337_;
goto v___jp_332_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___y_333_ = v___x_338_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_Nat_reprFast(v___y_333_);
v___x_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_331_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(lean_object* v_newState_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
return v_x_340_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v___x_344_; 
v_head_342_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_head_342_);
v_tail_343_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_tail_343_);
lean_dec_ref_known(v_x_341_, 2);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_339_, v_head_342_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_346_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_342_, v_val_345_, v_x_340_);
v_x_340_ = v___x_346_;
v_x_341_ = v_tail_343_;
goto _start;
}
else
{
lean_dec(v___x_344_);
lean_dec(v_head_342_);
v_x_341_ = v_tail_343_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2___boxed(lean_object* v_newState_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_349_, v_x_350_, v_x_351_);
lean_dec(v_newState_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___oldState_353_, lean_object* v_newState_354_, lean_object* v_newItems_355_, lean_object* v_otherState_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_354_, v_otherState_356_, v_newItems_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___oldState_358_, lean_object* v_newState_359_, lean_object* v_newItems_360_, lean_object* v_otherState_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___oldState_358_, v_newState_359_, v_newItems_360_, v_otherState_361_);
lean_dec(v_newState_359_);
lean_dec(v___oldState_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v_m_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_r_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v_r_366_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_365_, v_m_363_);
v___x_367_ = lean_array_get_size(v_r_366_);
v___x_368_ = lean_nat_dec_eq(v___x_367_, v___x_364_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___y_372_; uint8_t v___x_376_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_sub(v___x_367_, v___x_369_);
v___x_376_ = lean_nat_dec_le(v___x_364_, v___x_370_);
if (v___x_376_ == 0)
{
lean_inc(v___x_370_);
v___y_372_ = v___x_370_;
goto v___jp_371_;
}
else
{
v___y_372_ = v___x_364_;
goto v___jp_371_;
}
v___jp_371_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_le(v___y_372_, v___x_370_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v___x_370_);
lean_inc(v___y_372_);
v___x_374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_367_, v_r_366_, v___y_372_, v___y_372_);
lean_dec(v___y_372_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_367_, v_r_366_, v___y_372_, v___x_370_);
lean_dec(v___x_370_);
return v___x_375_;
}
}
}
else
{
return v_r_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_m_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_m_377_);
lean_dec(v_m_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___x_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___x_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(lean_object* v___x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_385_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v___x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_390_, v_x_391_, v_x_392_);
lean_dec_ref(v_x_392_);
lean_dec_ref(v_x_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_));
v___x_425_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(lean_object* v_init_428_, lean_object* v_t_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_428_, v_t_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_431_, lean_object* v_t_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(v_init_431_, v_t_432_);
lean_dec(v_t_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(lean_object* v_n_434_, lean_object* v_as_435_, lean_object* v_lo_436_, lean_object* v_hi_437_, lean_object* v_w_438_, lean_object* v_hlo_439_, lean_object* v_hhi_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_434_, v_as_435_, v_lo_436_, v_hi_437_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_442_, lean_object* v_as_443_, lean_object* v_lo_444_, lean_object* v_hi_445_, lean_object* v_w_446_, lean_object* v_hlo_447_, lean_object* v_hhi_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(v_n_442_, v_as_443_, v_lo_444_, v_hi_445_, v_w_446_, v_hlo_447_, v_hhi_448_);
lean_dec(v_hi_445_);
lean_dec(v_n_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_450_, lean_object* v_lo_451_, lean_object* v_hi_452_, lean_object* v_hhi_453_, lean_object* v_pivot_454_, lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_k_457_, lean_object* v_ilo_458_, lean_object* v_ik_459_, lean_object* v_w_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_452_, v_pivot_454_, v_as_455_, v_i_456_, v_k_457_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_462_, lean_object* v_lo_463_, lean_object* v_hi_464_, lean_object* v_hhi_465_, lean_object* v_pivot_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_k_469_, lean_object* v_ilo_470_, lean_object* v_ik_471_, lean_object* v_w_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(v_n_462_, v_lo_463_, v_hi_464_, v_hhi_465_, v_pivot_466_, v_as_467_, v_i_468_, v_k_469_, v_ilo_470_, v_ik_471_, v_w_472_);
lean_dec_ref(v_pivot_466_);
lean_dec(v_hi_464_);
lean_dec(v_lo_463_);
lean_dec(v_n_462_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_474_){
_start:
{
uint8_t v_stage_u2081_475_; 
v_stage_u2081_475_ = lean_ctor_get_uint8(v_m_474_, sizeof(void*)*2);
if (v_stage_u2081_475_ == 0)
{
return v_m_474_;
}
else
{
lean_object* v_map_u2081_476_; lean_object* v_map_u2082_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_map_u2081_476_ = lean_ctor_get(v_m_474_, 0);
v_map_u2082_477_ = lean_ctor_get(v_m_474_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_m_474_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v_m_474_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_map_u2082_477_);
lean_inc(v_map_u2081_476_);
lean_dec(v_m_474_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; lean_object* v___x_483_; 
v___x_481_ = 0;
if (v_isShared_480_ == 0)
{
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_map_u2081_476_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_map_u2082_477_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*2, v___x_481_);
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_486_, lean_object* v_m_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(v_m_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object* v_x_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_a_490_);
lean_inc_ref_n(v___x_491_, 2);
v___x_492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object* v_x_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(v_x_493_, v_a_494_);
lean_dec_ref(v_x_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_ks_500_; lean_object* v_vs_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_525_; 
v_ks_500_ = lean_ctor_get(v_x_496_, 0);
v_vs_501_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_525_ == 0)
{
v___x_503_ = v_x_496_;
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_vs_501_);
lean_inc(v_ks_500_);
lean_dec(v_x_496_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_get_size(v_ks_500_);
v___x_506_ = lean_nat_dec_lt(v_x_497_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_x_497_);
v___x_507_ = lean_array_push(v_ks_500_, v_x_498_);
v___x_508_ = lean_array_push(v_vs_501_, v_x_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_k_x27_512_; uint8_t v___x_513_; 
v_k_x27_512_ = lean_array_fget_borrowed(v_ks_500_, v_x_497_);
v___x_513_ = lean_name_eq(v_x_498_, v_k_x27_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_515_; 
if (v_isShared_504_ == 0)
{
v___x_515_ = v___x_503_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_ks_500_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_vs_501_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_x_497_, v___x_516_);
lean_dec(v_x_497_);
v_x_496_ = v___x_515_;
v_x_497_ = v___x_517_;
goto _start;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_array_fset(v_ks_500_, v_x_497_, v_x_498_);
v___x_521_ = lean_array_fset(v_vs_501_, v_x_497_, v_x_499_);
lean_dec(v_x_497_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_521_);
lean_ctor_set(v___x_503_, 0, v___x_520_);
v___x_523_ = v___x_503_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_n_526_, lean_object* v_k_527_, lean_object* v_v_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_n_526_, v___x_529_, v_k_527_, v_v_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_532_, size_t v_x_533_, size_t v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_es_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v_j_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_es_537_ = lean_ctor_get(v_x_532_, 0);
v___x_538_ = ((size_t)31ULL);
v___x_539_ = lean_usize_land(v_x_533_, v___x_538_);
v_j_540_ = lean_usize_to_nat(v___x_539_);
v___x_541_ = lean_array_get_size(v_es_537_);
v___x_542_ = lean_nat_dec_lt(v_j_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_j_540_);
lean_dec(v_x_536_);
lean_dec(v_x_535_);
return v_x_532_;
}
else
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_537_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_532_, 0);
lean_dec(v_unused_582_);
v___x_544_ = v_x_532_;
v_isShared_545_ = v_isSharedCheck_581_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_x_532_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_581_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_v_546_; lean_object* v___x_547_; lean_object* v_xs_x27_548_; lean_object* v___y_550_; 
v_v_546_ = lean_array_fget(v_es_537_, v_j_540_);
v___x_547_ = lean_box(0);
v_xs_x27_548_ = lean_array_fset(v_es_537_, v_j_540_, v___x_547_);
switch(lean_obj_tag(v_v_546_))
{
case 0:
{
lean_object* v_key_555_; lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_key_555_ = lean_ctor_get(v_v_546_, 0);
v_val_556_ = lean_ctor_get(v_v_546_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_v_546_);
if (v_isSharedCheck_566_ == 0)
{
v___x_558_ = v_v_546_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_inc(v_key_555_);
lean_dec(v_v_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint8_t v___x_560_; 
v___x_560_ = lean_name_eq(v_x_535_, v_key_555_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_558_);
v___x_561_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_555_, v_val_556_, v_x_535_, v_x_536_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___y_550_ = v___x_562_;
goto v___jp_549_;
}
else
{
lean_object* v___x_564_; 
lean_dec(v_val_556_);
lean_dec(v_key_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_x_536_);
lean_ctor_set(v___x_558_, 0, v_x_535_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_x_535_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_x_536_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_550_ = v___x_564_;
goto v___jp_549_;
}
}
}
}
case 1:
{
lean_object* v_node_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v_node_567_ = lean_ctor_get(v_v_546_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_546_);
if (v_isSharedCheck_579_ == 0)
{
v___x_569_ = v_v_546_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_node_567_);
lean_dec(v_v_546_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_571_ = ((size_t)5ULL);
v___x_572_ = lean_usize_shift_right(v_x_533_, v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_x_534_, v___x_573_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_node_567_, v___x_572_, v___x_574_, v_x_535_, v_x_536_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_575_);
v___x_577_ = v___x_569_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_550_ = v___x_577_;
goto v___jp_549_;
}
}
}
default: 
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_535_);
lean_ctor_set(v___x_580_, 1, v_x_536_);
v___y_550_ = v___x_580_;
goto v___jp_549_;
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_array_fset(v_xs_x27_548_, v_j_540_, v___y_550_);
lean_dec(v_j_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_551_);
v___x_553_ = v___x_544_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_ks_583_ = lean_ctor_get(v_x_532_, 0);
v_vs_584_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v_x_532_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_532_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_ks_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_vs_584_);
v___x_589_ = v_reuseFailAlloc_603_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v_newNode_590_; uint8_t v___y_592_; size_t v___x_598_; uint8_t v___x_599_; 
v_newNode_590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5___redArg(v___x_589_, v_x_535_, v_x_536_);
v___x_598_ = ((size_t)7ULL);
v___x_599_ = lean_usize_dec_le(v___x_598_, v_x_534_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_590_);
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_599_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_ks_593_ = lean_ctor_get(v_newNode_590_, 0);
lean_inc_ref(v_ks_593_);
v_vs_594_ = lean_ctor_get(v_newNode_590_, 1);
lean_inc_ref(v_vs_594_);
lean_dec_ref(v_newNode_590_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0);
v___x_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_534_, v_ks_593_, v_vs_594_, v___x_595_, v___x_596_);
lean_dec_ref(v_vs_594_);
lean_dec_ref(v_ks_593_);
return v___x_597_;
}
else
{
return v_newNode_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(size_t v_depth_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_i_608_, lean_object* v_entries_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v_entries_609_;
}
else
{
lean_object* v_k_612_; lean_object* v_v_613_; uint64_t v___y_615_; 
v_k_612_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v_v_613_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
if (lean_obj_tag(v_k_612_) == 0)
{
uint64_t v___x_626_; 
v___x_626_ = 1723ULL;
v___y_615_ = v___x_626_;
goto v___jp_614_;
}
else
{
uint64_t v_hash_627_; 
v_hash_627_ = lean_ctor_get_uint64(v_k_612_, sizeof(void*)*2);
v___y_615_ = v_hash_627_;
goto v___jp_614_;
}
v___jp_614_:
{
size_t v_h_616_; size_t v___x_617_; lean_object* v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v_h_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_h_616_ = lean_uint64_to_usize(v___y_615_);
v___x_617_ = ((size_t)5ULL);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_sub(v_depth_605_, v___x_619_);
v___x_621_ = lean_usize_mul(v___x_617_, v___x_620_);
v_h_622_ = lean_usize_shift_right(v_h_616_, v___x_621_);
v___x_623_ = lean_nat_add(v_i_608_, v___x_618_);
lean_dec(v_i_608_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
v___x_624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_entries_609_, v_h_622_, v_depth_605_, v_k_612_, v_v_613_);
v_i_608_ = v___x_623_;
v_entries_609_ = v___x_624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_depth_628_, lean_object* v_keys_629_, lean_object* v_vals_630_, lean_object* v_i_631_, lean_object* v_entries_632_){
_start:
{
size_t v_depth_boxed_633_; lean_object* v_res_634_; 
v_depth_boxed_633_ = lean_unbox_usize(v_depth_628_);
lean_dec(v_depth_628_);
v_res_634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_depth_boxed_633_, v_keys_629_, v_vals_630_, v_i_631_, v_entries_632_);
lean_dec_ref(v_vals_630_);
lean_dec_ref(v_keys_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_1178__boxed_640_; size_t v_x_1179__boxed_641_; lean_object* v_res_642_; 
v_x_1178__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_x_1179__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_635_, v_x_1178__boxed_640_, v_x_1179__boxed_641_, v_x_638_, v_x_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint64_t v___y_647_; 
if (lean_obj_tag(v_x_644_) == 0)
{
uint64_t v___x_651_; 
v___x_651_ = 1723ULL;
v___y_647_ = v___x_651_;
goto v___jp_646_;
}
else
{
uint64_t v_hash_652_; 
v_hash_652_ = lean_ctor_get_uint64(v_x_644_, sizeof(void*)*2);
v___y_647_ = v_hash_652_;
goto v___jp_646_;
}
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_uint64_to_usize(v___y_647_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_643_, v___x_648_, v___x_649_, v_x_644_, v_x_645_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(lean_object* v_m_653_, lean_object* v_query_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_zero_658_; uint8_t v_isZero_659_; 
v_zero_658_ = lean_unsigned_to_nat(0u);
v_isZero_659_ = lean_nat_dec_eq(v_x_656_, v_zero_658_);
if (v_isZero_659_ == 1)
{
lean_dec(v_x_657_);
lean_dec(v_x_656_);
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_box(2);
return v___x_660_;
}
else
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_val_661_ = lean_ctor_get(v_x_655_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v_x_655_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_x_655_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_val_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_keyArray_669_; lean_object* v_valueArray_670_; lean_object* v___x_671_; uint8_t v_isSome_672_; 
v_keyArray_669_ = lean_ctor_get(v_m_653_, 1);
v_valueArray_670_ = lean_ctor_get(v_m_653_, 2);
v___x_671_ = lean_array_fget_borrowed(v_keyArray_669_, v_x_657_);
v_isSome_672_ = lean_noption_is_some(v___x_671_);
if (v_isSome_672_ == 0)
{
lean_dec(v_x_656_);
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v_x_657_);
return v___x_673_;
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_x_657_);
v_val_674_ = lean_ctor_get(v_x_655_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v_x_655_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v_x_655_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_one_682_; lean_object* v_n_683_; lean_object* v___y_685_; 
v_one_682_ = lean_unsigned_to_nat(1u);
v_n_683_ = lean_nat_sub(v_x_656_, v_one_682_);
lean_dec(v_x_656_);
if (v_isSome_672_ == 0)
{
goto v___jp_691_;
}
else
{
lean_object* v___x_693_; uint8_t v_isSome_694_; 
v___x_693_ = lean_array_fget_borrowed(v_valueArray_670_, v_x_657_);
v_isSome_694_ = lean_noption_is_some(v___x_693_);
if (v_isSome_694_ == 0)
{
goto v___jp_691_;
}
else
{
lean_object* v_val_695_; uint8_t v___x_696_; 
lean_inc(v___x_671_);
v_val_695_ = lean_noption_get(v___x_671_);
v___x_696_ = lean_name_eq(v_val_695_, v_query_654_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
lean_dec(v_val_695_);
v___x_697_ = lean_array_get_size(v_keyArray_669_);
v___x_698_ = lean_nat_add(v_x_657_, v_one_682_);
lean_dec(v_x_657_);
v___x_699_ = lean_nat_dec_lt(v___x_698_, v___x_697_);
if (v___x_699_ == 0)
{
lean_dec(v___x_698_);
v_x_656_ = v_n_683_;
v_x_657_ = v_zero_658_;
goto _start;
}
else
{
v_x_656_ = v_n_683_;
v_x_657_ = v___x_698_;
goto _start;
}
}
else
{
lean_object* v_val_702_; lean_object* v___x_703_; 
lean_dec(v_n_683_);
lean_dec(v_x_655_);
lean_inc(v___x_693_);
v_val_702_ = lean_noption_get(v___x_693_);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v_x_657_);
lean_ctor_set(v___x_703_, 1, v_val_695_);
lean_ctor_set(v___x_703_, 2, v_val_702_);
return v___x_703_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_array_get_size(v_keyArray_669_);
v___x_687_ = lean_nat_add(v_x_657_, v_one_682_);
lean_dec(v_x_657_);
v___x_688_ = lean_nat_dec_lt(v___x_687_, v___x_686_);
if (v___x_688_ == 0)
{
lean_dec(v___x_687_);
v_x_655_ = v___y_685_;
v_x_656_ = v_n_683_;
v_x_657_ = v_zero_658_;
goto _start;
}
else
{
v_x_655_ = v___y_685_;
v_x_656_ = v_n_683_;
v_x_657_ = v___x_687_;
goto _start;
}
}
v___jp_691_:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v___x_692_; 
lean_inc(v_x_657_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_x_657_);
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
v___y_685_ = v_x_655_;
goto v___jp_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_704_, lean_object* v_query_705_, lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_m_704_, v_query_705_, v_x_706_, v_x_707_, v_x_708_);
lean_dec(v_query_705_);
lean_dec_ref(v_m_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_m_710_, lean_object* v_query_711_){
_start:
{
lean_object* v_keyArray_712_; lean_object* v___x_713_; uint64_t v___y_715_; 
v_keyArray_712_ = lean_ctor_get(v_m_710_, 1);
v___x_713_ = lean_array_get_size(v_keyArray_712_);
if (lean_obj_tag(v_query_711_) == 0)
{
uint64_t v___x_730_; 
v___x_730_ = 1723ULL;
v___y_715_ = v___x_730_;
goto v___jp_714_;
}
else
{
uint64_t v_hash_731_; 
v_hash_731_ = lean_ctor_get_uint64(v_query_711_, sizeof(void*)*2);
v___y_715_ = v_hash_731_;
goto v___jp_714_;
}
v___jp_714_:
{
uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v_fold_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_716_ = 32ULL;
v___x_717_ = lean_uint64_shift_right(v___y_715_, v___x_716_);
v_fold_718_ = lean_uint64_xor(v___y_715_, v___x_717_);
v___x_719_ = 16ULL;
v___x_720_ = lean_uint64_shift_right(v_fold_718_, v___x_719_);
v___x_721_ = lean_uint64_xor(v_fold_718_, v___x_720_);
v___x_722_ = lean_uint64_to_usize(v___x_721_);
v___x_723_ = lean_usize_of_nat(v___x_713_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_sub(v___x_723_, v___x_724_);
v___x_726_ = lean_usize_land(v___x_722_, v___x_725_);
v___x_727_ = lean_usize_to_nat(v___x_726_);
v___x_728_ = lean_box(0);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_m_710_, v_query_711_, v___x_728_, v___x_713_, v___x_727_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object* v_m_732_, lean_object* v_query_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_m_732_, v_query_733_);
lean_dec(v_query_733_);
lean_dec_ref(v_m_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_b_735_, lean_object* v_acc_736_, lean_object* v_i_737_){
_start:
{
lean_object* v___y_739_; lean_object* v_keyArray_747_; lean_object* v_valueArray_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_keyArray_747_ = lean_ctor_get(v_b_735_, 1);
v_valueArray_748_ = lean_ctor_get(v_b_735_, 2);
v___x_749_ = lean_array_get_size(v_keyArray_747_);
v___x_750_ = lean_nat_dec_lt(v_i_737_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v_i_737_);
return v_acc_736_;
}
else
{
lean_object* v___x_751_; uint8_t v_isSome_752_; 
v___x_751_ = lean_array_fget_borrowed(v_keyArray_747_, v_i_737_);
v_isSome_752_ = lean_noption_is_some(v___x_751_);
if (v_isSome_752_ == 0)
{
goto v___jp_743_;
}
else
{
lean_object* v___x_753_; uint8_t v_isSome_754_; 
v___x_753_ = lean_array_fget_borrowed(v_valueArray_748_, v_i_737_);
v_isSome_754_ = lean_noption_is_some(v___x_753_);
if (v_isSome_754_ == 0)
{
goto v___jp_743_;
}
else
{
lean_object* v_val_755_; lean_object* v_val_756_; lean_object* v_i_758_; lean_object* v___x_763_; 
lean_inc(v___x_751_);
v_val_755_ = lean_noption_get(v___x_751_);
lean_inc(v___x_753_);
v_val_756_ = lean_noption_get(v___x_753_);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_acc_736_, v_val_755_);
switch(lean_obj_tag(v___x_763_))
{
case 0:
{
lean_object* v_index_764_; lean_object* v_size_765_; lean_object* v___x_766_; 
v_index_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_index_764_);
lean_dec_ref_known(v___x_763_, 3);
v_size_765_ = lean_ctor_get(v_acc_736_, 0);
lean_inc(v_size_765_);
v___x_766_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_736_, v_size_765_, v_index_764_, v_val_755_, v_val_756_);
lean_dec(v_index_764_);
v___y_739_ = v___x_766_;
goto v___jp_738_;
}
case 1:
{
lean_object* v_index_767_; 
v_index_767_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_index_767_);
lean_dec_ref_known(v___x_763_, 1);
v_i_758_ = v_index_767_;
goto v___jp_757_;
}
default: 
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_736_, v___x_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_index_770_; 
v_index_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_index_770_);
lean_dec_ref_known(v___x_769_, 1);
v_i_758_ = v_index_770_;
goto v___jp_757_;
}
else
{
lean_dec(v_val_756_);
lean_dec(v_val_755_);
v___y_739_ = v_acc_736_;
goto v___jp_738_;
}
}
}
v___jp_757_:
{
lean_object* v_size_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_size_759_ = lean_ctor_get(v_acc_736_, 0);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_size_759_, v___x_760_);
v___x_762_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_736_, v___x_761_, v_i_758_, v_val_755_, v_val_756_);
lean_dec(v_i_758_);
v___y_739_ = v___x_762_;
goto v___jp_738_;
}
}
}
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_i_737_, v___x_740_);
lean_dec(v_i_737_);
v_acc_736_ = v___y_739_;
v_i_737_ = v___x_741_;
goto _start;
}
v___jp_743_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_i_737_, v___x_744_);
lean_dec(v_i_737_);
v_i_737_ = v___x_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_b_771_, lean_object* v_acc_772_, lean_object* v_i_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg(v_b_771_, v_acc_772_, v_i_773_);
lean_dec_ref(v_b_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(lean_object* v_init_775_, lean_object* v_b_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg(v_b_776_, v_init_775_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_init_779_, lean_object* v_b_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_init_779_, v_b_780_);
lean_dec_ref(v_b_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(lean_object* v_m_782_){
_start:
{
lean_object* v_keyArray_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_cellCount_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_target_790_; lean_object* v___x_791_; 
v_keyArray_783_ = lean_ctor_get(v_m_782_, 1);
v___x_784_ = lean_array_get_size(v_keyArray_783_);
v___x_785_ = lean_unsigned_to_nat(2u);
v_cellCount_786_ = lean_nat_mul(v___x_784_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_786_);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_786_);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_786_);
v_target_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_790_, 0, v___x_787_);
lean_ctor_set(v_target_790_, 1, v___x_788_);
lean_ctor_set(v_target_790_, 2, v___x_789_);
v___x_791_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_target_790_, v_m_782_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(lean_object* v_m_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_792_);
lean_dec_ref(v_m_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
uint8_t v_stage_u2081_797_; lean_object* v_map_u2081_798_; lean_object* v_map_u2082_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_879_; 
v_stage_u2081_797_ = lean_ctor_get_uint8(v_x_794_, sizeof(void*)*2);
v_map_u2081_798_ = lean_ctor_get(v_x_794_, 0);
v_map_u2082_799_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_879_ == 0)
{
v___x_801_ = v_x_794_;
v_isShared_802_ = v_isSharedCheck_879_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_map_u2082_799_);
lean_inc(v_map_u2081_798_);
lean_dec(v_x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_879_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___y_804_; lean_object* v_i_805_; lean_object* v___y_814_; lean_object* v___y_826_; lean_object* v_i_827_; 
if (v_stage_u2081_797_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_801_);
v___x_845_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_u2082_799_, v_x_795_, v_x_796_);
v___x_846_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_846_, 0, v_map_u2081_798_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_map_u2081_798_, v_x_795_);
switch(lean_obj_tag(v___x_847_))
{
case 0:
{
lean_object* v_index_848_; lean_object* v_size_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_801_);
v_index_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_index_848_);
lean_dec_ref_known(v___x_847_, 3);
v_size_849_ = lean_ctor_get(v_map_u2081_798_, 0);
lean_inc(v_size_849_);
v___x_850_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_798_, v_size_849_, v_index_848_, v_x_795_, v_x_796_);
lean_dec(v_index_848_);
v___x_851_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_851_;
}
case 1:
{
lean_object* v_index_852_; lean_object* v_size_853_; lean_object* v_keyArray_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
lean_del_object(v___x_801_);
v_index_852_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_index_852_);
lean_dec_ref_known(v___x_847_, 1);
v_size_853_ = lean_ctor_get(v_map_u2081_798_, 0);
v_keyArray_854_ = lean_ctor_get(v_map_u2081_798_, 1);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_add(v_size_853_, v___x_855_);
v___x_857_ = lean_array_get_size(v_keyArray_854_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec(v___x_856_);
lean_dec(v_index_852_);
goto v___jp_833_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_859_ = lean_unsigned_to_nat(4u);
v___x_860_ = lean_nat_mul(v___x_856_, v___x_859_);
v___x_861_ = lean_unsigned_to_nat(3u);
v___x_862_ = lean_nat_mul(v___x_857_, v___x_861_);
v___x_863_ = lean_nat_dec_le(v___x_860_, v___x_862_);
lean_dec(v___x_862_);
lean_dec(v___x_860_);
if (v___x_863_ == 0)
{
lean_dec(v___x_856_);
lean_dec(v_index_852_);
goto v___jp_833_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_798_, v___x_856_, v_index_852_, v_x_795_, v_x_796_);
lean_dec(v_index_852_);
v___x_865_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_865_;
}
}
}
default: 
{
lean_object* v_size_866_; lean_object* v_keyArray_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_size_866_ = lean_ctor_get(v_map_u2081_798_, 0);
v_keyArray_867_ = lean_ctor_get(v_map_u2081_798_, 1);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_size_866_, v___x_868_);
v___x_870_ = lean_array_get_size(v_keyArray_867_);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v___x_869_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_map_u2081_798_);
lean_dec_ref(v_map_u2081_798_);
v___y_814_ = v___x_872_;
goto v___jp_813_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_873_ = lean_unsigned_to_nat(4u);
v___x_874_ = lean_nat_mul(v___x_869_, v___x_873_);
lean_dec(v___x_869_);
v___x_875_ = lean_unsigned_to_nat(3u);
v___x_876_ = lean_nat_mul(v___x_870_, v___x_875_);
v___x_877_ = lean_nat_dec_le(v___x_874_, v___x_876_);
lean_dec(v___x_876_);
lean_dec(v___x_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_map_u2081_798_);
lean_dec_ref(v_map_u2081_798_);
v___y_814_ = v___x_878_;
goto v___jp_813_;
}
else
{
v___y_814_ = v_map_u2081_798_;
goto v___jp_813_;
}
}
}
}
}
v___jp_803_:
{
lean_object* v_size_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_size_806_ = lean_ctor_get(v___y_804_, 0);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_size_806_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_804_, v___x_808_, v_i_805_, v_x_795_, v_x_796_);
lean_dec(v_i_805_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_809_);
v___x_811_ = v___x_801_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*2, v_stage_u2081_797_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
v___jp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v___y_814_, v_x_795_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_index_816_; lean_object* v_size_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_del_object(v___x_801_);
v_index_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_index_816_);
lean_dec_ref_known(v___x_815_, 3);
v_size_817_ = lean_ctor_get(v___y_814_, 0);
lean_inc(v_size_817_);
v___x_818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_814_, v_size_817_, v_index_816_, v_x_795_, v_x_796_);
lean_dec(v_index_816_);
v___x_819_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_819_;
}
case 1:
{
lean_object* v_index_820_; 
v_index_820_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_index_820_);
lean_dec_ref_known(v___x_815_, 1);
v___y_804_ = v___y_814_;
v_i_805_ = v_index_820_;
goto v___jp_803_;
}
default: 
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_814_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_index_823_; 
v_index_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_index_823_);
lean_dec_ref_known(v___x_822_, 1);
v___y_804_ = v___y_814_;
v_i_805_ = v_index_823_;
goto v___jp_803_;
}
else
{
lean_object* v___x_824_; 
lean_del_object(v___x_801_);
lean_dec(v_x_796_);
lean_dec(v_x_795_);
v___x_824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_824_, 0, v___y_814_);
lean_ctor_set(v___x_824_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_824_;
}
}
}
}
v___jp_825_:
{
lean_object* v_size_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_size_828_ = lean_ctor_get(v___y_826_, 0);
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_nat_add(v_size_828_, v___x_829_);
v___x_831_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_826_, v___x_830_, v_i_827_, v_x_795_, v_x_796_);
lean_dec(v_i_827_);
v___x_832_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_832_;
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_map_u2081_798_);
lean_dec_ref(v_map_u2081_798_);
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v___x_834_, v_x_795_);
switch(lean_obj_tag(v___x_835_))
{
case 0:
{
lean_object* v_index_836_; lean_object* v_size_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_index_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_836_);
lean_dec_ref_known(v___x_835_, 3);
v_size_837_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_size_837_);
v___x_838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_834_, v_size_837_, v_index_836_, v_x_795_, v_x_796_);
lean_dec(v_index_836_);
v___x_839_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_839_;
}
case 1:
{
lean_object* v_index_840_; 
v_index_840_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_840_);
lean_dec_ref_known(v___x_835_, 1);
v___y_826_ = v___x_834_;
v_i_827_ = v_index_840_;
goto v___jp_825_;
}
default: 
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_834_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_index_843_; 
v_index_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_index_843_);
lean_dec_ref_known(v___x_842_, 1);
v___y_826_ = v___x_834_;
v_i_827_ = v_index_843_;
goto v___jp_825_;
}
else
{
lean_object* v___x_844_; 
lean_dec(v_x_796_);
lean_dec(v_x_795_);
v___x_844_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_844_, 0, v___x_834_);
lean_ctor_set(v___x_844_, 1, v_map_u2082_799_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*2, v_stage_u2081_797_);
return v___x_844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(lean_object* v_d_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_884_; 
v_fst_882_ = lean_ctor_get(v_x_881_, 0);
lean_inc(v_fst_882_);
v_snd_883_ = lean_ctor_get(v_x_881_, 1);
lean_inc(v_snd_883_);
lean_dec_ref(v_x_881_);
v___x_884_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_d_880_, v_fst_882_, v_snd_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_891_; lean_object* v___x_892_; 
v_cellCount_891_ = lean_unsigned_to_nat(16u);
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_893_; lean_object* v___x_894_; 
v_cellCount_893_ = lean_unsigned_to_nat(16u);
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_893_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_895_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_896_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
lean_ctor_set(v___x_898_, 2, v___x_895_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_903_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_904_ = 1;
v___x_905_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_902_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*2, v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___f_906_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___f_907_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_908_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___f_909_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_910_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_));
v___x_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___f_909_);
lean_ctor_set(v___x_911_, 2, v___x_908_);
lean_ctor_set(v___x_911_, 3, v___f_907_);
lean_ctor_set(v___x_911_, 4, v___f_906_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
v___x_914_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_x_918_, v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_00_u03b2_922_, lean_object* v_m_923_, lean_object* v_query_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_m_923_, v_query_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_00_u03b2_926_, lean_object* v_m_927_, lean_object* v_query_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(v_00_u03b2_926_, v_m_927_, v_query_928_);
lean_dec(v_query_928_);
lean_dec_ref(v_m_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_931_, v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_00_u03b2_935_, lean_object* v_m_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_00_u03b2_938_, lean_object* v_m_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b2_938_, v_m_939_);
lean_dec_ref(v_m_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_query_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_m_942_, v_query_943_, v_x_944_, v_x_945_, v_x_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_949_, lean_object* v_m_950_, lean_object* v_query_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_949_, v_m_950_, v_query_951_, v_x_952_, v_x_953_, v_x_954_, v_x_955_);
lean_dec(v_query_951_);
lean_dec_ref(v_m_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, size_t v_x_959_, size_t v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_958_, v_x_959_, v_x_960_, v_x_961_, v_x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
size_t v_x_1818__boxed_970_; size_t v_x_1819__boxed_971_; lean_object* v_res_972_; 
v_x_1818__boxed_970_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_x_1819__boxed_971_ = lean_unbox_usize(v_x_967_);
lean_dec(v_x_967_);
v_res_972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_964_, v_x_965_, v_x_1818__boxed_970_, v_x_1819__boxed_971_, v_x_968_, v_x_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6(lean_object* v_00_u03b2_973_, lean_object* v_init_974_, lean_object* v_b_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_init_974_, v_b_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_977_, lean_object* v_init_978_, lean_object* v_b_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6(v_00_u03b2_977_, v_init_978_, v_b_979_);
lean_dec_ref(v_b_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_981_, lean_object* v_n_982_, lean_object* v_k_983_, lean_object* v_v_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5___redArg(v_n_982_, v_k_983_, v_v_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_986_, size_t v_depth_987_, lean_object* v_keys_988_, lean_object* v_vals_989_, lean_object* v_heq_990_, lean_object* v_i_991_, lean_object* v_entries_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_depth_987_, v_keys_988_, v_vals_989_, v_i_991_, v_entries_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_994_, lean_object* v_depth_995_, lean_object* v_keys_996_, lean_object* v_vals_997_, lean_object* v_heq_998_, lean_object* v_i_999_, lean_object* v_entries_1000_){
_start:
{
size_t v_depth_boxed_1001_; lean_object* v_res_1002_; 
v_depth_boxed_1001_ = lean_unbox_usize(v_depth_995_);
lean_dec(v_depth_995_);
v_res_1002_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_994_, v_depth_boxed_1001_, v_keys_996_, v_vals_997_, v_heq_998_, v_i_999_, v_entries_1000_);
lean_dec_ref(v_vals_997_);
lean_dec_ref(v_keys_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1003_, lean_object* v_b_1004_, lean_object* v_acc_1005_, lean_object* v_i_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___redArg(v_b_1004_, v_acc_1005_, v_i_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_b_1009_, lean_object* v_acc_1010_, lean_object* v_i_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__3_spec__6_spec__9(v_00_u03b2_1008_, v_b_1009_, v_acc_1010_, v_i_1011_);
lean_dec_ref(v_b_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(lean_object* v_as_1019_, lean_object* v_k_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_m_1025_; lean_object* v_a_1026_; uint8_t v___x_1027_; 
v___x_1023_ = lean_nat_add(v_x_1021_, v_x_1022_);
v___x_1024_ = lean_unsigned_to_nat(1u);
v_m_1025_ = lean_nat_shiftr(v___x_1023_, v___x_1024_);
lean_dec(v___x_1023_);
v_a_1026_ = lean_array_fget_borrowed(v_as_1019_, v_m_1025_);
v___x_1027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_1026_, v_k_1020_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
lean_dec(v_x_1022_);
v___x_1028_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_1020_, v_a_1026_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec(v_m_1025_);
lean_dec(v_x_1021_);
lean_inc(v_a_1026_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1026_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_nat_dec_eq(v_m_1025_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_nat_sub(v_m_1025_, v___x_1024_);
lean_dec(v_m_1025_);
v___x_1033_ = lean_nat_dec_lt(v___x_1032_, v_x_1021_);
if (v___x_1033_ == 0)
{
v_x_1022_ = v___x_1032_;
goto _start;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v___x_1032_);
lean_dec(v_x_1021_);
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_m_1025_);
lean_dec(v_x_1021_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
lean_dec(v_x_1021_);
v___x_1037_ = lean_nat_add(v_m_1025_, v___x_1024_);
lean_dec(v_m_1025_);
v___x_1038_ = lean_nat_dec_le(v___x_1037_, v_x_1022_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec(v___x_1037_);
lean_dec(v_x_1022_);
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
else
{
v_x_1021_ = v___x_1037_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg___boxed(lean_object* v_as_1041_, lean_object* v_k_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v_as_1041_, v_k_1042_, v_x_1043_, v_x_1044_);
lean_dec_ref(v_k_1042_);
lean_dec_ref(v_as_1041_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1046_, lean_object* v_vals_1047_, lean_object* v_i_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_keys_1046_);
v___x_1051_ = lean_nat_dec_lt(v_i_1048_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_i_1048_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v_k_x27_1053_; uint8_t v___x_1054_; 
v_k_x27_1053_ = lean_array_fget_borrowed(v_keys_1046_, v_i_1048_);
v___x_1054_ = lean_name_eq(v_k_1049_, v_k_x27_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_i_1048_, v___x_1055_);
lean_dec(v_i_1048_);
v_i_1048_ = v___x_1056_;
goto _start;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_array_fget_borrowed(v_vals_1047_, v_i_1048_);
lean_dec(v_i_1048_);
lean_inc(v___x_1058_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1060_, lean_object* v_vals_1061_, lean_object* v_i_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1060_, v_vals_1061_, v_i_1062_, v_k_1063_);
lean_dec(v_k_1063_);
lean_dec_ref(v_vals_1061_);
lean_dec_ref(v_keys_1060_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v_es_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_j_1072_; lean_object* v___x_1073_; 
v_es_1068_ = lean_ctor_get(v_x_1065_, 0);
v___x_1069_ = lean_box(2);
v___x_1070_ = ((size_t)31ULL);
v___x_1071_ = lean_usize_land(v_x_1066_, v___x_1070_);
v_j_1072_ = lean_usize_to_nat(v___x_1071_);
v___x_1073_ = lean_array_get_borrowed(v___x_1069_, v_es_1068_, v_j_1072_);
lean_dec(v_j_1072_);
switch(lean_obj_tag(v___x_1073_))
{
case 0:
{
lean_object* v_key_1074_; lean_object* v_val_1075_; uint8_t v___x_1076_; 
v_key_1074_ = lean_ctor_get(v___x_1073_, 0);
v_val_1075_ = lean_ctor_get(v___x_1073_, 1);
v___x_1076_ = lean_name_eq(v_x_1067_, v_key_1074_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(0);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
lean_inc(v_val_1075_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_val_1075_);
return v___x_1078_;
}
}
case 1:
{
lean_object* v_node_1079_; size_t v___x_1080_; size_t v___x_1081_; 
v_node_1079_ = lean_ctor_get(v___x_1073_, 0);
v___x_1080_ = ((size_t)5ULL);
v___x_1081_ = lean_usize_shift_right(v_x_1066_, v___x_1080_);
v_x_1065_ = v_node_1079_;
v_x_1066_ = v___x_1081_;
goto _start;
}
default: 
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_box(0);
return v___x_1083_;
}
}
}
else
{
lean_object* v_ks_1084_; lean_object* v_vs_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_ks_1084_ = lean_ctor_get(v_x_1065_, 0);
v_vs_1085_ = lean_ctor_get(v_x_1065_, 1);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1084_, v_vs_1085_, v___x_1086_, v_x_1067_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
size_t v_x_582__boxed_1091_; lean_object* v_res_1092_; 
v_x_582__boxed_1091_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_res_1092_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1088_, v_x_582__boxed_1091_, v_x_1090_);
lean_dec(v_x_1090_);
lean_dec_ref(v_x_1088_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
uint64_t v___y_1096_; 
if (lean_obj_tag(v_x_1094_) == 0)
{
uint64_t v___x_1099_; 
v___x_1099_ = 1723ULL;
v___y_1096_ = v___x_1099_;
goto v___jp_1095_;
}
else
{
uint64_t v_hash_1100_; 
v_hash_1100_ = lean_ctor_get_uint64(v_x_1094_, sizeof(void*)*2);
v___y_1096_ = v_hash_1100_;
goto v___jp_1095_;
}
v___jp_1095_:
{
size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_uint64_to_usize(v___y_1096_);
v___x_1098_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1093_, v___x_1097_, v_x_1094_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_1101_, v_x_1102_);
lean_dec(v_x_1102_);
lean_dec_ref(v_x_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(lean_object* v_m_1104_, lean_object* v_query_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_m_1104_, v_query_1105_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_index_1107_; lean_object* v_key_1108_; lean_object* v_value_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_index_1107_ = lean_ctor_get(v___x_1106_, 0);
v_key_1108_ = lean_ctor_get(v___x_1106_, 1);
v_value_1109_ = lean_ctor_get(v___x_1106_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1106_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_value_1109_);
lean_inc(v_key_1108_);
lean_inc(v_index_1107_);
lean_dec(v___x_1106_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_index_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_key_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_value_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___x_1106_);
v___x_1117_ = lean_box(1);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_1118_, lean_object* v_query_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_m_1118_, v_query_1119_);
lean_dec(v_query_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_m_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_value_1124_; lean_object* v___x_1125_; 
v_value_1124_ = lean_ctor_get(v___x_1123_, 2);
lean_inc(v_value_1124_);
lean_dec_ref_known(v___x_1123_, 3);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_value_1124_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(lean_object* v_m_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_m_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
uint8_t v_stage_u2081_1132_; 
v_stage_u2081_1132_ = lean_ctor_get_uint8(v_x_1130_, sizeof(void*)*2);
if (v_stage_u2081_1132_ == 0)
{
lean_object* v_map_u2081_1133_; lean_object* v_map_u2082_1134_; lean_object* v___x_1135_; 
v_map_u2081_1133_ = lean_ctor_get(v_x_1130_, 0);
v_map_u2082_1134_ = lean_ctor_get(v_x_1130_, 1);
v___x_1135_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_map_u2082_1134_, v_x_1131_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_1133_, v_x_1131_);
return v___x_1136_;
}
else
{
return v___x_1135_;
}
}
else
{
lean_object* v_map_u2081_1137_; lean_object* v___x_1138_; 
v_map_u2081_1137_ = lean_ctor_get(v_x_1130_, 0);
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_1137_, v_x_1131_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_1139_, v_x_1140_);
lean_dec(v_x_1140_);
lean_dec_ref(v_x_1139_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_getReducibilityStatusCore___closed__2(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((lean_object*)(l_Lean_getReducibilityStatusCore___closed__1));
v___x_1145_ = ((lean_object*)(l_Lean_getReducibilityStatusCore___closed__0));
v___x_1146_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT uint8_t l_Lean_getReducibilityStatusCore(lean_object* v_env_1147_, lean_object* v_declName_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v_ext_1150_; lean_object* v_toEnvExtension_1151_; lean_object* v_asyncMode_1152_; lean_object* v___x_1153_; lean_object* v_m_1154_; lean_object* v___x_1155_; 
v___x_1149_ = l_Lean_reducibilityExtraExt;
v_ext_1150_ = lean_ctor_get(v___x_1149_, 1);
v_toEnvExtension_1151_ = lean_ctor_get(v_ext_1150_, 0);
v_asyncMode_1152_ = lean_ctor_get(v_toEnvExtension_1151_, 2);
v___x_1153_ = lean_obj_once(&l_Lean_getReducibilityStatusCore___closed__2, &l_Lean_getReducibilityStatusCore___closed__2_once, _init_l_Lean_getReducibilityStatusCore___closed__2);
lean_inc_ref(v_env_1147_);
v_m_1154_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1153_, v___x_1149_, v_env_1147_, v_asyncMode_1152_);
v___x_1155_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_m_1154_, v_declName_1148_);
lean_dec(v_m_1154_);
if (lean_obj_tag(v___x_1155_) == 1)
{
lean_object* v_val_1156_; uint8_t v___x_1157_; 
lean_dec(v_declName_1148_);
lean_dec_ref(v_env_1147_);
v_val_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = lean_unbox(v_val_1156_);
lean_dec(v_val_1156_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(1);
v___x_1159_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1147_, v_declName_1148_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v_toEnvExtension_1161_; lean_object* v_asyncMode_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_1161_ = lean_ctor_get(v___x_1160_, 0);
v_asyncMode_1162_ = lean_ctor_get(v_toEnvExtension_1161_, 2);
lean_inc(v_declName_1148_);
v___x_1163_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1158_, v___x_1160_, v_env_1147_, v_asyncMode_1162_, v_declName_1148_);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1163_, v_declName_1148_);
lean_dec(v_declName_1148_);
lean_dec(v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
return v___x_1165_;
}
else
{
lean_object* v_val_1166_; uint8_t v___x_1167_; 
v_val_1166_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1167_ = lean_unbox(v_val_1166_);
lean_dec(v_val_1166_);
return v___x_1167_;
}
}
else
{
lean_object* v_val_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_val_1168_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1169_ = l_Lean_reducibilityCoreExt;
v___x_1170_ = 0;
v___x_1171_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1158_, v___x_1169_, v_env_1147_, v_val_1168_, v___x_1170_);
lean_dec(v_val_1168_);
lean_dec_ref(v_env_1147_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_array_get_size(v___x_1171_);
v___x_1174_ = lean_nat_dec_lt(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; 
lean_dec_ref(v___x_1171_);
lean_dec(v_declName_1148_);
v___x_1175_ = 1;
return v___x_1175_;
}
else
{
uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1176_ = 1;
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_sub(v___x_1173_, v___x_1177_);
v___x_1179_ = lean_nat_dec_le(v___x_1172_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec(v___x_1178_);
lean_dec_ref(v___x_1171_);
lean_dec(v_declName_1148_);
return v___x_1176_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_box(v___x_1176_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_declName_1148_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v___x_1171_, v___x_1181_, v___x_1172_, v___x_1178_);
lean_dec_ref_known(v___x_1181_, 2);
lean_dec_ref(v___x_1171_);
if (lean_obj_tag(v___x_1182_) == 0)
{
return v___x_1176_;
}
else
{
lean_object* v_val_1183_; lean_object* v_snd_1184_; uint8_t v___x_1185_; 
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_snd_1184_ = lean_ctor_get(v_val_1183_, 1);
lean_inc(v_snd_1184_);
lean_dec(v_val_1183_);
v___x_1185_ = lean_unbox(v_snd_1184_);
lean_dec(v_snd_1184_);
return v___x_1185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatusCore___boxed(lean_object* v_env_1186_, lean_object* v_declName_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Lean_getReducibilityStatusCore(v_env_1186_, v_declName_1187_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(lean_object* v_00_u03b2_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(v_x_1191_, v_x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(lean_object* v_00_u03b2_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(v_00_u03b2_1194_, v_x_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec_ref(v_x_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(lean_object* v_as_1198_, lean_object* v_k_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v_as_1198_, v_k_1199_, v_x_1200_, v_x_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___boxed(lean_object* v_as_1204_, lean_object* v_k_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(v_as_1204_, v_k_1205_, v_x_1206_, v_x_1207_, v_x_1208_);
lean_dec_ref(v_k_1205_);
lean_dec_ref(v_as_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(lean_object* v_00_u03b2_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_1211_, v_x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(v_00_u03b2_1214_, v_x_1215_, v_x_1216_);
lean_dec(v_x_1216_);
lean_dec_ref(v_x_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(lean_object* v_00_u03b2_1218_, lean_object* v_m_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_1219_, v_a_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(v_00_u03b2_1222_, v_m_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_m_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1226_, lean_object* v_x_1227_, size_t v_x_1228_, lean_object* v_x_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_1227_, v_x_1228_, v_x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
size_t v_x_807__boxed_1235_; lean_object* v_res_1236_; 
v_x_807__boxed_1235_ = lean_unbox_usize(v_x_1233_);
lean_dec(v_x_1233_);
v_res_1236_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(v_00_u03b2_1231_, v_x_1232_, v_x_807__boxed_1235_, v_x_1234_);
lean_dec(v_x_1234_);
lean_dec_ref(v_x_1232_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1237_, lean_object* v_m_1238_, lean_object* v_query_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_m_1238_, v_query_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_query_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(v_00_u03b2_1241_, v_m_1242_, v_query_1243_);
lean_dec(v_query_1243_);
lean_dec_ref(v_m_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1245_, lean_object* v_keys_1246_, lean_object* v_vals_1247_, lean_object* v_heq_1248_, lean_object* v_i_1249_, lean_object* v_k_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1246_, v_vals_1247_, v_i_1249_, v_k_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_keys_1253_, lean_object* v_vals_1254_, lean_object* v_heq_1255_, lean_object* v_i_1256_, lean_object* v_k_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1252_, v_keys_1253_, v_vals_1254_, v_heq_1255_, v_i_1256_, v_k_1257_);
lean_dec(v_k_1257_);
lean_dec_ref(v_vals_1254_);
lean_dec_ref(v_keys_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object* v_env_1259_, lean_object* v_declName_1260_, uint8_t v_status_1261_, uint8_t v_attrKind_1262_, lean_object* v_currNamespace_1263_){
_start:
{
if (v_attrKind_1262_ == 0)
{
lean_object* v___x_1264_; 
lean_dec(v_currNamespace_1263_);
v___x_1264_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1259_, v_declName_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; lean_object* v_toEnvExtension_1266_; lean_object* v_asyncMode_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1265_ = l_Lean_reducibilityCoreExt;
v_toEnvExtension_1266_ = lean_ctor_get(v___x_1265_, 0);
v_asyncMode_1267_ = lean_ctor_get(v_toEnvExtension_1266_, 2);
v___x_1268_ = lean_box(v_status_1261_);
lean_inc(v_declName_1260_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_declName_1260_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1265_, v_env_1259_, v___x_1269_, v_asyncMode_1267_, v_declName_1260_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref_known(v___x_1264_, 1);
v___x_1271_ = l_Lean_reducibilityExtraExt;
v___x_1272_ = lean_box(v_status_1261_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_declName_1260_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_1271_, v_env_1259_, v___x_1273_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = l_Lean_reducibilityExtraExt;
v___x_1276_ = lean_box(v_status_1261_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_declName_1260_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1259_, v___x_1275_, v___x_1277_, v_attrKind_1262_, v_currNamespace_1263_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(lean_object* v_env_1279_, lean_object* v_declName_1280_, lean_object* v_status_1281_, lean_object* v_attrKind_1282_, lean_object* v_currNamespace_1283_){
_start:
{
uint8_t v_status_boxed_1284_; uint8_t v_attrKind_boxed_1285_; lean_object* v_res_1286_; 
v_status_boxed_1284_ = lean_unbox(v_status_1281_);
v_attrKind_boxed_1285_ = lean_unbox(v_attrKind_1282_);
v_res_1286_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1279_, v_declName_1280_, v_status_boxed_1284_, v_attrKind_boxed_1285_, v_currNamespace_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(lean_object* v_name_1287_, lean_object* v_decl_1288_, lean_object* v_ref_1289_){
_start:
{
lean_object* v_defValue_1291_; lean_object* v_descr_1292_; lean_object* v_deprecation_x3f_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_defValue_1291_ = lean_ctor_get(v_decl_1288_, 0);
v_descr_1292_ = lean_ctor_get(v_decl_1288_, 1);
v_deprecation_x3f_1293_ = lean_ctor_get(v_decl_1288_, 2);
v___x_1294_ = lean_alloc_ctor(1, 0, 1);
v___x_1295_ = lean_unbox(v_defValue_1291_);
lean_ctor_set_uint8(v___x_1294_, 0, v___x_1295_);
lean_inc(v_deprecation_x3f_1293_);
lean_inc_ref(v_descr_1292_);
lean_inc_n(v_name_1287_, 2);
v___x_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1296_, 0, v_name_1287_);
lean_ctor_set(v___x_1296_, 1, v_ref_1289_);
lean_ctor_set(v___x_1296_, 2, v___x_1294_);
lean_ctor_set(v___x_1296_, 3, v_descr_1292_);
lean_ctor_set(v___x_1296_, 4, v_deprecation_x3f_1293_);
v___x_1297_ = lean_register_option(v_name_1287_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1306_);
v___x_1299_ = v___x_1297_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1297_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_inc(v_defValue_1291_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_name_1287_);
lean_ctor_set(v___x_1301_, 1, v_defValue_1291_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_name_1287_);
v_a_1307_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1297_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1297_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1315_, lean_object* v_decl_1316_, lean_object* v_ref_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v_name_1315_, v_decl_1316_, v_ref_1317_);
lean_dec_ref(v_decl_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1335_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1336_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_));
v___x_1337_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v___x_1334_, v___x_1335_, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
return v_res_1339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(lean_object* v_opts_1340_, lean_object* v_opt_1341_){
_start:
{
lean_object* v_name_1342_; lean_object* v_defValue_1343_; lean_object* v_map_1344_; lean_object* v___x_1345_; 
v_name_1342_ = lean_ctor_get(v_opt_1341_, 0);
v_defValue_1343_ = lean_ctor_get(v_opt_1341_, 1);
v_map_1344_ = lean_ctor_get(v_opts_1340_, 0);
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1344_, v_name_1342_);
if (lean_obj_tag(v___x_1345_) == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_unbox(v_defValue_1343_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; 
v_val_1347_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v___x_1345_, 1);
if (lean_obj_tag(v_val_1347_) == 1)
{
uint8_t v_v_1348_; 
v_v_1348_ = lean_ctor_get_uint8(v_val_1347_, 0);
lean_dec_ref_known(v_val_1347_, 0);
return v_v_1348_;
}
else
{
uint8_t v___x_1349_; 
lean_dec(v_val_1347_);
v___x_1349_ = lean_unbox(v_defValue_1343_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(lean_object* v_opts_1350_, lean_object* v_opt_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_opts_1350_, v_opt_1351_);
lean_dec_ref(v_opt_1351_);
lean_dec_ref(v_opts_1350_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
lean_ctor_set(v___x_1359_, 4, v___x_1357_);
lean_ctor_set(v___x_1359_, 5, v___x_1357_);
lean_ctor_set(v___x_1359_, 6, v___x_1357_);
lean_ctor_set(v___x_1359_, 7, v___x_1357_);
lean_ctor_set(v___x_1359_, 8, v___x_1357_);
lean_ctor_set(v___x_1359_, 9, v___x_1357_);
lean_ctor_set(v___x_1359_, 10, v___x_1357_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_unsigned_to_nat(32u);
v___x_1361_ = lean_mk_empty_array_with_capacity(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1363_ = ((size_t)5ULL);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_unsigned_to_nat(32u);
v___x_1366_ = lean_mk_empty_array_with_capacity(v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3);
v___x_1368_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1366_);
lean_ctor_set(v___x_1368_, 2, v___x_1364_);
lean_ctor_set(v___x_1368_, 3, v___x_1364_);
lean_ctor_set_usize(v___x_1368_, 4, v___x_1363_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1369_ = lean_box(1);
v___x_1370_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
v___x_1371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
v___x_1372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___x_1370_);
lean_ctor_set(v___x_1372_, 2, v___x_1369_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(lean_object* v_msgData_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_env_1378_; lean_object* v_options_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1377_ = lean_st_ref_get(v___y_1375_);
v_env_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_env_1378_);
lean_dec(v___x_1377_);
v_options_1379_ = lean_ctor_get(v___y_1374_, 2);
v___x_1380_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
v___x_1381_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_1379_);
v___x_1382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1382_, 0, v_env_1378_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
lean_ctor_set(v___x_1382_, 3, v_options_1379_);
v___x_1383_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_msgData_1373_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(lean_object* v_msgData_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msgData_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_ref_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_ref_1394_ = lean_ctor_get(v___y_1391_, 5);
v___x_1395_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msg_1390_, v___y_1391_, v___y_1392_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_inc(v_ref_1394_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_ref_1394_);
lean_ctor_set(v___x_1400_, 1, v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 1);
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg___boxed(lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_fileName_1415_; lean_object* v_fileMap_1416_; lean_object* v_options_1417_; lean_object* v_currRecDepth_1418_; lean_object* v_maxRecDepth_1419_; lean_object* v_ref_1420_; lean_object* v_currNamespace_1421_; lean_object* v_openDecls_1422_; lean_object* v_initHeartbeats_1423_; lean_object* v_maxHeartbeats_1424_; lean_object* v_quotContext_1425_; lean_object* v_currMacroScope_1426_; uint8_t v_diag_1427_; lean_object* v_cancelTk_x3f_1428_; uint8_t v_suppressElabErrors_1429_; lean_object* v_inheritedTraceOptions_1430_; lean_object* v_ref_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_fileName_1415_ = lean_ctor_get(v___y_1412_, 0);
v_fileMap_1416_ = lean_ctor_get(v___y_1412_, 1);
v_options_1417_ = lean_ctor_get(v___y_1412_, 2);
v_currRecDepth_1418_ = lean_ctor_get(v___y_1412_, 3);
v_maxRecDepth_1419_ = lean_ctor_get(v___y_1412_, 4);
v_ref_1420_ = lean_ctor_get(v___y_1412_, 5);
v_currNamespace_1421_ = lean_ctor_get(v___y_1412_, 6);
v_openDecls_1422_ = lean_ctor_get(v___y_1412_, 7);
v_initHeartbeats_1423_ = lean_ctor_get(v___y_1412_, 8);
v_maxHeartbeats_1424_ = lean_ctor_get(v___y_1412_, 9);
v_quotContext_1425_ = lean_ctor_get(v___y_1412_, 10);
v_currMacroScope_1426_ = lean_ctor_get(v___y_1412_, 11);
v_diag_1427_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*14);
v_cancelTk_x3f_1428_ = lean_ctor_get(v___y_1412_, 12);
v_suppressElabErrors_1429_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1430_ = lean_ctor_get(v___y_1412_, 13);
v_ref_1431_ = l_Lean_replaceRef(v_ref_1410_, v_ref_1420_);
lean_inc_ref(v_inheritedTraceOptions_1430_);
lean_inc(v_cancelTk_x3f_1428_);
lean_inc(v_currMacroScope_1426_);
lean_inc(v_quotContext_1425_);
lean_inc(v_maxHeartbeats_1424_);
lean_inc(v_initHeartbeats_1423_);
lean_inc(v_openDecls_1422_);
lean_inc(v_currNamespace_1421_);
lean_inc(v_maxRecDepth_1419_);
lean_inc(v_currRecDepth_1418_);
lean_inc_ref(v_options_1417_);
lean_inc_ref(v_fileMap_1416_);
lean_inc_ref(v_fileName_1415_);
v___x_1432_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1432_, 0, v_fileName_1415_);
lean_ctor_set(v___x_1432_, 1, v_fileMap_1416_);
lean_ctor_set(v___x_1432_, 2, v_options_1417_);
lean_ctor_set(v___x_1432_, 3, v_currRecDepth_1418_);
lean_ctor_set(v___x_1432_, 4, v_maxRecDepth_1419_);
lean_ctor_set(v___x_1432_, 5, v_ref_1431_);
lean_ctor_set(v___x_1432_, 6, v_currNamespace_1421_);
lean_ctor_set(v___x_1432_, 7, v_openDecls_1422_);
lean_ctor_set(v___x_1432_, 8, v_initHeartbeats_1423_);
lean_ctor_set(v___x_1432_, 9, v_maxHeartbeats_1424_);
lean_ctor_set(v___x_1432_, 10, v_quotContext_1425_);
lean_ctor_set(v___x_1432_, 11, v_currMacroScope_1426_);
lean_ctor_set(v___x_1432_, 12, v_cancelTk_x3f_1428_);
lean_ctor_set(v___x_1432_, 13, v_inheritedTraceOptions_1430_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*14, v_diag_1427_);
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*14 + 1, v_suppressElabErrors_1429_);
v___x_1433_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_1411_, v___x_1432_, v___y_1413_);
lean_dec_ref_known(v___x_1432_, 14);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1434_, v_msg_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v_ref_1434_);
return v_res_1439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
return v___x_1442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_1461_, lean_object* v_declHint_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v_env_1466_; uint8_t v___x_1467_; 
v___x_1465_ = lean_st_ref_get(v___y_1463_);
v_env_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc_ref(v_env_1466_);
lean_dec(v___x_1465_);
v___x_1467_ = l_Lean_Name_isAnonymous(v_declHint_1462_);
if (v___x_1467_ == 0)
{
uint8_t v_isExporting_1468_; 
v_isExporting_1468_ = lean_ctor_get_uint8(v_env_1466_, sizeof(void*)*8);
if (v_isExporting_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec_ref(v_env_1466_);
lean_dec(v_declHint_1462_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_msg_1461_);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
lean_inc_ref(v_env_1466_);
v___x_1470_ = l_Lean_Environment_setExporting(v_env_1466_, v___x_1467_);
lean_inc(v_declHint_1462_);
lean_inc_ref(v___x_1470_);
v___x_1471_ = l_Lean_Environment_contains(v___x_1470_, v_declHint_1462_, v_isExporting_1468_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_env_1466_);
lean_dec(v_declHint_1462_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_msg_1461_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_c_1478_; lean_object* v___x_1479_; 
v___x_1473_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
v___x_1474_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
v___x_1475_ = l_Lean_Options_empty;
v___x_1476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1470_);
lean_ctor_set(v___x_1476_, 1, v___x_1473_);
lean_ctor_set(v___x_1476_, 2, v___x_1474_);
lean_ctor_set(v___x_1476_, 3, v___x_1475_);
lean_inc(v_declHint_1462_);
v___x_1477_ = l_Lean_MessageData_ofConstName(v_declHint_1462_, v___x_1467_);
v_c_1478_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1478_, 0, v___x_1476_);
lean_ctor_set(v_c_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1466_, v_declHint_1462_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_env_1466_);
lean_dec(v_declHint_1462_);
v___x_1480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_c_1478_);
v___x_1482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_MessageData_note(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_msg_1461_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
else
{
lean_object* v_val_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1522_; 
v_val_1487_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1489_ = v___x_1479_;
v_isShared_1490_ = v_isSharedCheck_1522_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_val_1487_);
lean_dec(v___x_1479_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1522_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_mod_1494_; uint8_t v___x_1495_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = l_Lean_Environment_header(v_env_1466_);
lean_dec_ref(v_env_1466_);
v___x_1493_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1492_);
v_mod_1494_ = lean_array_get(v___x_1491_, v___x_1493_, v_val_1487_);
lean_dec(v_val_1487_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_isPrivateName(v_declHint_1462_);
lean_dec(v_declHint_1462_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v_c_1478_);
v___x_1498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_MessageData_ofName(v_mod_1494_);
v___x_1501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = l_Lean_MessageData_note(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_msg_1461_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1505_);
v___x_1507_ = v___x_1489_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_c_1478_);
v___x_1511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_MessageData_ofName(v_mod_1494_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_MessageData_note(v___x_1516_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_msg_1461_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1518_);
v___x_1520_ = v___x_1489_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref(v_env_1466_);
lean_dec(v_declHint_1462_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_msg_1461_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1524_, v_declHint_1525_, v___y_1526_);
lean_dec(v___y_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_1529_, lean_object* v_declHint_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v___x_1534_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1529_, v_declHint_1530_, v___y_1532_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = l_Lean_unknownIdentifierMessageTag;
v___x_1540_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_1545_, lean_object* v_declHint_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1545_, v_declHint_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_1551_, lean_object* v_msg_1552_, lean_object* v_declHint_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v_a_1558_; lean_object* v___x_1559_; 
v___x_1557_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_1552_, v_declHint_1553_, v___y_1554_, v___y_1555_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1551_, v_a_1558_, v___y_1554_, v___y_1555_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1560_, lean_object* v_msg_1561_, lean_object* v_declHint_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1560_, v_msg_1561_, v_declHint_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v_ref_1560_);
return v_res_1566_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1573_, lean_object* v_constName_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1578_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1579_ = 0;
lean_inc(v_constName_1574_);
v___x_1580_ = l_Lean_MessageData_ofConstName(v_constName_1574_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1578_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1573_, v___x_1583_, v_constName_1574_, v___y_1575_, v___y_1576_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1585_, lean_object* v_constName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1585_, v_constName_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v_ref_1585_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(lean_object* v_constName_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_ref_1595_; lean_object* v___x_1596_; 
v_ref_1595_ = lean_ctor_get(v___y_1592_, 5);
v___x_1596_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_1595_, v_constName_1591_, v___y_1592_, v___y_1593_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(lean_object* v_constName_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(lean_object* v_constName_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v_env_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_st_ref_get(v___y_1604_);
v_env_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc_ref(v_env_1607_);
lean_dec(v___x_1606_);
v___x_1608_ = 0;
lean_inc(v_constName_1602_);
v___x_1609_ = l_Lean_Environment_find_x3f(v_env_1607_, v_constName_1602_, v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_1602_, v___y_1603_, v___y_1604_);
return v___x_1610_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_constName_1602_);
v_val_1611_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1609_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v___x_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 0);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_val_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2___boxed(lean_object* v_constName_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_constName_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1623_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14));
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18));
v___x_1653_ = l_Lean_stringToMessageData(v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24));
v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26));
v___x_1665_ = l_Lean_stringToMessageData(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28));
v___x_1668_ = l_Lean_stringToMessageData(v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__42));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__44));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__46));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__48));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(lean_object* v_declName_1699_, lean_object* v_suffix_1700_, uint8_t v_status_1701_, uint8_t v_attrKind_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_options_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1814_; lean_object* v___y_1815_; 
v_options_1730_ = lean_ctor_get(v___y_1703_, 2);
v___x_1731_ = l_Lean_allowUnsafeReducibility;
v___x_1732_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_options_1730_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1884_; 
lean_inc(v_declName_1699_);
v___x_1884_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_declName_1699_, v___y_1703_, v___y_1704_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; uint8_t v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = l_Lean_ConstantInfo_isDefinition(v_a_1885_);
lean_dec(v_a_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1887_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
v___x_1888_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1886_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__49);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v_suffix_1700_);
v___x_1893_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1892_, v___y_1703_, v___y_1704_);
return v___x_1893_;
}
else
{
v___y_1814_ = v___y_1703_;
v___y_1815_ = v___y_1704_;
goto v___jp_1813_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
v_a_1894_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1884_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1884_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
v___jp_1706_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
v___jp_1709_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
v___jp_1712_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
v___jp_1715_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
v___jp_1718_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
v___jp_1721_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
v___jp_1724_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
v___jp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1736_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
v___x_1737_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_suffix_1700_);
v___x_1742_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1741_, v___y_1734_, v___y_1735_);
return v___x_1742_;
}
v___jp_1743_:
{
switch(v_status_1701_)
{
case 0:
{
if (v___y_1744_ == 1)
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1718_;
}
else
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
v___x_1748_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1744_);
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1751_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_suffix_1700_);
v___x_1758_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1757_, v___y_1745_, v___y_1746_);
return v___x_1758_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1718_;
}
}
}
case 1:
{
if (v___y_1744_ == 1)
{
v___y_1734_ = v___y_1745_;
v___y_1735_ = v___y_1746_;
goto v___jp_1733_;
}
else
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1759_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
v___x_1760_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_suffix_1700_);
v___x_1765_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1764_, v___y_1745_, v___y_1746_);
return v___x_1765_;
}
else
{
v___y_1734_ = v___y_1745_;
v___y_1735_ = v___y_1746_;
goto v___jp_1733_;
}
}
}
case 2:
{
switch(v___y_1744_)
{
case 1:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1721_;
}
case 3:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1721_;
}
case 4:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1721_;
}
default: 
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1766_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9);
v___x_1767_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1744_);
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1770_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_suffix_1700_);
v___x_1777_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1776_, v___y_1745_, v___y_1746_);
return v___x_1777_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1721_;
}
}
}
}
case 3:
{
switch(v___y_1744_)
{
case 1:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1724_;
}
case 4:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1724_;
}
default: 
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1778_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13);
v___x_1779_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1744_);
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1782_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v_suffix_1700_);
v___x_1789_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1788_, v___y_1745_, v___y_1746_);
return v___x_1789_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1724_;
}
}
}
}
default: 
{
if (v___y_1744_ == 1)
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1727_;
}
else
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1790_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17);
v___x_1791_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_ReducibilityStatus_toAttrString(v___y_1744_);
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1794_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v_suffix_1700_);
v___x_1801_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1800_, v___y_1745_, v___y_1746_);
return v___x_1801_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1727_;
}
}
}
}
}
v___jp_1802_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
v___x_1807_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_suffix_1700_);
v___x_1812_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1811_, v___y_1805_, v___y_1803_);
return v___x_1812_;
}
v___jp_1813_:
{
lean_object* v___x_1816_; lean_object* v_env_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_st_ref_get(v___y_1815_);
v_env_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_ref(v_env_1817_);
lean_dec(v___x_1816_);
lean_inc(v_declName_1699_);
v___x_1818_ = l_Lean_getReducibilityStatusCore(v_env_1817_, v_declName_1699_);
switch(v_attrKind_1702_)
{
case 0:
{
lean_object* v___x_1819_; lean_object* v_env_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_st_ref_get(v___y_1815_);
v_env_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc_ref(v_env_1820_);
lean_dec(v___x_1819_);
v___x_1821_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1820_, v_declName_1699_);
lean_dec_ref(v_env_1820_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_dec_ref_known(v___x_1821_, 1);
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___x_1818_;
v___y_1805_ = v___y_1814_;
goto v___jp_1802_;
}
else
{
lean_dec(v___x_1821_);
if (v___x_1732_ == 0)
{
v___y_1744_ = v___x_1818_;
v___y_1745_ = v___y_1814_;
v___y_1746_ = v___y_1815_;
goto v___jp_1743_;
}
else
{
v___y_1803_ = v___y_1815_;
v___y_1804_ = v___x_1818_;
v___y_1805_ = v___y_1814_;
goto v___jp_1802_;
}
}
}
case 1:
{
switch(v_status_1701_)
{
case 0:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23);
v___x_1823_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_suffix_1700_);
v___x_1828_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1827_, v___y_1814_, v___y_1815_);
return v___x_1828_;
}
case 1:
{
if (v___x_1818_ == 2)
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1706_;
}
else
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1829_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27);
v___x_1830_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1818_);
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v_suffix_1700_);
v___x_1840_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1839_, v___y_1814_, v___y_1815_);
return v___x_1840_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1706_;
}
}
}
case 2:
{
switch(v___x_1818_)
{
case 1:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1709_;
}
case 3:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1709_;
}
case 4:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1709_;
}
default: 
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1841_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33);
v___x_1842_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1818_);
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1845_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_suffix_1700_);
v___x_1852_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1851_, v___y_1814_, v___y_1815_);
return v___x_1852_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1709_;
}
}
}
}
case 3:
{
switch(v___x_1818_)
{
case 1:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1712_;
}
case 4:
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1712_;
}
default: 
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37);
v___x_1854_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1818_);
v___x_1859_ = l_Lean_stringToMessageData(v___x_1858_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1857_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_suffix_1700_);
v___x_1864_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1863_, v___y_1814_, v___y_1815_);
return v___x_1864_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1712_;
}
}
}
}
default: 
{
if (v___x_1818_ == 1)
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1715_;
}
else
{
if (v___x_1732_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1865_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41);
v___x_1866_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_ReducibilityStatus_toAttrString(v___x_1818_);
v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__43);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_suffix_1700_);
v___x_1876_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1875_, v___y_1814_, v___y_1815_);
return v___x_1876_;
}
else
{
lean_dec_ref(v_suffix_1700_);
lean_dec(v_declName_1699_);
goto v___jp_1715_;
}
}
}
}
}
default: 
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1877_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__45);
v___x_1878_ = l_Lean_MessageData_ofConstName(v_declName_1699_, v___x_1732_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__47);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_suffix_1700_);
v___x_1883_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_1882_, v___y_1814_, v___y_1815_);
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(lean_object* v_declName_1904_, lean_object* v_suffix_1905_, lean_object* v_status_1906_, lean_object* v_attrKind_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_status_boxed_1911_; uint8_t v_attrKind_boxed_1912_; lean_object* v_res_1913_; 
v_status_boxed_1911_ = lean_unbox(v_status_1906_);
v_attrKind_boxed_1912_ = lean_unbox(v_attrKind_1907_);
v_res_1913_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(v_declName_1904_, v_suffix_1905_, v_status_boxed_1911_, v_attrKind_boxed_1912_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(lean_object* v___y_1914_, uint8_t v_isExporting_1915_, lean_object* v___x_1916_, lean_object* v_a_x3f_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v_env_1920_; lean_object* v_nextMacroScope_1921_; lean_object* v_ngen_1922_; lean_object* v_auxDeclNGen_1923_; lean_object* v_traceState_1924_; lean_object* v_messages_1925_; lean_object* v_infoState_1926_; lean_object* v_snapshotTasks_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1938_; 
v___x_1919_ = lean_st_ref_take(v___y_1914_);
v_env_1920_ = lean_ctor_get(v___x_1919_, 0);
v_nextMacroScope_1921_ = lean_ctor_get(v___x_1919_, 1);
v_ngen_1922_ = lean_ctor_get(v___x_1919_, 2);
v_auxDeclNGen_1923_ = lean_ctor_get(v___x_1919_, 3);
v_traceState_1924_ = lean_ctor_get(v___x_1919_, 4);
v_messages_1925_ = lean_ctor_get(v___x_1919_, 6);
v_infoState_1926_ = lean_ctor_get(v___x_1919_, 7);
v_snapshotTasks_1927_ = lean_ctor_get(v___x_1919_, 8);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v___x_1919_, 5);
lean_dec(v_unused_1939_);
v___x_1929_ = v___x_1919_;
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snapshotTasks_1927_);
lean_inc(v_infoState_1926_);
lean_inc(v_messages_1925_);
lean_inc(v_traceState_1924_);
lean_inc(v_auxDeclNGen_1923_);
lean_inc(v_ngen_1922_);
lean_inc(v_nextMacroScope_1921_);
lean_inc(v_env_1920_);
lean_dec(v___x_1919_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = l_Lean_Environment_setExporting(v_env_1920_, v_isExporting_1915_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 5, v___x_1916_);
lean_ctor_set(v___x_1929_, 0, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_nextMacroScope_1921_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_ngen_1922_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_auxDeclNGen_1923_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_traceState_1924_);
lean_ctor_set(v_reuseFailAlloc_1937_, 5, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1937_, 6, v_messages_1925_);
lean_ctor_set(v_reuseFailAlloc_1937_, 7, v_infoState_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 8, v_snapshotTasks_1927_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_st_ref_put(v___y_1914_, v___x_1933_);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_1940_, lean_object* v_isExporting_1941_, lean_object* v___x_1942_, lean_object* v_a_x3f_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v_isExporting_boxed_1945_; lean_object* v_res_1946_; 
v_isExporting_boxed_1945_ = lean_unbox(v_isExporting_1941_);
v_res_1946_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1940_, v_isExporting_boxed_1945_, v___x_1942_, v_a_x3f_1943_);
lean_dec(v_a_x3f_1943_);
lean_dec(v___y_1940_);
return v_res_1946_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(lean_object* v_x_1952_, uint8_t v_isExporting_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; uint8_t v_isExporting_1959_; lean_object* v___x_2010_; uint8_t v_isModule_2011_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_env_1958_);
lean_dec(v___x_1957_);
v_isExporting_1959_ = lean_ctor_get_uint8(v_env_1958_, sizeof(void*)*8);
v___x_2010_ = l_Lean_Environment_header(v_env_1958_);
lean_dec_ref(v_env_1958_);
v_isModule_2011_ = lean_ctor_get_uint8(v___x_2010_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2010_);
if (v_isModule_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
v___x_2012_ = lean_apply_3(v_x_1952_, v___y_1954_, v___y_1955_, lean_box(0));
return v___x_2012_;
}
else
{
if (v_isExporting_1959_ == 0)
{
if (v_isExporting_1953_ == 0)
{
lean_object* v___x_2013_; 
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
v___x_2013_ = lean_apply_3(v_x_1952_, v___y_1954_, v___y_1955_, lean_box(0));
return v___x_2013_;
}
else
{
goto v___jp_1960_;
}
}
else
{
if (v_isExporting_1953_ == 0)
{
goto v___jp_1960_;
}
else
{
lean_object* v___x_2014_; 
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
v___x_2014_ = lean_apply_3(v_x_1952_, v___y_1954_, v___y_1955_, lean_box(0));
return v___x_2014_;
}
}
}
v___jp_1960_:
{
lean_object* v___x_1961_; lean_object* v_env_1962_; lean_object* v_nextMacroScope_1963_; lean_object* v_ngen_1964_; lean_object* v_auxDeclNGen_1965_; lean_object* v_traceState_1966_; lean_object* v_messages_1967_; lean_object* v_infoState_1968_; lean_object* v_snapshotTasks_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2008_; 
v___x_1961_ = lean_st_ref_take(v___y_1955_);
v_env_1962_ = lean_ctor_get(v___x_1961_, 0);
v_nextMacroScope_1963_ = lean_ctor_get(v___x_1961_, 1);
v_ngen_1964_ = lean_ctor_get(v___x_1961_, 2);
v_auxDeclNGen_1965_ = lean_ctor_get(v___x_1961_, 3);
v_traceState_1966_ = lean_ctor_get(v___x_1961_, 4);
v_messages_1967_ = lean_ctor_get(v___x_1961_, 6);
v_infoState_1968_ = lean_ctor_get(v___x_1961_, 7);
v_snapshotTasks_1969_ = lean_ctor_get(v___x_1961_, 8);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1961_, 5);
lean_dec(v_unused_2009_);
v___x_1971_ = v___x_1961_;
v_isShared_1972_ = v_isSharedCheck_2008_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_snapshotTasks_1969_);
lean_inc(v_infoState_1968_);
lean_inc(v_messages_1967_);
lean_inc(v_traceState_1966_);
lean_inc(v_auxDeclNGen_1965_);
lean_inc(v_ngen_1964_);
lean_inc(v_nextMacroScope_1963_);
lean_inc(v_env_1962_);
lean_dec(v___x_1961_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2008_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1973_ = l_Lean_Environment_setExporting(v_env_1962_, v_isExporting_1953_);
v___x_1974_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 5, v___x_1974_);
lean_ctor_set(v___x_1971_, 0, v___x_1973_);
v___x_1976_ = v___x_1971_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_nextMacroScope_1963_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_ngen_1964_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_auxDeclNGen_1965_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_traceState_1966_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_2007_, 6, v_messages_1967_);
lean_ctor_set(v_reuseFailAlloc_2007_, 7, v_infoState_1968_);
lean_ctor_set(v_reuseFailAlloc_2007_, 8, v_snapshotTasks_1969_);
v___x_1976_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v_r_1978_; 
v___x_1977_ = lean_st_ref_put(v___y_1955_, v___x_1976_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
v_r_1978_ = lean_apply_3(v_x_1952_, v___y_1954_, v___y_1955_, lean_box(0));
if (lean_obj_tag(v_r_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1995_; 
v_a_1979_ = lean_ctor_get(v_r_1978_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_r_1978_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1981_ = v_r_1978_;
v_isShared_1982_ = v_isSharedCheck_1995_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v_r_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1995_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
lean_inc(v_a_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 1);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v___x_1985_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1955_, v_isExporting_1959_, v___x_1974_, v___x_1984_);
lean_dec_ref(v___x_1984_);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1985_, 0);
lean_dec(v_unused_1993_);
v___x_1987_ = v___x_1985_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v___x_1985_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v_a_1979_);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1979_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_a_1996_ = lean_ctor_get(v_r_1978_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v_r_1978_, 1);
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_1955_, v_isExporting_1959_, v___x_1974_, v___x_1997_);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1998_, 0);
lean_dec(v_unused_2006_);
v___x_2000_ = v___x_1998_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v___x_1998_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 1);
lean_ctor_set(v___x_2000_, 0, v_a_1996_);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1996_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___boxed(lean_object* v_x_2015_, lean_object* v_isExporting_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v_isExporting_boxed_2020_; lean_object* v_res_2021_; 
v_isExporting_boxed_2020_ = lean_unbox(v_isExporting_2016_);
v_res_2021_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_2015_, v_isExporting_boxed_2020_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(lean_object* v_x_2022_, uint8_t v_when_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
if (v_when_2023_ == 0)
{
lean_object* v___x_2027_; 
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
v___x_2027_ = lean_apply_3(v_x_2022_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2027_;
}
else
{
uint8_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = 0;
v___x_2029_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_2022_, v___x_2028_, v___y_2024_, v___y_2025_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(lean_object* v_x_2030_, lean_object* v_when_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_when_boxed_2035_; lean_object* v_res_2036_; 
v_when_boxed_2035_ = lean_unbox(v_when_2031_);
v_res_2036_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_2030_, v_when_boxed_2035_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2036_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1));
v___x_2041_ = l_Lean_MessageData_ofFormat(v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3(void){
_start:
{
lean_object* v___x_2042_; lean_object* v_suffix_2043_; 
v___x_2042_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2);
v_suffix_2043_ = l_Lean_MessageData_note(v___x_2042_);
return v_suffix_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate(lean_object* v_declName_2044_, uint8_t v_status_2045_, uint8_t v_attrKind_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_suffix_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___f_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; 
v_suffix_2050_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3, &l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3);
v___x_2051_ = lean_box(v_status_2045_);
v___x_2052_ = lean_box(v_attrKind_2046_);
v___f_2053_ = lean_alloc_closure((void*)(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2053_, 0, v_declName_2044_);
lean_closure_set(v___f_2053_, 1, v_suffix_2050_);
lean_closure_set(v___f_2053_, 2, v___x_2051_);
lean_closure_set(v___f_2053_, 3, v___x_2052_);
v___x_2054_ = 1;
v___x_2055_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v___f_2053_, v___x_2054_, v_a_2047_, v_a_2048_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(lean_object* v_declName_2056_, lean_object* v_status_2057_, lean_object* v_attrKind_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
uint8_t v_status_boxed_2062_; uint8_t v_attrKind_boxed_2063_; lean_object* v_res_2064_; 
v_status_boxed_2062_ = lean_unbox(v_status_2057_);
v_attrKind_boxed_2063_ = lean_unbox(v_attrKind_2058_);
v_res_2064_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_2056_, v_status_boxed_2062_, v_attrKind_boxed_2063_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(lean_object* v_00_u03b1_2065_, lean_object* v_msg_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_2066_, v___y_2067_, v___y_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_msg_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(v_00_u03b1_2071_, v_msg_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(lean_object* v_00_u03b1_2077_, lean_object* v_x_2078_, uint8_t v_isExporting_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_2078_, v_isExporting_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_x_2085_, lean_object* v_isExporting_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v_isExporting_boxed_2090_; lean_object* v_res_2091_; 
v_isExporting_boxed_2090_ = lean_unbox(v_isExporting_2086_);
v_res_2091_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(v_00_u03b1_2084_, v_x_2085_, v_isExporting_boxed_2090_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(lean_object* v_00_u03b1_2092_, lean_object* v_x_2093_, uint8_t v_when_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_2093_, v_when_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_x_2100_, lean_object* v_when_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v_when_boxed_2105_; lean_object* v_res_2106_; 
v_when_boxed_2105_ = lean_unbox(v_when_2101_);
v_res_2106_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(v_00_u03b1_2099_, v_x_2100_, v_when_boxed_2105_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(lean_object* v_00_u03b1_2107_, lean_object* v_constName_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_constName_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(v_00_u03b1_2113_, v_constName_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_2119_, lean_object* v_ref_2120_, lean_object* v_constName_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_2120_, v_constName_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_ref_2127_, lean_object* v_constName_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(v_00_u03b1_2126_, v_ref_2127_, v_constName_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v_ref_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_2133_, lean_object* v_ref_2134_, lean_object* v_msg_2135_, lean_object* v_declHint_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_2134_, v_msg_2135_, v_declHint_2136_, v___y_2137_, v___y_2138_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_ref_2142_, lean_object* v_msg_2143_, lean_object* v_declHint_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(v_00_u03b1_2141_, v_ref_2142_, v_msg_2143_, v_declHint_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v_ref_2142_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_2149_, lean_object* v_declHint_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_2149_, v_declHint_2150_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2155_, lean_object* v_declHint_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_2155_, v_declHint_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_2161_, lean_object* v_ref_2162_, lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_2162_, v_msg_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_ref_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_2168_, v_ref_2169_, v_msg_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v_ref_2169_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(uint8_t v_status_2175_, lean_object* v_declName_2176_, lean_object* v_stx_2177_, uint8_t v_attrKind_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2177_, v_a_2179_, v_a_2180_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v___x_2183_; 
lean_dec_ref_known(v___x_2182_, 1);
lean_inc(v_declName_2176_);
v___x_2183_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(v_declName_2176_, v_status_2175_, v_attrKind_2178_, v_a_2179_, v_a_2180_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2212_; 
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2213_);
v___x_2185_ = v___x_2183_;
v_isShared_2186_ = v_isSharedCheck_2212_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v___x_2183_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2212_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v_currNamespace_2188_; lean_object* v_env_2189_; lean_object* v_nextMacroScope_2190_; lean_object* v_ngen_2191_; lean_object* v_auxDeclNGen_2192_; lean_object* v_traceState_2193_; lean_object* v_messages_2194_; lean_object* v_infoState_2195_; lean_object* v_snapshotTasks_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2210_; 
v___x_2187_ = lean_st_ref_take(v_a_2180_);
v_currNamespace_2188_ = lean_ctor_get(v_a_2179_, 6);
v_env_2189_ = lean_ctor_get(v___x_2187_, 0);
v_nextMacroScope_2190_ = lean_ctor_get(v___x_2187_, 1);
v_ngen_2191_ = lean_ctor_get(v___x_2187_, 2);
v_auxDeclNGen_2192_ = lean_ctor_get(v___x_2187_, 3);
v_traceState_2193_ = lean_ctor_get(v___x_2187_, 4);
v_messages_2194_ = lean_ctor_get(v___x_2187_, 6);
v_infoState_2195_ = lean_ctor_get(v___x_2187_, 7);
v_snapshotTasks_2196_ = lean_ctor_get(v___x_2187_, 8);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2187_, 5);
lean_dec(v_unused_2211_);
v___x_2198_ = v___x_2187_;
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_snapshotTasks_2196_);
lean_inc(v_infoState_2195_);
lean_inc(v_messages_2194_);
lean_inc(v_traceState_2193_);
lean_inc(v_auxDeclNGen_2192_);
lean_inc(v_ngen_2191_);
lean_inc(v_nextMacroScope_2190_);
lean_inc(v_env_2189_);
lean_dec(v___x_2187_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_inc(v_currNamespace_2188_);
v___x_2200_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2189_, v_declName_2176_, v_status_2175_, v_attrKind_2178_, v_currNamespace_2188_);
v___x_2201_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 5, v___x_2201_);
lean_ctor_set(v___x_2198_, 0, v___x_2200_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_nextMacroScope_2190_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_ngen_2191_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_auxDeclNGen_2192_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_traceState_2193_);
lean_ctor_set(v_reuseFailAlloc_2209_, 5, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2209_, 6, v_messages_2194_);
lean_ctor_set(v_reuseFailAlloc_2209_, 7, v_infoState_2195_);
lean_ctor_set(v_reuseFailAlloc_2209_, 8, v_snapshotTasks_2196_);
v___x_2203_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_st_ref_put(v_a_2180_, v___x_2203_);
v___x_2205_ = lean_box(0);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2205_);
v___x_2207_ = v___x_2185_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_dec(v_declName_2176_);
return v___x_2183_;
}
}
else
{
lean_dec(v_declName_2176_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed(lean_object* v_status_2214_, lean_object* v_declName_2215_, lean_object* v_stx_2216_, lean_object* v_attrKind_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
uint8_t v_status_boxed_2221_; uint8_t v_attrKind_boxed_2222_; lean_object* v_res_2223_; 
v_status_boxed_2221_ = lean_unbox(v_status_2214_);
v_attrKind_boxed_2222_ = lean_unbox(v_attrKind_2217_);
v_res_2223_ = l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(v_status_boxed_2221_, v_declName_2215_, v_stx_2216_, v_attrKind_boxed_2222_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2223_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(lean_object* v___x_2230_, lean_object* v_decl_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2236_ = l_Lean_MessageData_ofName(v___x_2230_);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_2239_, v___y_2232_, v___y_2233_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v___x_2241_, lean_object* v_decl_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(v___x_2241_, v_decl_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v_decl_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2312_ = l_Lean_registerBuiltinAttribute(v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
return v_res_2314_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_unsigned_to_nat(4118757939u);
v___x_2316_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2317_ = l_Lean_Name_num___override(v___x_2316_, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2319_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2320_ = l_Lean_Name_str___override(v___x_2319_, v___x_2318_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2322_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2323_ = l_Lean_Name_str___override(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_unsigned_to_nat(2u);
v___x_2325_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2326_ = l_Lean_Name_num___override(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2333_ = 0;
v___x_2334_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2335_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2336_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2337_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2335_);
lean_ctor_set(v___x_2337_, 2, v___x_2334_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*3, v___x_2333_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___f_2341_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2342_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_));
v___x_2343_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v___x_2342_);
lean_ctor_set(v___x_2344_, 2, v___f_2341_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
v___x_2347_ = l_Lean_registerBuiltinAttribute(v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
return v_res_2349_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_unsigned_to_nat(2994861043u);
v___x_2351_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2352_ = l_Lean_Name_num___override(v___x_2351_, v___x_2350_);
return v___x_2352_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2354_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2355_ = l_Lean_Name_str___override(v___x_2354_, v___x_2353_);
return v___x_2355_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_));
v___x_2357_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2358_ = l_Lean_Name_str___override(v___x_2357_, v___x_2356_);
return v___x_2358_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_unsigned_to_nat(2u);
v___x_2360_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2361_ = l_Lean_Name_num___override(v___x_2360_, v___x_2359_);
return v___x_2361_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2368_ = 0;
v___x_2369_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2370_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2371_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2372_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v___x_2370_);
lean_ctor_set(v___x_2372_, 2, v___x_2369_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*3, v___x_2368_);
return v___x_2372_;
}
}
static lean_object* _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___f_2376_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2377_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_));
v___x_2378_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___x_2377_);
lean_ctor_set(v___x_2379_, 2, v___f_2376_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_obj_once(&l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_, &l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once, _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
v___x_2382_ = l_Lean_registerBuiltinAttribute(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_));
v___x_2417_ = l_Lean_registerBuiltinAttribute(v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2____boxed(lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_();
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_));
v___x_2452_ = l_Lean_registerBuiltinAttribute(v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2____boxed(lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_();
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg___lam__0(lean_object* v_declName_2455_, lean_object* v_toPure_2456_, lean_object* v_____do__lift_2457_){
_start:
{
uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = l_Lean_getReducibilityStatusCore(v_____do__lift_2457_, v_declName_2455_);
v___x_2459_ = lean_box(v___x_2458_);
v___x_2460_ = lean_apply_2(v_toPure_2456_, lean_box(0), v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___redArg(lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_declName_2463_){
_start:
{
lean_object* v_toApplicative_2464_; lean_object* v_toBind_2465_; lean_object* v_getEnv_2466_; lean_object* v_toPure_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; 
v_toApplicative_2464_ = lean_ctor_get(v_inst_2461_, 0);
lean_inc_ref(v_toApplicative_2464_);
v_toBind_2465_ = lean_ctor_get(v_inst_2461_, 1);
lean_inc(v_toBind_2465_);
lean_dec_ref(v_inst_2461_);
v_getEnv_2466_ = lean_ctor_get(v_inst_2462_, 0);
lean_inc(v_getEnv_2466_);
lean_dec_ref(v_inst_2462_);
v_toPure_2467_ = lean_ctor_get(v_toApplicative_2464_, 1);
lean_inc(v_toPure_2467_);
lean_dec_ref(v_toApplicative_2464_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_getReducibilityStatus___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2468_, 0, v_declName_2463_);
lean_closure_set(v___f_2468_, 1, v_toPure_2467_);
v___x_2469_ = lean_apply_4(v_toBind_2465_, lean_box(0), lean_box(0), v_getEnv_2466_, v___f_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus(lean_object* v_m_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_declName_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_getReducibilityStatus___redArg(v_inst_2471_, v_inst_2472_, v_declName_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0(lean_object* v_declName_2475_, uint8_t v_s_2476_, lean_object* v_env_2477_){
_start:
{
uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = 0;
v___x_2479_ = lean_box(0);
v___x_2480_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2477_, v_declName_2475_, v_s_2476_, v___x_2478_, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___lam__0___boxed(lean_object* v_declName_2481_, lean_object* v_s_2482_, lean_object* v_env_2483_){
_start:
{
uint8_t v_s_boxed_2484_; lean_object* v_res_2485_; 
v_s_boxed_2484_ = lean_unbox(v_s_2482_);
v_res_2485_ = l_Lean_setReducibilityStatus___redArg___lam__0(v_declName_2481_, v_s_boxed_2484_, v_env_2483_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg(lean_object* v_inst_2486_, lean_object* v_declName_2487_, uint8_t v_s_2488_){
_start:
{
lean_object* v_modifyEnv_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
v_modifyEnv_2489_ = lean_ctor_get(v_inst_2486_, 1);
lean_inc(v_modifyEnv_2489_);
lean_dec_ref(v_inst_2486_);
v___x_2490_ = lean_box(v_s_2488_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_setReducibilityStatus___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2491_, 0, v_declName_2487_);
lean_closure_set(v___f_2491_, 1, v___x_2490_);
v___x_2492_ = lean_apply_1(v_modifyEnv_2489_, v___f_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___redArg___boxed(lean_object* v_inst_2493_, lean_object* v_declName_2494_, lean_object* v_s_2495_){
_start:
{
uint8_t v_s_boxed_2496_; lean_object* v_res_2497_; 
v_s_boxed_2496_ = lean_unbox(v_s_2495_);
v_res_2497_ = l_Lean_setReducibilityStatus___redArg(v_inst_2493_, v_declName_2494_, v_s_boxed_2496_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus(lean_object* v_m_2498_, lean_object* v_inst_2499_, lean_object* v_declName_2500_, uint8_t v_s_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_setReducibilityStatus___redArg(v_inst_2499_, v_declName_2500_, v_s_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___boxed(lean_object* v_m_2503_, lean_object* v_inst_2504_, lean_object* v_declName_2505_, lean_object* v_s_2506_){
_start:
{
uint8_t v_s_boxed_2507_; lean_object* v_res_2508_; 
v_s_boxed_2507_ = lean_unbox(v_s_2506_);
v_res_2508_ = l_Lean_setReducibilityStatus(v_m_2503_, v_inst_2504_, v_declName_2505_, v_s_boxed_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___redArg(lean_object* v_inst_2509_, lean_object* v_declName_2510_){
_start:
{
uint8_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = 0;
v___x_2512_ = l_Lean_setReducibilityStatus___redArg(v_inst_2509_, v_declName_2510_, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute(lean_object* v_m_2513_, lean_object* v_inst_2514_, lean_object* v_declName_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_setReducibleAttribute___redArg(v_inst_2514_, v_declName_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0(lean_object* v_toPure_2517_, uint8_t v_____do__lift_2518_){
_start:
{
if (v_____do__lift_2518_ == 0)
{
uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = 1;
v___x_2520_ = lean_box(v___x_2519_);
v___x_2521_ = lean_apply_2(v_toPure_2517_, lean_box(0), v___x_2520_);
return v___x_2521_;
}
else
{
uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = 0;
v___x_2523_ = lean_box(v___x_2522_);
v___x_2524_ = lean_apply_2(v_toPure_2517_, lean_box(0), v___x_2523_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg___lam__0___boxed(lean_object* v_toPure_2525_, lean_object* v_____do__lift_2526_){
_start:
{
uint8_t v_____do__lift_47__boxed_2527_; lean_object* v_res_2528_; 
v_____do__lift_47__boxed_2527_ = lean_unbox(v_____do__lift_2526_);
v_res_2528_ = l_Lean_isReducible___redArg___lam__0(v_toPure_2525_, v_____do__lift_47__boxed_2527_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___redArg(lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_declName_2531_){
_start:
{
lean_object* v_toApplicative_2532_; lean_object* v_toBind_2533_; lean_object* v_toPure_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; 
v_toApplicative_2532_ = lean_ctor_get(v_inst_2529_, 0);
v_toBind_2533_ = lean_ctor_get(v_inst_2529_, 1);
lean_inc(v_toBind_2533_);
v_toPure_2534_ = lean_ctor_get(v_toApplicative_2532_, 1);
lean_inc(v_toPure_2534_);
v___x_2535_ = l_Lean_getReducibilityStatus___redArg(v_inst_2529_, v_inst_2530_, v_declName_2531_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_isReducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2536_, 0, v_toPure_2534_);
v___x_2537_ = lean_apply_4(v_toBind_2533_, lean_box(0), lean_box(0), v___x_2535_, v___f_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible(lean_object* v_m_2538_, lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_declName_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_isReducible___redArg(v_inst_2539_, v_inst_2540_, v_declName_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0(lean_object* v_toPure_2543_, uint8_t v_____do__lift_2544_){
_start:
{
if (v_____do__lift_2544_ == 2)
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = 1;
v___x_2546_ = lean_box(v___x_2545_);
v___x_2547_ = lean_apply_2(v_toPure_2543_, lean_box(0), v___x_2546_);
return v___x_2547_;
}
else
{
uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = 0;
v___x_2549_ = lean_box(v___x_2548_);
v___x_2550_ = lean_apply_2(v_toPure_2543_, lean_box(0), v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg___lam__0___boxed(lean_object* v_toPure_2551_, lean_object* v_____do__lift_2552_){
_start:
{
uint8_t v_____do__lift_47__boxed_2553_; lean_object* v_res_2554_; 
v_____do__lift_47__boxed_2553_ = lean_unbox(v_____do__lift_2552_);
v_res_2554_ = l_Lean_isIrreducible___redArg___lam__0(v_toPure_2551_, v_____do__lift_47__boxed_2553_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___redArg(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_declName_2557_){
_start:
{
lean_object* v_toApplicative_2558_; lean_object* v_toBind_2559_; lean_object* v_toPure_2560_; lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___x_2563_; 
v_toApplicative_2558_ = lean_ctor_get(v_inst_2555_, 0);
v_toBind_2559_ = lean_ctor_get(v_inst_2555_, 1);
lean_inc(v_toBind_2559_);
v_toPure_2560_ = lean_ctor_get(v_toApplicative_2558_, 1);
lean_inc(v_toPure_2560_);
v___x_2561_ = l_Lean_getReducibilityStatus___redArg(v_inst_2555_, v_inst_2556_, v_declName_2557_);
v___f_2562_ = lean_alloc_closure((void*)(l_Lean_isIrreducible___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2562_, 0, v_toPure_2560_);
v___x_2563_ = lean_apply_4(v_toBind_2559_, lean_box(0), lean_box(0), v___x_2561_, v___f_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible(lean_object* v_m_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_declName_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_isIrreducible___redArg(v_inst_2565_, v_inst_2566_, v_declName_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT uint8_t l_Lean_isImplicitReducibleCore(lean_object* v_env_2569_, lean_object* v_declName_2570_){
_start:
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Lean_getReducibilityStatusCore(v_env_2569_, v_declName_2570_);
if (v___x_2571_ == 3)
{
uint8_t v___x_2572_; 
v___x_2572_ = 1;
return v___x_2572_;
}
else
{
uint8_t v___x_2573_; 
v___x_2573_ = 0;
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducibleCore___boxed(lean_object* v_env_2574_, lean_object* v_declName_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l_Lean_isImplicitReducibleCore(v_env_2574_, v_declName_2575_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg___lam__0(lean_object* v_declName_2578_, lean_object* v_toPure_2579_, lean_object* v_____do__lift_2580_){
_start:
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = l_Lean_isImplicitReducibleCore(v_____do__lift_2580_, v_declName_2578_);
v___x_2582_ = lean_box(v___x_2581_);
v___x_2583_ = lean_apply_2(v_toPure_2579_, lean_box(0), v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___redArg(lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_declName_2586_){
_start:
{
lean_object* v_toApplicative_2587_; lean_object* v_toBind_2588_; lean_object* v_getEnv_2589_; lean_object* v_toPure_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; 
v_toApplicative_2587_ = lean_ctor_get(v_inst_2584_, 0);
lean_inc_ref(v_toApplicative_2587_);
v_toBind_2588_ = lean_ctor_get(v_inst_2584_, 1);
lean_inc(v_toBind_2588_);
lean_dec_ref(v_inst_2584_);
v_getEnv_2589_ = lean_ctor_get(v_inst_2585_, 0);
lean_inc(v_getEnv_2589_);
lean_dec_ref(v_inst_2585_);
v_toPure_2590_ = lean_ctor_get(v_toApplicative_2587_, 1);
lean_inc(v_toPure_2590_);
lean_dec_ref(v_toApplicative_2587_);
v___f_2591_ = lean_alloc_closure((void*)(l_Lean_isImplicitReducible___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2591_, 0, v_declName_2586_);
lean_closure_set(v___f_2591_, 1, v_toPure_2590_);
v___x_2592_ = lean_apply_4(v_toBind_2588_, lean_box(0), lean_box(0), v_getEnv_2589_, v___f_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible(lean_object* v_m_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_declName_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_isImplicitReducible___redArg(v_inst_2594_, v_inst_2595_, v_declName_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT uint8_t l_Lean_isInstanceReducibleCore(lean_object* v_env_2598_, lean_object* v_declName_2599_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_getReducibilityStatusCore(v_env_2598_, v_declName_2599_);
if (v___x_2600_ == 4)
{
uint8_t v___x_2601_; 
v___x_2601_ = 1;
return v___x_2601_;
}
else
{
uint8_t v___x_2602_; 
v___x_2602_ = 0;
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducibleCore___boxed(lean_object* v_env_2603_, lean_object* v_declName_2604_){
_start:
{
uint8_t v_res_2605_; lean_object* v_r_2606_; 
v_res_2605_ = l_Lean_isInstanceReducibleCore(v_env_2603_, v_declName_2604_);
v_r_2606_ = lean_box(v_res_2605_);
return v_r_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg___lam__0(lean_object* v_declName_2607_, lean_object* v_toPure_2608_, lean_object* v_____do__lift_2609_){
_start:
{
uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = l_Lean_isInstanceReducibleCore(v_____do__lift_2609_, v_declName_2607_);
v___x_2611_ = lean_box(v___x_2610_);
v___x_2612_ = lean_apply_2(v_toPure_2608_, lean_box(0), v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___redArg(lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_declName_2615_){
_start:
{
lean_object* v_toApplicative_2616_; lean_object* v_toBind_2617_; lean_object* v_getEnv_2618_; lean_object* v_toPure_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
v_toApplicative_2616_ = lean_ctor_get(v_inst_2613_, 0);
lean_inc_ref(v_toApplicative_2616_);
v_toBind_2617_ = lean_ctor_get(v_inst_2613_, 1);
lean_inc(v_toBind_2617_);
lean_dec_ref(v_inst_2613_);
v_getEnv_2618_ = lean_ctor_get(v_inst_2614_, 0);
lean_inc(v_getEnv_2618_);
lean_dec_ref(v_inst_2614_);
v_toPure_2619_ = lean_ctor_get(v_toApplicative_2616_, 1);
lean_inc(v_toPure_2619_);
lean_dec_ref(v_toApplicative_2616_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_isInstanceReducible___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2620_, 0, v_declName_2615_);
lean_closure_set(v___f_2620_, 1, v_toPure_2619_);
v___x_2621_ = lean_apply_4(v_toBind_2617_, lean_box(0), lean_box(0), v_getEnv_2618_, v___f_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible(lean_object* v_m_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_declName_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_isInstanceReducible___redArg(v_inst_2623_, v_inst_2624_, v_declName_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute___redArg(lean_object* v_inst_2627_, lean_object* v_declName_2628_){
_start:
{
uint8_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = 2;
v___x_2630_ = l_Lean_setReducibilityStatus___redArg(v_inst_2627_, v_declName_2628_, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_setIrreducibleAttribute(lean_object* v_m_2631_, lean_object* v_inst_2632_, lean_object* v_declName_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_setIrreducibleAttribute___redArg(v_inst_2632_, v_declName_2633_);
return v___x_2634_;
}
}
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ReducibilityAttrs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedReducibilityStatus_default = _init_l_Lean_instInhabitedReducibilityStatus_default();
l_Lean_instInhabitedReducibilityStatus = _init_l_Lean_instInhabitedReducibilityStatus();
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reducibilityCoreExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reducibilityCoreExt);
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reducibilityExtraExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reducibilityExtraExt);
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_allowUnsafeReducibility = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_allowUnsafeReducibility);
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_82891871____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2104212786____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ReducibilityAttrs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ReducibilityAttrs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReducibilityAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ReducibilityAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ReducibilityAttrs(builtin);
}
#ifdef __cplusplus
}
#endif
